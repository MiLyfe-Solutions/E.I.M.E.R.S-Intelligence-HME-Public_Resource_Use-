import V185TrunkScan23Chunk0617

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3654376 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3654376 : Nat := 118140960795 + 3654376 * 2 ^ 59
def prefixEnd_3654376 : Nat := 4983230072969 + 3 ^ 40 * 3654376 * 2
def baseEnd_3654376 : Nat := 1876451380254899470793837

theorem tailTrace_3654376 : CollatzResearch.WordTrace tailWord_3654376 prefixEnd_3654376 1876451380254899470793837 := by
  unfold tailWord_3654376
  simp only [CollatzResearch.WordTrace]
  refine ⟨66643021304413672288679491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88857361739218229718239321 66643021304413672288679491)
  ·
    refine ⟨99964531956620508433019237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66643021304413672288679491 99964531956620508433019237)
    ·
      refine ⟨18743349741866345331191107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99964531956620508433019237 18743349741866345331191107)
      ·
        refine ⟨28115024612799517996786661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18743349741866345331191107 28115024612799517996786661)
        ·
          refine ⟨5271567114899909624397499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28115024612799517996786661 5271567114899909624397499)
          ·
            refine ⟨7907350672349864436596249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271567114899909624397499 7907350672349864436596249)
            ·
              refine ⟨5930513004262398327447187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7907350672349864436596249 5930513004262398327447187)
              ·
                refine ⟨8895769506393597491170781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5930513004262398327447187 8895769506393597491170781)
                ·
                  refine ⟨3335913564897599059189043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8895769506393597491170781 3335913564897599059189043)
                  ·
                    refine ⟨5003870347346398588783565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3335913564897599059189043 5003870347346398588783565)
                    ·
                      refine ⟨1876451380254899470793837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5003870347346398588783565 1876451380254899470793837)
                      ·
                        rfl

theorem cell23_3654376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3654376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654376 prefixEnd_3654376 := by exact prefixLift 3654376
  have htrace : WordTrace (prefixWord ++ tailWord_3654376) baseStart_3654376 baseEnd_3654376 := by
    simpa [prefixWord, tailWord_3654376, baseEnd_3654376] using wordTrace_append hprefix tailTrace_3654376
  have hstable : (prefixWord ++ tailWord_3654376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654376).length < 2 ^ (prefixWord ++ tailWord_3654376).sum := by decide
  have hdescent : baseEnd_3654376 < baseStart_3654376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654435 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 2, 7]
def baseStart_3654435 : Nat := 118140960795 + 3654435 * 2 ^ 59
def prefixEnd_3654435 : Nat := 4983230072969 + 3 ^ 40 * 3654435 * 2
def baseEnd_3654435 : Nat := 625493891871171579985355

theorem tailTrace_3654435 : CollatzResearch.WordTrace tailWord_3654435 prefixEnd_3654435 625493891871171579985355 := by
  unfold tailWord_3654435
  simp only [CollatzResearch.WordTrace]
  refine ⟨133288194515613597653756759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88858796343742398435837839 133288194515613597653756759)
  ·
    refine ⟨199932291773420396480635139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133288194515613597653756759 199932291773420396480635139)
    ·
      refine ⟨299898437660130594720952709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199932291773420396480635139 299898437660130594720952709)
      ·
        refine ⟨56230957061274486510178633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299898437660130594720952709 56230957061274486510178633)
        ·
          refine ⟨42173217795955864882633975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56230957061274486510178633 42173217795955864882633975)
          ·
            refine ⟨63259826693933797323950963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42173217795955864882633975 63259826693933797323950963)
            ·
              refine ⟨94889740040900695985926445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63259826693933797323950963 94889740040900695985926445)
              ·
                refine ⟨35583652515337760994722417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94889740040900695985926445 35583652515337760994722417)
                ·
                  refine ⟨26687739386503320746041813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35583652515337760994722417 26687739386503320746041813)
                  ·
                    refine ⟨625493891871171579985355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26687739386503320746041813 625493891871171579985355)
                    ·
                      rfl

theorem cell23_3654435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 2, 7].length) (baseStart_3654435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654435 prefixEnd_3654435 := by exact prefixLift 3654435
  have htrace : WordTrace (prefixWord ++ tailWord_3654435) baseStart_3654435 baseEnd_3654435 := by
    simpa [prefixWord, tailWord_3654435, baseEnd_3654435] using wordTrace_append hprefix tailTrace_3654435
  have hstable : (prefixWord ++ tailWord_3654435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654435).length < 2 ^ (prefixWord ++ tailWord_3654435).sum := by decide
  have hdescent : baseEnd_3654435 < baseStart_3654435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654470 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_3654470 : Nat := 118140960795 + 3654470 * 2 ^ 59
def prefixEnd_3654470 : Nat := 4983230072969 + 3 ^ 40 * 3654470 * 2
def baseEnd_3654470 : Nat := 1876499647436422103018405

theorem tailTrace_3654470 : CollatzResearch.WordTrace tailWord_3654470 prefixEnd_3654470 1876499647436422103018405 := by
  unfold tailWord_3654470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4165295970952712457227527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88859647380324532420853909 4165295970952712457227527)
  ·
    refine ⟨6247943956429068685841291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4165295970952712457227527 6247943956429068685841291)
    ·
      refine ⟨9371915934643603028761937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6247943956429068685841291 9371915934643603028761937)
      ·
        refine ⟨7028936950982702271571453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9371915934643603028761937 7028936950982702271571453)
        ·
          refine ⟨2635851356618513351839295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7028936950982702271571453 2635851356618513351839295)
          ·
            refine ⟨3953777034927770027758943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635851356618513351839295 3953777034927770027758943)
            ·
              refine ⟨5930665552391655041638415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3953777034927770027758943 5930665552391655041638415)
              ·
                refine ⟨8895998328587482562457623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5930665552391655041638415 8895998328587482562457623)
                ·
                  refine ⟨13343997492881223843686435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8895998328587482562457623 13343997492881223843686435)
                  ·
                    refine ⟨20015996239321835765529653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13343997492881223843686435 20015996239321835765529653)
                    ·
                      refine ⟨1876499647436422103018405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20015996239321835765529653 1876499647436422103018405)
                      ·
                        rfl

theorem cell23_3654470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_3654470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654470 prefixEnd_3654470 := by exact prefixLift 3654470
  have htrace : WordTrace (prefixWord ++ tailWord_3654470) baseStart_3654470 baseEnd_3654470 := by
    simpa [prefixWord, tailWord_3654470, baseEnd_3654470] using wordTrace_append hprefix tailTrace_3654470
  have hstable : (prefixWord ++ tailWord_3654470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654470).length < 2 ^ (prefixWord ++ tailWord_3654470).sum := by decide
  have hdescent : baseEnd_3654470 < baseStart_3654470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654482 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 2, 6]
def baseStart_3654482 : Nat := 118140960795 + 3654482 * 2 ^ 59
def prefixEnd_3654482 : Nat := 4983230072969 + 3 ^ 40 * 3654482 * 2
def baseEnd_3654482 : Nat := 625501936401425352022783

theorem tailTrace_3654482 : CollatzResearch.WordTrace tailWord_3654482 prefixEnd_3654482 625501936401425352022783 := by
  unfold tailWord_3654482
  simp only [CollatzResearch.WordTrace]
  refine ⟨33322477186610831170179425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88859939164295549787145133 33322477186610831170179425)
  ·
    refine ⟨24991857889958123377634569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33322477186610831170179425 24991857889958123377634569)
    ·
      refine ⟨18743893417468592533225927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24991857889958123377634569 18743893417468592533225927)
      ·
        refine ⟨28115840126202888799838891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18743893417468592533225927 28115840126202888799838891)
        ·
          refine ⟨42173760189304333199758337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28115840126202888799838891 42173760189304333199758337)
          ·
            refine ⟨31630320141978249899818753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42173760189304333199758337 31630320141978249899818753)
            ·
              refine ⟨23722740106483687424864065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31630320141978249899818753 23722740106483687424864065)
              ·
                refine ⟨17792055079862765568648049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23722740106483687424864065 17792055079862765568648049)
                ·
                  refine ⟨13344041309897074176486037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17792055079862765568648049 13344041309897074176486037)
                  ·
                    refine ⟨625501936401425352022783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13344041309897074176486037 625501936401425352022783)
                    ·
                      rfl

theorem cell23_3654482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_3654482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654482 prefixEnd_3654482 := by exact prefixLift 3654482
  have htrace : WordTrace (prefixWord ++ tailWord_3654482) baseStart_3654482 baseEnd_3654482 := by
    simpa [prefixWord, tailWord_3654482, baseEnd_3654482] using wordTrace_append hprefix tailTrace_3654482
  have hstable : (prefixWord ++ tailWord_3654482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654482).length < 2 ^ (prefixWord ++ tailWord_3654482).sum := by decide
  have hdescent : baseEnd_3654482 < baseStart_3654482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654484 : List Nat := [2, 4, 1, 1, 5, 1, 2, 2, 1, 2, 2]
def baseStart_3654484 : Nat := 118140960795 + 3654484 * 2 ^ 59
def prefixEnd_3654484 : Nat := 4983230072969 + 3 ^ 40 * 3654484 * 2
def baseEnd_3654484 : Nat := 1876506836165585048243341

theorem tailTrace_3654484 : CollatzResearch.WordTrace tailWord_3654484 prefixEnd_3654484 1876506836165585048243341 := by
  unfold tailWord_3654484
  simp only [CollatzResearch.WordTrace]
  refine ⟨66644990846218039511145253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88859987794957386014860337 66644990846218039511145253)
  ·
    refine ⟨12495935783665882408339735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66644990846218039511145253 12495935783665882408339735)
    ·
      refine ⟨18743903675498823612509603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12495935783665882408339735 18743903675498823612509603)
      ·
        refine ⟨28115855513248235418764405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18743903675498823612509603 28115855513248235418764405)
        ·
          refine ⟨2635861454367022070509163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28115855513248235418764405 2635861454367022070509163)
          ·
            refine ⟨3953792181550533105763745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2635861454367022070509163 3953792181550533105763745)
            ·
              refine ⟨2965344136162899829322809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3953792181550533105763745 2965344136162899829322809)
              ·
                refine ⟨2224008102122174871992107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2965344136162899829322809 2224008102122174871992107)
                ·
                  refine ⟨3336012153183262307988161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224008102122174871992107 3336012153183262307988161)
                  ·
                    refine ⟨2502009114887446730991121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3336012153183262307988161 2502009114887446730991121)
                    ·
                      refine ⟨1876506836165585048243341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502009114887446730991121 1876506836165585048243341)
                      ·
                        rfl

theorem cell23_3654484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_3654484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654484 prefixEnd_3654484 := by exact prefixLift 3654484
  have htrace : WordTrace (prefixWord ++ tailWord_3654484) baseStart_3654484 baseEnd_3654484 := by
    simpa [prefixWord, tailWord_3654484, baseEnd_3654484] using wordTrace_append hprefix tailTrace_3654484
  have hstable : (prefixWord ++ tailWord_3654484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654484).length < 2 ^ (prefixWord ++ tailWord_3654484).sum := by decide
  have hdescent : baseEnd_3654484 < baseStart_3654484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654522 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3]
def baseStart_3654522 : Nat := 118140960795 + 3654522 * 2 ^ 59
def prefixEnd_3654522 : Nat := 4983230072969 + 3 ^ 40 * 3654522 * 2
def baseEnd_3654522 : Nat := 1876526348430455899568165

theorem tailTrace_3654522 : CollatzResearch.WordTrace tailWord_3654522 prefixEnd_3654522 1876526348430455899568165 := by
  unfold tailWord_3654522
  simp only [CollatzResearch.WordTrace]
  refine ⟨33322841916574602878043455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88860911777532274341449213 33322841916574602878043455)
  ·
    refine ⟨49984262874861904317065183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33322841916574602878043455 49984262874861904317065183)
    ·
      refine ⟨74976394312292856475597775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49984262874861904317065183 74976394312292856475597775)
      ·
        refine ⟨112464591468439284713396663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74976394312292856475597775 112464591468439284713396663)
        ·
          refine ⟨168696887202658927070094995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112464591468439284713396663 168696887202658927070094995)
          ·
            refine ⟨253045330803988390605142493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168696887202658927070094995 253045330803988390605142493)
            ·
              refine ⟨94891999051495646476928435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253045330803988390605142493 94891999051495646476928435)
              ·
                refine ⟨142337998577243469715392653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94891999051495646476928435 142337998577243469715392653)
                ·
                  refine ⟨53376749466466301143272245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142337998577243469715392653 53376749466466301143272245)
                  ·
                    refine ⟨5004070262481215732181773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53376749466466301143272245 5004070262481215732181773)
                    ·
                      refine ⟨1876526348430455899568165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5004070262481215732181773 1876526348430455899568165)
                      ·
                        rfl

theorem cell23_3654522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_3654522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654522 prefixEnd_3654522 := by exact prefixLift 3654522
  have htrace : WordTrace (prefixWord ++ tailWord_3654522) baseStart_3654522 baseEnd_3654522 := by
    simpa [prefixWord, tailWord_3654522, baseEnd_3654522] using wordTrace_append hprefix tailTrace_3654522
  have hstable : (prefixWord ++ tailWord_3654522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654522).length < 2 ^ (prefixWord ++ tailWord_3654522).sum := by decide
  have hdescent : baseEnd_3654522 < baseStart_3654522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654546 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 7]
def baseStart_3654546 : Nat := 118140960795 + 3654546 * 2 ^ 59
def prefixEnd_3654546 : Nat := 4983230072969 + 3 ^ 40 * 3654546 * 2
def baseEnd_3654546 : Nat := 208504296885129311740895

theorem tailTrace_3654546 : CollatzResearch.WordTrace tailWord_3654546 prefixEnd_3654546 208504296885129311740895 := by
  unfold tailWord_3654546
  simp only [CollatzResearch.WordTrace]
  refine ⟨33323060754552865902761873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88861495345474309074031661 33323060754552865902761873)
  ·
    refine ⟨24992295565914649427071405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33323060754552865902761873 24992295565914649427071405)
    ·
      refine ⟨9372110837217993535151777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24992295565914649427071405 9372110837217993535151777)
      ·
        refine ⟨7029083127913495151363833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9372110837217993535151777 7029083127913495151363833)
        ·
          refine ⟨5271812345935121363522875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7029083127913495151363833 5271812345935121363522875)
          ·
            refine ⟨7907718518902682045284313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271812345935121363522875 7907718518902682045284313)
            ·
              refine ⟨5930788889177011533963235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7907718518902682045284313 5930788889177011533963235)
              ·
                refine ⟨8896183333765517300944853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5930788889177011533963235 8896183333765517300944853)
                ·
                  refine ⟨208504296885129311740895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8896183333765517300944853 208504296885129311740895)
                  ·
                    rfl

theorem cell23_3654546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_3654546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654546 prefixEnd_3654546 := by exact prefixLift 3654546
  have htrace : WordTrace (prefixWord ++ tailWord_3654546) baseStart_3654546 baseEnd_3654546 := by
    simpa [prefixWord, tailWord_3654546, baseEnd_3654546] using wordTrace_append hprefix tailTrace_3654546
  have hstable : (prefixWord ++ tailWord_3654546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654546).length < 2 ^ (prefixWord ++ tailWord_3654546).sum := by decide
  have hdescent : baseEnd_3654546 < baseStart_3654546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654579 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 4, 4, 2]
def baseStart_3654579 : Nat := 118140960795 + 3654579 * 2 ^ 59
def prefixEnd_3654579 : Nat := 4983230072969 + 3 ^ 40 * 3654579 * 2
def baseEnd_3654579 : Nat := 1876555616827762176555403

theorem tailTrace_3654579 : CollatzResearch.WordTrace tailWord_3654579 prefixEnd_3654579 1876555616827762176555403 := by
  unfold tailWord_3654579
  simp only [CollatzResearch.WordTrace]
  refine ⟨133293446627091910246998791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88862297751394606831332527 133293446627091910246998791)
  ·
    refine ⟨199940169940637865370498187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133293446627091910246998791 199940169940637865370498187)
    ·
      refine ⟨299910254910956798055747281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199940169940637865370498187 299910254910956798055747281)
      ·
        refine ⟨224932691183217598541810461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299910254910956798055747281 224932691183217598541810461)
        ·
          refine ⟨84349759193706599453178923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224932691183217598541810461 84349759193706599453178923)
          ·
            refine ⟨126524638790559899179768385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84349759193706599453178923 126524638790559899179768385)
            ·
              refine ⟨94893479092919924384826289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126524638790559899179768385 94893479092919924384826289)
              ·
                refine ⟨71170109319689943288619717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94893479092919924384826289 71170109319689943288619717)
                ·
                  refine ⟨13344395497441864366616197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71170109319689943288619717 13344395497441864366616197)
                  ·
                    refine ⟨2502074155770349568740537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13344395497441864366616197 2502074155770349568740537)
                    ·
                      refine ⟨1876555616827762176555403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502074155770349568740537 1876555616827762176555403)
                      ·
                        rfl

theorem cell23_3654579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 4, 2].length) (baseStart_3654579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654579 prefixEnd_3654579 := by exact prefixLift 3654579
  have htrace : WordTrace (prefixWord ++ tailWord_3654579) baseStart_3654579 baseEnd_3654579 := by
    simpa [prefixWord, tailWord_3654579, baseEnd_3654579] using wordTrace_append hprefix tailTrace_3654579
  have hstable : (prefixWord ++ tailWord_3654579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654579).length < 2 ^ (prefixWord ++ tailWord_3654579).sum := by decide
  have hdescent : baseEnd_3654579 < baseStart_3654579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654580 : List Nat := [2, 5, 2, 1, 1, 3, 1, 3, 5]
def baseStart_3654580 : Nat := 118140960795 + 3654580 * 2 ^ 59
def prefixEnd_3654580 : Nat := 4983230072969 + 3 ^ 40 * 3654580 * 2
def baseEnd_3654580 : Nat := 208506236700935185849211

theorem tailTrace_3654580 : CollatzResearch.WordTrace tailWord_3654580 prefixEnd_3654580 208506236700935185849211 := by
  unfold tailWord_3654580
  simp only [CollatzResearch.WordTrace]
  refine ⟨66646741550044143708892597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88862322066725524945190129 66646741550044143708892597)
  ·
    refine ⟨6248132020316638472708681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66646741550044143708892597 6248132020316638472708681)
    ·
      refine ⟨4686099015237478854531511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6248132020316638472708681 4686099015237478854531511)
      ·
        refine ⟨7029148522856218281797267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4686099015237478854531511 7029148522856218281797267)
        ·
          refine ⟨10543722784284327422695901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029148522856218281797267 10543722784284327422695901)
          ·
            refine ⟨3953896044106622783510963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10543722784284327422695901 3953896044106622783510963)
            ·
              refine ⟨5930844066159934175266445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3953896044106622783510963 5930844066159934175266445)
              ·
                refine ⟨2224066524809975315724917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5930844066159934175266445 2224066524809975315724917)
                ·
                  refine ⟨208506236700935185849211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2224066524809975315724917 208506236700935185849211)
                  ·
                    rfl

theorem cell23_3654580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_3654580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654580 prefixEnd_3654580 := by exact prefixLift 3654580
  have htrace : WordTrace (prefixWord ++ tailWord_3654580) baseStart_3654580 baseEnd_3654580 := by
    simpa [prefixWord, tailWord_3654580, baseEnd_3654580] using wordTrace_append hprefix tailTrace_3654580
  have hstable : (prefixWord ++ tailWord_3654580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654580).length < 2 ^ (prefixWord ++ tailWord_3654580).sum := by decide
  have hdescent : baseEnd_3654580 < baseStart_3654580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654599 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_3654599 : Nat := 118140960795 + 3654599 * 2 ^ 59
def prefixEnd_3654599 : Nat := 4983230072969 + 3 ^ 40 * 3654599 * 2
def baseEnd_3654599 : Nat := 1876565886440852098305311

theorem tailTrace_3654599 : CollatzResearch.WordTrace tailWord_3654599 prefixEnd_3654599 1876565886440852098305311 := by
  unfold tailWord_3654599
  simp only [CollatzResearch.WordTrace]
  refine ⟨133294176087019453662726851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88862784058012969108484567 133294176087019453662726851)
  ·
    refine ⟨199941264130529180494090277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133294176087019453662726851 199941264130529180494090277)
    ·
      refine ⟨37488987024474221342641927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199941264130529180494090277 37488987024474221342641927)
      ·
        refine ⟨56233480536711332013962891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37488987024474221342641927 56233480536711332013962891)
        ·
          refine ⟨84350220805066998020944337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56233480536711332013962891 84350220805066998020944337)
          ·
            refine ⟨63262665603800248515708253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84350220805066998020944337 63262665603800248515708253)
            ·
              refine ⟨23723499601425093193390595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63262665603800248515708253 23723499601425093193390595)
              ·
                refine ⟨35585249402137639790085893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23723499601425093193390595 35585249402137639790085893)
                ·
                  refine ⟨6672234262900807460641105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35585249402137639790085893 6672234262900807460641105)
                  ·
                    refine ⟨5004175697175605595480829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6672234262900807460641105 5004175697175605595480829)
                    ·
                      refine ⟨1876565886440852098305311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5004175697175605595480829 1876565886440852098305311)
                      ·
                        rfl

theorem cell23_3654599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_3654599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654599 prefixEnd_3654599 := by exact prefixLift 3654599
  have htrace : WordTrace (prefixWord ++ tailWord_3654599) baseStart_3654599 baseEnd_3654599 := by
    simpa [prefixWord, tailWord_3654599, baseEnd_3654599] using wordTrace_append hprefix tailTrace_3654599
  have hstable : (prefixWord ++ tailWord_3654599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654599).length < 2 ^ (prefixWord ++ tailWord_3654599).sum := by decide
  have hdescent : baseEnd_3654599 < baseStart_3654599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654606 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_3654606 : Nat := 118140960795 + 3654606 * 2 ^ 59
def prefixEnd_3654606 : Nat := 4983230072969 + 3 ^ 40 * 3654606 * 2
def baseEnd_3654606 : Nat := 625523160268477856972593

theorem tailTrace_3654606 : CollatzResearch.WordTrace tailWord_3654606 prefixEnd_3654606 625523160268477856972593 := by
  unfold tailWord_3654606
  simp only [CollatzResearch.WordTrace]
  refine ⟨16661803924749261732278959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88862954265329395905487781 16661803924749261732278959)
  ·
    refine ⟨24992705887123892598418439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16661803924749261732278959 24992705887123892598418439)
    ·
      refine ⟨37489058830685838897627659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24992705887123892598418439 37489058830685838897627659)
      ·
        refine ⟨56233588246028758346441489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37489058830685838897627659 56233588246028758346441489)
        ·
          refine ⟨42175191184521568759831117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56233588246028758346441489 42175191184521568759831117)
          ·
            refine ⟨15815696694195588284936669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42175191184521568759831117 15815696694195588284936669)
            ·
              refine ⟨5930886260323345606851251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15815696694195588284936669 5930886260323345606851251)
              ·
                refine ⟨8896329390485018410276877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5930886260323345606851251 8896329390485018410276877)
                ·
                  refine ⟨3336123521431881903853829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8896329390485018410276877 3336123521431881903853829)
                  ·
                    refine ⟨625523160268477856972593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3336123521431881903853829 625523160268477856972593)
                    ·
                      rfl

theorem cell23_3654606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_3654606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654606 prefixEnd_3654606 := by exact prefixLift 3654606
  have htrace : WordTrace (prefixWord ++ tailWord_3654606) baseStart_3654606 baseEnd_3654606 := by
    simpa [prefixWord, tailWord_3654606, baseEnd_3654606] using wordTrace_append hprefix tailTrace_3654606
  have hstable : (prefixWord ++ tailWord_3654606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654606).length < 2 ^ (prefixWord ++ tailWord_3654606).sum := by decide
  have hdescent : baseEnd_3654606 < baseStart_3654606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654690 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_3654690 : Nat := 118140960795 + 3654690 * 2 ^ 59
def prefixEnd_3654690 : Nat := 4983230072969 + 3 ^ 40 * 3654690 * 2
def baseEnd_3654690 : Nat := 1876612613180411242267393

theorem tailTrace_3654690 : CollatzResearch.WordTrace tailWord_3654690 prefixEnd_3654690 1876612613180411242267393 := by
  unfold tailWord_3654690
  simp only [CollatzResearch.WordTrace]
  refine ⟨33324373782422444051072381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88864996753126517469526349 33324373782422444051072381)
  ·
    refine ⟨12496640168408416519152143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33324373782422444051072381 12496640168408416519152143)
    ·
      refine ⟨18744960252612624778728215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12496640168408416519152143 18744960252612624778728215)
      ·
        refine ⟨28117440378918937168092323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18744960252612624778728215 28117440378918937168092323)
        ·
          refine ⟨42176160568378405752138485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28117440378918937168092323 42176160568378405752138485)
          ·
            refine ⟨3954015053285475539262983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42176160568378405752138485 3954015053285475539262983)
            ·
              refine ⟨5931022579928213308894475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954015053285475539262983 5931022579928213308894475)
              ·
                refine ⟨8896533869892319963341713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5931022579928213308894475 8896533869892319963341713)
                ·
                  refine ⟨6672400402419239972506285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8896533869892319963341713 6672400402419239972506285)
                  ·
                    refine ⟨2502150150907214989689857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6672400402419239972506285 2502150150907214989689857)
                    ·
                      refine ⟨1876612613180411242267393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502150150907214989689857 1876612613180411242267393)
                      ·
                        rfl

theorem cell23_3654690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_3654690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654690 prefixEnd_3654690 := by exact prefixLift 3654690
  have htrace : WordTrace (prefixWord ++ tailWord_3654690) baseStart_3654690 baseEnd_3654690 := by
    simpa [prefixWord, tailWord_3654690, baseEnd_3654690] using wordTrace_append hprefix tailTrace_3654690
  have hstable : (prefixWord ++ tailWord_3654690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654690).length < 2 ^ (prefixWord ++ tailWord_3654690).sum := by decide
  have hdescent : baseEnd_3654690 < baseStart_3654690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654699 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 4]
def baseStart_3654699 : Nat := 118140960795 + 3654699 * 2 ^ 59
def prefixEnd_3654699 : Nat := 4983230072969 + 3 ^ 40 * 3654699 * 2
def baseEnd_3654699 : Nat := 1876617234506301707054851

theorem tailTrace_3654699 : CollatzResearch.WordTrace tailWord_3654699 prefixEnd_3654699 1876617234506301707054851 := by
  unfold tailWord_3654699
  simp only [CollatzResearch.WordTrace]
  refine ⟨133297823386657170741367151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88865215591104780494244767 133297823386657170741367151)
  ·
    refine ⟨199946735079985756112050727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133297823386657170741367151 199946735079985756112050727)
    ·
      refine ⟨299920102619978634168076091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199946735079985756112050727 299920102619978634168076091)
      ·
        refine ⟨449880153929967951252114137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299920102619978634168076091 449880153929967951252114137)
        ·
          refine ⟨337410115447475963439085603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449880153929967951252114137 337410115447475963439085603)
          ·
            refine ⟨506115173171213945158628405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337410115447475963439085603 506115173171213945158628405)
            ·
              refine ⟨47448297484801307358621413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 506115173171213945158628405 47448297484801307358621413)
              ·
                refine ⟨8896555778400245129741515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47448297484801307358621413 8896555778400245129741515)
                ·
                  refine ⟨13344833667600367694612273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8896555778400245129741515 13344833667600367694612273)
                  ·
                    refine ⟨10008625250700275770959205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13344833667600367694612273 10008625250700275770959205)
                    ·
                      refine ⟨1876617234506301707054851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10008625250700275770959205 1876617234506301707054851)
                      ·
                        rfl

theorem cell23_3654699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 4].length) (baseStart_3654699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654699 prefixEnd_3654699 := by exact prefixLift 3654699
  have htrace : WordTrace (prefixWord ++ tailWord_3654699) baseStart_3654699 baseEnd_3654699 := by
    simpa [prefixWord, tailWord_3654699, baseEnd_3654699] using wordTrace_append hprefix tailTrace_3654699
  have hstable : (prefixWord ++ tailWord_3654699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654699).length < 2 ^ (prefixWord ++ tailWord_3654699).sum := by decide
  have hdescent : baseEnd_3654699 < baseStart_3654699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654713 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 2, 4]
def baseStart_3654713 : Nat := 118140960795 + 3654713 * 2 ^ 59
def prefixEnd_3654713 : Nat := 4983230072969 + 3 ^ 40 * 3654713 * 2
def baseEnd_3654713 : Nat := 625541474411821550759929

theorem tailTrace_3654713 : CollatzResearch.WordTrace tailWord_3654713 prefixEnd_3654713 625541474411821550759929 := by
  unfold tailWord_3654713
  simp only [CollatzResearch.WordTrace]
  refine ⟨133298334008606451132376793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88865556005737634088251195 133298334008606451132376793)
  ·
    refine ⟨99973750506454838349282595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133298334008606451132376793 99973750506454838349282595)
    ·
      refine ⟨149960625759682257523923893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99973750506454838349282595 149960625759682257523923893)
      ·
        refine ⟨14058808664970211642867865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149960625759682257523923893 14058808664970211642867865)
        ·
          refine ⟨10544106498727658732150899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14058808664970211642867865 10544106498727658732150899)
          ·
            refine ⟨15816159748091488098226349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10544106498727658732150899 15816159748091488098226349)
            ·
              refine ⟨5931059905534308036834881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15816159748091488098226349 5931059905534308036834881)
              ·
                refine ⟨4448294929150731027626161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5931059905534308036834881 4448294929150731027626161)
                ·
                  refine ⟨3336221196863048270719621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4448294929150731027626161 3336221196863048270719621)
                  ·
                    refine ⟨625541474411821550759929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3336221196863048270719621 625541474411821550759929)
                    ·
                      rfl

theorem cell23_3654713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 4].length) (baseStart_3654713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654713 prefixEnd_3654713 := by exact prefixLift 3654713
  have htrace : WordTrace (prefixWord ++ tailWord_3654713) baseStart_3654713 baseEnd_3654713 := by
    simpa [prefixWord, tailWord_3654713, baseEnd_3654713] using wordTrace_append hprefix tailTrace_3654713
  have hstable : (prefixWord ++ tailWord_3654713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654713).length < 2 ^ (prefixWord ++ tailWord_3654713).sum := by decide
  have hdescent : baseEnd_3654713 < baseStart_3654713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654720 : List Nat := [2, 1, 1, 2, 2, 3, 1, 6, 1, 2, 2]
def baseStart_3654720 : Nat := 118140960795 + 3654720 * 2 ^ 59
def prefixEnd_3654720 : Nat := 4983230072969 + 3 ^ 40 * 3654720 * 2
def baseEnd_3654720 : Nat := 1876628017600046124892255

theorem tailTrace_3654720 : CollatzResearch.WordTrace tailWord_3654720 prefixEnd_3654720 1876628017600046124892255 := by
  unfold tailWord_3654720
  simp only [CollatzResearch.WordTrace]
  refine ⟨66649294659790545663940807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88865726213054060885254409 66649294659790545663940807)
  ·
    refine ⟨99973941989685818495911211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66649294659790545663940807 99973941989685818495911211)
    ·
      refine ⟨149960912984528727743866817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99973941989685818495911211 149960912984528727743866817)
      ·
        refine ⟨112470684738396545807900113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149960912984528727743866817 112470684738396545807900113)
        ·
          refine ⟨84353013553797409355925085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112470684738396545807900113 84353013553797409355925085)
          ·
            refine ⟨31632380082674028508471907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84353013553797409355925085 31632380082674028508471907)
            ·
              refine ⟨47448570124011042762707861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31632380082674028508471907 47448570124011042762707861)
              ·
                refine ⟨2224151724563017629501931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47448570124011042762707861 2224151724563017629501931)
                ·
                  refine ⟨3336227586844526444252897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224151724563017629501931 3336227586844526444252897)
                  ·
                    refine ⟨2502170690133394833189673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3336227586844526444252897 2502170690133394833189673)
                    ·
                      refine ⟨1876628017600046124892255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502170690133394833189673 1876628017600046124892255)
                      ·
                        rfl

theorem cell23_3654720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 1, 2, 2].length) (baseStart_3654720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654720 prefixEnd_3654720 := by exact prefixLift 3654720
  have htrace : WordTrace (prefixWord ++ tailWord_3654720) baseStart_3654720 baseEnd_3654720 := by
    simpa [prefixWord, tailWord_3654720, baseEnd_3654720] using wordTrace_append hprefix tailTrace_3654720
  have hstable : (prefixWord ++ tailWord_3654720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654720).length < 2 ^ (prefixWord ++ tailWord_3654720).sum := by decide
  have hdescent : baseEnd_3654720 < baseStart_3654720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654733 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_3654733 : Nat := 118140960795 + 3654733 * 2 ^ 59
def prefixEnd_3654733 : Nat := 4983230072969 + 3 ^ 40 * 3654733 * 2
def baseEnd_3654733 : Nat := 1876634692848554574029695

theorem tailTrace_3654733 : CollatzResearch.WordTrace tailWord_3654733 prefixEnd_3654733 1876634692848554574029695 := by
  unfold tailWord_3654733
  simp only [CollatzResearch.WordTrace]
  refine ⟨133299063468533994548104853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88866042312355996365403235 133299063468533994548104853)
  ·
    refine ⟨6248393600087530994442415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133299063468533994548104853 6248393600087530994442415)
    ·
      refine ⟨9372590400131296491663623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6248393600087530994442415 9372590400131296491663623)
      ·
        refine ⟨14058885600196944737495435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9372590400131296491663623 14058885600196944737495435)
        ·
          refine ⟨21088328400295417106243153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14058885600196944737495435 21088328400295417106243153)
          ·
            refine ⟨15816246300221562829682365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21088328400295417106243153 15816246300221562829682365)
            ·
              refine ⟨5931092362583086061130887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15816246300221562829682365 5931092362583086061130887)
              ·
                refine ⟨8896638543874629091696331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5931092362583086061130887 8896638543874629091696331)
                ·
                  refine ⟨13344957815811943637544497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8896638543874629091696331 13344957815811943637544497)
                  ·
                    refine ⟨10008718361858957728158373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13344957815811943637544497 10008718361858957728158373)
                    ·
                      refine ⟨1876634692848554574029695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10008718361858957728158373 1876634692848554574029695)
                      ·
                        rfl

theorem cell23_3654733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_3654733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654733 prefixEnd_3654733 := by exact prefixLift 3654733
  have htrace : WordTrace (prefixWord ++ tailWord_3654733) baseStart_3654733 baseEnd_3654733 := by
    simpa [prefixWord, tailWord_3654733, baseEnd_3654733] using wordTrace_append hprefix tailTrace_3654733
  have hstable : (prefixWord ++ tailWord_3654733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654733).length < 2 ^ (prefixWord ++ tailWord_3654733).sum := by decide
  have hdescent : baseEnd_3654733 < baseStart_3654733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654754 : List Nat := [3, 3, 2, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3654754 : Nat := 118140960795 + 3654754 * 2 ^ 59
def prefixEnd_3654754 : Nat := 4983230072969 + 3 ^ 40 * 3654754 * 2
def baseEnd_3654754 : Nat := 1876645475942298991867099

theorem tailTrace_3654754 : CollatzResearch.WordTrace tailWord_3654754 prefixEnd_3654754 1876645475942298991867099 := by
  unfold tailWord_3654754
  simp only [CollatzResearch.WordTrace]
  refine ⟨33324957350364478783654829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88866552934305276756412877 33324957350364478783654829)
  ·
    refine ⟨12496859006386679543870561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33324957350364478783654829 12496859006386679543870561)
    ·
      refine ⟨9372644254790009657902921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12496859006386679543870561 9372644254790009657902921)
      ·
        refine ⟨7029483191092507243427191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9372644254790009657902921 7029483191092507243427191)
        ·
          refine ⟨10544224786638760865140787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029483191092507243427191 10544224786638760865140787)
          ·
            refine ⟨15816337179958141297711181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10544224786638760865140787 15816337179958141297711181)
            ·
              refine ⟨5931126442484302986641693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15816337179958141297711181 5931126442484302986641693)
              ·
                refine ⟨2224172415931613619990635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5931126442484302986641693 2224172415931613619990635)
                ·
                  refine ⟨3336258623897420429985953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224172415931613619990635 3336258623897420429985953)
                  ·
                    refine ⟨2502193967923065322489465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3336258623897420429985953 2502193967923065322489465)
                    ·
                      refine ⟨1876645475942298991867099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502193967923065322489465 1876645475942298991867099)
                      ·
                        rfl

theorem cell23_3654754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3654754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654754 prefixEnd_3654754 := by exact prefixLift 3654754
  have htrace : WordTrace (prefixWord ++ tailWord_3654754) baseStart_3654754 baseEnd_3654754 := by
    simpa [prefixWord, tailWord_3654754, baseEnd_3654754] using wordTrace_append hprefix tailTrace_3654754
  have hstable : (prefixWord ++ tailWord_3654754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654754).length < 2 ^ (prefixWord ++ tailWord_3654754).sum := by decide
  have hdescent : baseEnd_3654754 < baseStart_3654754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654769 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 2, 6]
def baseStart_3654769 : Nat := 118140960795 + 3654769 * 2 ^ 59
def prefixEnd_3654769 : Nat := 4983230072969 + 3 ^ 40 * 3654769 * 2
def baseEnd_3654769 : Nat := 625551059384038811059843

theorem tailTrace_3654769 : CollatzResearch.WordTrace tailWord_3654769 prefixEnd_3654769 625551059384038811059843 := by
  unfold tailWord_3654769
  simp only [CollatzResearch.WordTrace]
  refine ⟨133300376496403572696415361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88866917664269048464276907 133300376496403572696415361)
  ·
    refine ⟨99975282372302679522311521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133300376496403572696415361 99975282372302679522311521)
    ·
      refine ⟨74981461779227009641733641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99975282372302679522311521 74981461779227009641733641)
      ·
        refine ⟨56236096334420257231300231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74981461779227009641733641 56236096334420257231300231)
        ·
          refine ⟨84354144501630385846950347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56236096334420257231300231 84354144501630385846950347)
          ·
            refine ⟨126531216752445578770425521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84354144501630385846950347 126531216752445578770425521)
            ·
              refine ⟨94898412564334184077819141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126531216752445578770425521 94898412564334184077819141)
              ·
                refine ⟨17793452355812659514591089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94898412564334184077819141 17793452355812659514591089)
                ·
                  refine ⟨13345089266859494635943317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17793452355812659514591089 13345089266859494635943317)
                  ·
                    refine ⟨625551059384038811059843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13345089266859494635943317 625551059384038811059843)
                    ·
                      rfl

theorem cell23_3654769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_3654769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654769 prefixEnd_3654769 := by exact prefixLift 3654769
  have htrace : WordTrace (prefixWord ++ tailWord_3654769) baseStart_3654769 baseEnd_3654769 := by
    simpa [prefixWord, tailWord_3654769, baseEnd_3654769] using wordTrace_append hprefix tailTrace_3654769
  have hstable : (prefixWord ++ tailWord_3654769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654769).length < 2 ^ (prefixWord ++ tailWord_3654769).sum := by decide
  have hdescent : baseEnd_3654769 < baseStart_3654769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654810 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3654810 : Nat := 118140960795 + 3654810 * 2 ^ 59
def prefixEnd_3654810 : Nat := 4983230072969 + 3 ^ 40 * 3654810 * 2
def baseEnd_3654810 : Nat := 1876674230858950772766841

theorem tailTrace_3654810 : CollatzResearch.WordTrace tailWord_3654810 prefixEnd_3654810 1876674230858950772766841 := by
  unfold tailWord_3654810
  simp only [CollatzResearch.WordTrace]
  refine ⟨33325467972313759174664471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88867914592836691132438589 33325467972313759174664471)
  ·
    refine ⟨49988201958470638761996707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33325467972313759174664471 49988201958470638761996707)
    ·
      refine ⟨74982302937705958142995061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49988201958470638761996707 74982302937705958142995061)
      ·
        refine ⟨7029590900409933575905787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74982302937705958142995061 7029590900409933575905787)
        ·
          refine ⟨10544386350614900363858681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029590900409933575905787 10544386350614900363858681)
          ·
            refine ⟨7908289762961175272894011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10544386350614900363858681 7908289762961175272894011)
            ·
              refine ⟨11862434644441762909341017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908289762961175272894011 11862434644441762909341017)
              ·
                refine ⟨8896825983331322182005763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11862434644441762909341017 8896825983331322182005763)
                ·
                  refine ⟨13345238974996983273008645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8896825983331322182005763 13345238974996983273008645)
                  ·
                    refine ⟨2502232307811934363689121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13345238974996983273008645 2502232307811934363689121)
                    ·
                      refine ⟨1876674230858950772766841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502232307811934363689121 1876674230858950772766841)
                      ·
                        rfl

theorem cell23_3654810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3654810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654810 prefixEnd_3654810 := by exact prefixLift 3654810
  have htrace : WordTrace (prefixWord ++ tailWord_3654810) baseStart_3654810 baseEnd_3654810 := by
    simpa [prefixWord, tailWord_3654810, baseEnd_3654810] using wordTrace_append hprefix tailTrace_3654810
  have hstable : (prefixWord ++ tailWord_3654810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654810).length < 2 ^ (prefixWord ++ tailWord_3654810).sum := by decide
  have hdescent : baseEnd_3654810 < baseStart_3654810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654814 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_3654814 : Nat := 118140960795 + 3654814 * 2 ^ 59
def prefixEnd_3654814 : Nat := 4983230072969 + 3 ^ 40 * 3654814 * 2
def baseEnd_3654814 : Nat := 1876676284781568757116823

theorem tailTrace_3654814 : CollatzResearch.WordTrace tailWord_3654814 prefixEnd_3654814 1876676284781568757116823 := by
  unfold tailWord_3654814
  simp only [CollatzResearch.WordTrace]
  refine ⟨16662752222655068172725437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88868011854160363587868997 16662752222655068172725437)
  ·
    refine ⟨6248532083495650564772039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16662752222655068172725437 6248532083495650564772039)
    ·
      refine ⟨9372798125243475847158059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6248532083495650564772039 9372798125243475847158059)
      ·
        refine ⟨14059197187865213770737089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9372798125243475847158059 14059197187865213770737089)
        ·
          refine ⟨10544397890898910328052817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14059197187865213770737089 10544397890898910328052817)
          ·
            refine ⟨7908298418174182746039613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10544397890898910328052817 7908298418174182746039613)
            ·
              refine ⟨2965611906815318529764855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7908298418174182746039613 2965611906815318529764855)
              ·
                refine ⟨4448417860222977794647283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965611906815318529764855 4448417860222977794647283)
                ·
                  refine ⟨6672626790334466691970925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448417860222977794647283 6672626790334466691970925)
                  ·
                    refine ⟨2502235046375425009489097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6672626790334466691970925 2502235046375425009489097)
                    ·
                      refine ⟨1876676284781568757116823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502235046375425009489097 1876676284781568757116823)
                      ·
                        rfl

theorem cell23_3654814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_3654814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654814 prefixEnd_3654814 := by exact prefixLift 3654814
  have htrace : WordTrace (prefixWord ++ tailWord_3654814) baseStart_3654814 baseEnd_3654814 := by
    simpa [prefixWord, tailWord_3654814, baseEnd_3654814] using wordTrace_append hprefix tailTrace_3654814
  have hstable : (prefixWord ++ tailWord_3654814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654814).length < 2 ^ (prefixWord ++ tailWord_3654814).sum := by decide
  have hdescent : baseEnd_3654814 < baseStart_3654814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654859 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 1, 10]
def baseStart_3654859 : Nat := 118140960795 + 3654859 * 2 ^ 59
def prefixEnd_3654859 : Nat := 4983230072969 + 3 ^ 40 * 3654859 * 2
def baseEnd_3654859 : Nat := 625566463803673693684705

theorem tailTrace_3654859 : CollatzResearch.WordTrace tailWord_3654859 prefixEnd_3654859 625566463803673693684705 := by
  unfold tailWord_3654859
  simp only [CollatzResearch.WordTrace]
  refine ⟨133303659066077518067191631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88869106044051678711461087 133303659066077518067191631)
  ·
    refine ⟨199955488599116277100787447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133303659066077518067191631 199955488599116277100787447)
    ·
      refine ⟨299933232898674415651181171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199955488599116277100787447 299933232898674415651181171)
      ·
        refine ⟨449899849348011623476771757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299933232898674415651181171 449899849348011623476771757)
        ·
          refine ⟨168712443505504358803789409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449899849348011623476771757 168712443505504358803789409)
          ·
            refine ⟨126534332629128269102842057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168712443505504358803789409 126534332629128269102842057)
            ·
              refine ⟨94900749471846201827131543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126534332629128269102842057 94900749471846201827131543)
              ·
                refine ⟨142351124207769302740697315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94900749471846201827131543 142351124207769302740697315)
                ·
                  refine ⟨213526686311653954111045973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142351124207769302740697315 213526686311653954111045973)
                  ·
                    refine ⟨625566463803673693684705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 213526686311653954111045973 625566463803673693684705)
                    ·
                      rfl

theorem cell23_3654859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 10].length) (baseStart_3654859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654859 prefixEnd_3654859 := by exact prefixLift 3654859
  have htrace : WordTrace (prefixWord ++ tailWord_3654859) baseStart_3654859 baseEnd_3654859 := by
    simpa [prefixWord, tailWord_3654859, baseEnd_3654859] using wordTrace_append hprefix tailTrace_3654859
  have hstable : (prefixWord ++ tailWord_3654859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654859).length < 2 ^ (prefixWord ++ tailWord_3654859).sum := by decide
  have hdescent : baseEnd_3654859 < baseStart_3654859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654910 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3654910 : Nat := 118140960795 + 3654910 * 2 ^ 59
def prefixEnd_3654910 : Nat := 4983230072969 + 3 ^ 40 * 3654910 * 2
def baseEnd_3654910 : Nat := 625575192974800127172127

theorem tailTrace_3654910 : CollatzResearch.WordTrace tailWord_3654910 prefixEnd_3654910 625575192974800127172127 := by
  unfold tailWord_3654910
  simp only [CollatzResearch.WordTrace]
  refine ⟨16663189898611594222162273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88870346125928502518198789 16663189898611594222162273)
  ·
    refine ⟨12497392423958695666621705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16663189898611594222162273 12497392423958695666621705)
    ·
      refine ⟨9373044317969021749966279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12497392423958695666621705 9373044317969021749966279)
      ·
        refine ⟨14059566476953532624949419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9373044317969021749966279 14059566476953532624949419)
        ·
          refine ⟨21089349715430298937424129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14059566476953532624949419 21089349715430298937424129)
          ·
            refine ⟨15817012286572724203068097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21089349715430298937424129 15817012286572724203068097)
            ·
              refine ⟨11862759214929543152301073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15817012286572724203068097 11862759214929543152301073)
              ·
                refine ⟨8897069411197157364225805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11862759214929543152301073 8897069411197157364225805)
                ·
                  refine ⟨3336401029198934011584677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8897069411197157364225805 3336401029198934011584677)
                  ·
                    refine ⟨625575192974800127172127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3336401029198934011584677 625575192974800127172127)
                    ·
                      rfl

theorem cell23_3654910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3654910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654910 prefixEnd_3654910 := by exact prefixLift 3654910
  have htrace : WordTrace (prefixWord ++ tailWord_3654910) baseStart_3654910 baseEnd_3654910 := by
    simpa [prefixWord, tailWord_3654910, baseEnd_3654910] using wordTrace_append hprefix tailTrace_3654910
  have hstable : (prefixWord ++ tailWord_3654910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654910).length < 2 ^ (prefixWord ++ tailWord_3654910).sum := by decide
  have hdescent : baseEnd_3654910 < baseStart_3654910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654944 : List Nat := [2, 1, 1, 5, 3, 1, 3, 2, 1, 4]
def baseStart_3654944 : Nat := 118140960795 + 3654944 * 2 ^ 59
def prefixEnd_3654944 : Nat := 4983230072969 + 3 ^ 40 * 3654944 * 2
def baseEnd_3654944 : Nat := 625581012422217749497075

theorem tailTrace_3654944 : CollatzResearch.WordTrace tailWord_3654944 prefixEnd_3654944 625581012422217749497075 := by
  unfold tailWord_3654944
  simp only [CollatzResearch.WordTrace]
  refine ⟨66653379635384788792017943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88871172847179718389357257 66653379635384788792017943)
  ·
    refine ⟨99980069453077183188026915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66653379635384788792017943 99980069453077183188026915)
    ·
      refine ⟨149970104179615774782040373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99980069453077183188026915 149970104179615774782040373)
      ·
        refine ⟨14059697266838978885816285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149970104179615774782040373 14059697266838978885816285)
        ·
          refine ⟨5272386475064617082181107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14059697266838978885816285 5272386475064617082181107)
          ·
            refine ⟨7908579712596925623271661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272386475064617082181107 7908579712596925623271661)
            ·
              refine ⟨2965717392223847108726873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7908579712596925623271661 2965717392223847108726873)
              ·
                refine ⟨2224288044167885331545155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2965717392223847108726873 2224288044167885331545155)
                ·
                  refine ⟨3336432066251827997317733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224288044167885331545155 3336432066251827997317733)
                  ·
                    refine ⟨625581012422217749497075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3336432066251827997317733 625581012422217749497075)
                    ·
                      rfl

theorem cell23_3654944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 2, 1, 4].length) (baseStart_3654944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654944 prefixEnd_3654944 := by exact prefixLift 3654944
  have htrace : WordTrace (prefixWord ++ tailWord_3654944) baseStart_3654944 baseEnd_3654944 := by
    simpa [prefixWord, tailWord_3654944, baseEnd_3654944] using wordTrace_append hprefix tailTrace_3654944
  have hstable : (prefixWord ++ tailWord_3654944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654944).length < 2 ^ (prefixWord ++ tailWord_3654944).sum := by decide
  have hdescent : baseEnd_3654944 < baseStart_3654944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654956 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_3654956 : Nat := 118140960795 + 3654956 * 2 ^ 59
def prefixEnd_3654956 : Nat := 4983230072969 + 3 ^ 40 * 3654956 * 2
def baseEnd_3654956 : Nat := 1876749199034507201541169

theorem tailTrace_3654956 : CollatzResearch.WordTrace tailWord_3654956 prefixEnd_3654956 1876749199034507201541169 := by
  unfold tailWord_3654956
  simp only [CollatzResearch.WordTrace]
  refine ⟨66653598473363051816736361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88871464631150735755648481 66653598473363051816736361)
  ·
    refine ⟨49990198855022288862552271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66653598473363051816736361 49990198855022288862552271)
    ·
      refine ⟨74985298282533433293828407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49990198855022288862552271 74985298282533433293828407)
      ·
        refine ⟨112477947423800149940742611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74985298282533433293828407 112477947423800149940742611)
        ·
          refine ⟨168716921135700224911113917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112477947423800149940742611 168716921135700224911113917)
          ·
            refine ⟨63268845425887584341667719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168716921135700224911113917 63268845425887584341667719)
            ·
              refine ⟨94903268138831376512501579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63268845425887584341667719 94903268138831376512501579)
              ·
                refine ⟨142354902208247064768752369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94903268138831376512501579 142354902208247064768752369)
                ·
                  refine ⟨106766176656185298576564277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142354902208247064768752369 106766176656185298576564277)
                  ·
                    refine ⟨10009329061517371741552901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106766176656185298576564277 10009329061517371741552901)
                    ·
                      refine ⟨1876749199034507201541169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10009329061517371741552901 1876749199034507201541169)
                      ·
                        rfl

theorem cell23_3654956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_3654956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654956 prefixEnd_3654956 := by exact prefixLift 3654956
  have htrace : WordTrace (prefixWord ++ tailWord_3654956) baseStart_3654956 baseEnd_3654956 := by
    simpa [prefixWord, tailWord_3654956, baseEnd_3654956] using wordTrace_append hprefix tailTrace_3654956
  have hstable : (prefixWord ++ tailWord_3654956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654956).length < 2 ^ (prefixWord ++ tailWord_3654956).sum := by decide
  have hdescent : baseEnd_3654956 < baseStart_3654956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654957 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 6]
def baseStart_3654957 : Nat := 118140960795 + 3654957 * 2 ^ 59
def prefixEnd_3654957 : Nat := 4983230072969 + 3 ^ 40 * 3654957 * 2
def baseEnd_3654957 : Nat := 208527745835017966403185

theorem tailTrace_3654957 : CollatzResearch.WordTrace tailWord_3654957 prefixEnd_3654957 208527745835017966403185 := by
  unfold tailWord_3654957
  simp only [CollatzResearch.WordTrace]
  refine ⟨133307233419722480804259125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88871488946481653869506083 133307233419722480804259125)
  ·
    refine ⟨12497553133098982575399293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133307233419722480804259125 12497553133098982575399293)
    ·
      refine ⟨4686582424912118465774735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12497553133098982575399293 4686582424912118465774735)
      ·
        refine ⟨7029873637368177698662103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4686582424912118465774735 7029873637368177698662103)
        ·
          refine ⟨10544810456052266547993155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029873637368177698662103 10544810456052266547993155)
          ·
            refine ⟨15817215684078399821989733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10544810456052266547993155 15817215684078399821989733)
            ·
              refine ⟨2965727940764699966623075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15817215684078399821989733 2965727940764699966623075)
              ·
                refine ⟨4448591911147049949934613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965727940764699966623075 4448591911147049949934613)
                ·
                  refine ⟨208527745835017966403185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4448591911147049949934613 208527745835017966403185)
                  ·
                    rfl

theorem cell23_3654957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_3654957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654957 prefixEnd_3654957 := by exact prefixLift 3654957
  have htrace : WordTrace (prefixWord ++ tailWord_3654957) baseStart_3654957 baseEnd_3654957 := by
    simpa [prefixWord, tailWord_3654957, baseEnd_3654957] using wordTrace_append hprefix tailTrace_3654957
  have hstable : (prefixWord ++ tailWord_3654957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654957).length < 2 ^ (prefixWord ++ tailWord_3654957).sum := by decide
  have hdescent : baseEnd_3654957 < baseStart_3654957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654977 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3654977 : Nat := 118140960795 + 3654977 * 2 ^ 59
def prefixEnd_3654977 : Nat := 4983230072969 + 3 ^ 40 * 3654977 * 2
def baseEnd_3654977 : Nat := 1876759982128251619378573

theorem tailTrace_3654977 : CollatzResearch.WordTrace tailWord_3654977 prefixEnd_3654977 1876759982128251619378573 := by
  unfold tailWord_3654977
  simp only [CollatzResearch.WordTrace]
  refine ⟨133307962879650024219987185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88871975253100016146658123 133307962879650024219987185)
  ·
    refine ⟨99980972159737518164990389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133307962879650024219987185 99980972159737518164990389)
    ·
      refine ⟨9373216139975392327967849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99980972159737518164990389 9373216139975392327967849)
      ·
        refine ⟨7029912104981544245975887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9373216139975392327967849 7029912104981544245975887)
        ·
          refine ⟨10544868157472316368963831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7029912104981544245975887 10544868157472316368963831)
          ·
            refine ⟨15817302236208474553445747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10544868157472316368963831 15817302236208474553445747)
            ·
              refine ⟨23725953354312711830168621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15817302236208474553445747 23725953354312711830168621)
              ·
                refine ⟨8897232507867266936313233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23725953354312711830168621 8897232507867266936313233)
                ·
                  refine ⟨6672924380900450202234925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8897232507867266936313233 6672924380900450202234925)
                  ·
                    refine ⟨2502346642837668825838097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6672924380900450202234925 2502346642837668825838097)
                    ·
                      refine ⟨1876759982128251619378573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502346642837668825838097 1876759982128251619378573)
                      ·
                        rfl

theorem cell23_3654977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3654977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654977 prefixEnd_3654977 := by exact prefixLift 3654977
  have htrace : WordTrace (prefixWord ++ tailWord_3654977) baseStart_3654977 baseEnd_3654977 := by
    simpa [prefixWord, tailWord_3654977, baseEnd_3654977] using wordTrace_append hprefix tailTrace_3654977
  have hstable : (prefixWord ++ tailWord_3654977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654977).length < 2 ^ (prefixWord ++ tailWord_3654977).sum := by decide
  have hdescent : baseEnd_3654977 < baseStart_3654977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654983 : List Nat := [1, 1, 4, 1, 2, 4, 1, 2, 1, 6]
def baseStart_3654983 : Nat := 118140960795 + 3654983 * 2 ^ 59
def prefixEnd_3654983 : Nat := 4983230072969 + 3 ^ 40 * 3654983 * 2
def baseEnd_3654983 : Nat := 625587687670726198634515

theorem tailTrace_3654983 : CollatzResearch.WordTrace tailWord_3654983 prefixEnd_3654983 625587687670726198634515 := by
  unfold tailWord_3654983
  simp only [CollatzResearch.WordTrace]
  refine ⟨133308181717628287244705603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88872121145085524829803735 133308181717628287244705603)
  ·
    refine ⟨199962272576442430867058405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133308181717628287244705603 199962272576442430867058405)
    ·
      refine ⟨37492926108082955787573451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199962272576442430867058405 37492926108082955787573451)
      ·
        refine ⟨56239389162124433681360177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37492926108082955787573451 56239389162124433681360177)
        ·
          refine ⟨42179541871593325261020133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56239389162124433681360177 42179541871593325261020133)
          ·
            refine ⟨7908664100923748486441275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42179541871593325261020133 7908664100923748486441275)
            ·
              refine ⟨11862996151385622729661913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7908664100923748486441275 11862996151385622729661913)
              ·
                refine ⟨8897247113539217047246435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11862996151385622729661913 8897247113539217047246435)
                ·
                  refine ⟨13345870670308825570869653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8897247113539217047246435 13345870670308825570869653)
                  ·
                    refine ⟨625587687670726198634515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13345870670308825570869653 625587687670726198634515)
                    ·
                      rfl

theorem cell23_3654983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_3654983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654983 prefixEnd_3654983 := by exact prefixLift 3654983
  have htrace : WordTrace (prefixWord ++ tailWord_3654983) baseStart_3654983 baseEnd_3654983 := by
    simpa [prefixWord, tailWord_3654983, baseEnd_3654983] using wordTrace_append hprefix tailTrace_3654983
  have hstable : (prefixWord ++ tailWord_3654983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654983).length < 2 ^ (prefixWord ++ tailWord_3654983).sum := by decide
  have hdescent : baseEnd_3654983 < baseStart_3654983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655000 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 2, 4]
def baseStart_3655000 : Nat := 118140960795 + 3655000 * 2 ^ 59
def prefixEnd_3655000 : Nat := 4983230072969 + 3 ^ 40 * 3655000 * 2
def baseEnd_3655000 : Nat := 625590597394435009796989

theorem tailTrace_3655000 : CollatzResearch.WordTrace tailWord_3655000 prefixEnd_3655000 625590597394435009796989 := by
  unfold tailWord_3655000
  simp only [CollatzResearch.WordTrace]
  refine ⟨66654400879283349574037227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88872534505711132765382969 66654400879283349574037227)
  ·
    refine ⟨99981601318925024361055841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66654400879283349574037227 99981601318925024361055841)
    ·
      refine ⟨74986200989193768270791881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99981601318925024361055841 74986200989193768270791881)
      ·
        refine ⟨56239650741895326203093911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74986200989193768270791881 56239650741895326203093911)
        ·
          refine ⟨84359476112842989304640867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56239650741895326203093911 84359476112842989304640867)
          ·
            refine ⟨126539214169264483956961301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84359476112842989304640867 126539214169264483956961301)
            ·
              refine ⟨5931525664184272685482561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126539214169264483956961301 5931525664184272685482561)
              ·
                refine ⟨4448644248138204514111921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5931525664184272685482561 4448644248138204514111921)
                ·
                  refine ⟨3336483186103653385583941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4448644248138204514111921 3336483186103653385583941)
                  ·
                    refine ⟨625590597394435009796989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3336483186103653385583941 625590597394435009796989)
                    ·
                      rfl

theorem cell23_3655000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_3655000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655000 prefixEnd_3655000 := by exact prefixLift 3655000
  have htrace : WordTrace (prefixWord ++ tailWord_3655000) baseStart_3655000 baseEnd_3655000 := by
    simpa [prefixWord, tailWord_3655000, baseEnd_3655000] using wordTrace_append hprefix tailTrace_3655000
  have hstable : (prefixWord ++ tailWord_3655000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655000).length < 2 ^ (prefixWord ++ tailWord_3655000).sum := by decide
  have hdescent : baseEnd_3655000 < baseStart_3655000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655010 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_3655010 : Nat := 118140960795 + 3655010 * 2 ^ 59
def prefixEnd_3655010 : Nat := 4983230072969 + 3 ^ 40 * 3655010 * 2
def baseEnd_3655010 : Nat := 1876776926989849990265921

theorem tailTrace_3655010 : CollatzResearch.WordTrace tailWord_3655010 prefixEnd_3655010 1876776926989849990265921 := by
  unfold tailWord_3655010
  simp only [CollatzResearch.WordTrace]
  refine ⟨33327291622132617713984621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88872777659020313903958989 33327291622132617713984621)
  ·
    refine ⟨12497734358299731642744233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33327291622132617713984621 12497734358299731642744233)
    ·
      refine ⟨9373300768724798732058175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12497734358299731642744233 9373300768724798732058175)
      ·
        refine ⟨14059951153087198098087263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9373300768724798732058175 14059951153087198098087263)
        ·
          refine ⟨21089926729630797147130895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14059951153087198098087263 21089926729630797147130895)
          ·
            refine ⟨31634890094446195720696343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21089926729630797147130895 31634890094446195720696343)
            ·
              refine ⟨47452335141669293581044515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31634890094446195720696343 47452335141669293581044515)
              ·
                refine ⟨71178502712503940371566773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47452335141669293581044515 71178502712503940371566773)
                ·
                  refine ⟨6672984629297244409834385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71178502712503940371566773 6672984629297244409834385)
                  ·
                    refine ⟨5004738471972933307375789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6672984629297244409834385 5004738471972933307375789)
                    ·
                      refine ⟨1876776926989849990265921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5004738471972933307375789 1876776926989849990265921)
                      ·
                        rfl

theorem cell23_3655010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_3655010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655010 prefixEnd_3655010 := by exact prefixLift 3655010
  have htrace : WordTrace (prefixWord ++ tailWord_3655010) baseStart_3655010 baseEnd_3655010 := by
    simpa [prefixWord, tailWord_3655010, baseEnd_3655010] using wordTrace_append hprefix tailTrace_3655010
  have hstable : (prefixWord ++ tailWord_3655010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655010).length < 2 ^ (prefixWord ++ tailWord_3655010).sum := by decide
  have hdescent : baseEnd_3655010 < baseStart_3655010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655020 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 4]
def baseStart_3655020 : Nat := 118140960795 + 3655020 * 2 ^ 59
def prefixEnd_3655020 : Nat := 4983230072969 + 3 ^ 40 * 3655020 * 2
def baseEnd_3655020 : Nat := 1876782061796394951140875

theorem tailTrace_3655020 : CollatzResearch.WordTrace tailWord_3655020 prefixEnd_3655020 1876782061796394951140875 := by
  unfold tailWord_3655020
  simp only [CollatzResearch.WordTrace]
  refine ⟨66654765609247121281901257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88873020812329495042535009 66654765609247121281901257)
  ·
    refine ⟨49991074206935340961425943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66654765609247121281901257 49991074206935340961425943)
    ·
      refine ⟨74986611310403011442138915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49991074206935340961425943 74986611310403011442138915)
      ·
        refine ⟨112479916965604517163208373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74986611310403011442138915 112479916965604517163208373)
        ·
          refine ⟨10544992215525423484050785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112479916965604517163208373 10544992215525423484050785)
          ·
            refine ⟨7908744161644067613038089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10544992215525423484050785 7908744161644067613038089)
            ·
              refine ⟨5931558121233050709778567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7908744161644067613038089 5931558121233050709778567)
              ·
                refine ⟨8897337181849576064667851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5931558121233050709778567 8897337181849576064667851)
                ·
                  refine ⟨13346005772774364097001777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8897337181849576064667851 13346005772774364097001777)
                  ·
                    refine ⟨10009504329580773072751333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13346005772774364097001777 10009504329580773072751333)
                    ·
                      refine ⟨1876782061796394951140875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10009504329580773072751333 1876782061796394951140875)
                      ·
                        rfl

theorem cell23_3655020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_3655020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655020 prefixEnd_3655020 := by exact prefixLift 3655020
  have htrace : WordTrace (prefixWord ++ tailWord_3655020) baseStart_3655020 baseEnd_3655020 := by
    simpa [prefixWord, tailWord_3655020, baseEnd_3655020] using wordTrace_append hprefix tailTrace_3655020
  have hstable : (prefixWord ++ tailWord_3655020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655020).length < 2 ^ (prefixWord ++ tailWord_3655020).sum := by decide
  have hdescent : baseEnd_3655020 < baseStart_3655020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655038 : List Nat := [4, 2, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_3655038 : Nat := 118140960795 + 3655038 * 2 ^ 59
def prefixEnd_3655038 : Nat := 4983230072969 + 3 ^ 40 * 3655038 * 2
def baseEnd_3655038 : Nat := 625597101482725293571931

theorem tailTrace_3655038 : CollatzResearch.WordTrace tailWord_3655038 prefixEnd_3655038 625597101482725293571931 := by
  unfold tailWord_3655038
  simp only [CollatzResearch.WordTrace]
  refine ⟨16663773466553628954744721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88873458488286021091971845 16663773466553628954744721)
  ·
    refine ⟨12497830099915221716058541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16663773466553628954744721 12497830099915221716058541)
    ·
      refine ⟨4686686287468208143521953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12497830099915221716058541 4686686287468208143521953)
      ·
        refine ⟨3515014715601156107641465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4686686287468208143521953 3515014715601156107641465)
        ·
          refine ⟨2636261036700867080731099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3515014715601156107641465 2636261036700867080731099)
          ·
            refine ⟨3954391555051300621096649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636261036700867080731099 3954391555051300621096649)
            ·
              refine ⟨2965793666288475465822487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3954391555051300621096649 2965793666288475465822487)
              ·
                refine ⟨4448690499432713198733731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965793666288475465822487 4448690499432713198733731)
                ·
                  refine ⟨6673035749149069798100597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448690499432713198733731 6673035749149069798100597)
                  ·
                    refine ⟨625597101482725293571931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6673035749149069798100597 625597101482725293571931)
                    ·
                      rfl

theorem cell23_3655038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_3655038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655038 prefixEnd_3655038 := by exact prefixLift 3655038
  have htrace : WordTrace (prefixWord ++ tailWord_3655038) baseStart_3655038 baseEnd_3655038 := by
    simpa [prefixWord, tailWord_3655038, baseEnd_3655038] using wordTrace_append hprefix tailTrace_3655038
  have hstable : (prefixWord ++ tailWord_3655038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655038).length < 2 ^ (prefixWord ++ tailWord_3655038).sum := by decide
  have hdescent : baseEnd_3655038 < baseStart_3655038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655041 : List Nat := [1, 2, 4, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_3655041 : Nat := 118140960795 + 3655041 * 2 ^ 59
def prefixEnd_3655041 : Nat := 4983230072969 + 3 ^ 40 * 3655041 * 2
def baseEnd_3655041 : Nat := 1876792844890139368978279

theorem tailTrace_3655041 : CollatzResearch.WordTrace tailWord_3655041 prefixEnd_3655041 1876792844890139368978279 := by
  unfold tailWord_3655041
  simp only [CollatzResearch.WordTrace]
  refine ⟨133310297151418163150316977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88873531434278775433544651 133310297151418163150316977)
  ·
    refine ⟨99982722863563622362737733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133310297151418163150316977 99982722863563622362737733)
    ·
      refine ⟨18746760536918179193013325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99982722863563622362737733 18746760536918179193013325)
      ·
        refine ⟨7030035201344317197379997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18746760536918179193013325 7030035201344317197379997)
        ·
          refine ⟨2636263200504118949017499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7030035201344317197379997 2636263200504118949017499)
          ·
            refine ⟨3954394800756178423526249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636263200504118949017499 3954394800756178423526249)
            ·
              refine ⟨2965796100567133817644687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3954394800756178423526249 2965796100567133817644687)
              ·
                refine ⟨4448694150850700726467031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965796100567133817644687 4448694150850700726467031)
                ·
                  refine ⟨6673041226276051089700547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448694150850700726467031 6673041226276051089700547)
                  ·
                    refine ⟨10009561839414076634550821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6673041226276051089700547 10009561839414076634550821)
                    ·
                      refine ⟨1876792844890139368978279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10009561839414076634550821 1876792844890139368978279)
                      ·
                        rfl

theorem cell23_3655041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_3655041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655041 prefixEnd_3655041 := by exact prefixLift 3655041
  have htrace : WordTrace (prefixWord ++ tailWord_3655041) baseStart_3655041 baseEnd_3655041 := by
    simpa [prefixWord, tailWord_3655041, baseEnd_3655041] using wordTrace_append hprefix tailTrace_3655041
  have hstable : (prefixWord ++ tailWord_3655041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655041).length < 2 ^ (prefixWord ++ tailWord_3655041).sum := by decide
  have hdescent : baseEnd_3655041 < baseStart_3655041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655044 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_3655044 : Nat := 118140960795 + 3655044 * 2 ^ 59
def prefixEnd_3655044 : Nat := 4983230072969 + 3 ^ 40 * 3655044 * 2
def baseEnd_3655044 : Nat := 1876794385332102857240765

theorem tailTrace_3655044 : CollatzResearch.WordTrace tailWord_3655044 prefixEnd_3655044 1876794385332102857240765 := by
  unfold tailWord_3655044
  simp only [CollatzResearch.WordTrace]
  refine ⟨66655203285203647331338093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88873604380271529775117457 66655203285203647331338093)
  ·
    refine ⟨24995701231951367749251785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66655203285203647331338093 24995701231951367749251785)
    ·
      refine ⟨18746775923963525811938839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24995701231951367749251785 18746775923963525811938839)
      ·
        refine ⟨28120163885945288717908259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18746775923963525811938839 28120163885945288717908259)
        ·
          refine ⟨42180245828917933076862389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28120163885945288717908259 42180245828917933076862389)
          ·
            refine ⟨3954398046461056225955849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42180245828917933076862389 3954398046461056225955849)
            ·
              refine ⟨2965798534845792169466887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3954398046461056225955849 2965798534845792169466887)
              ·
                refine ⟨4448697802268688254200331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965798534845792169466887 4448697802268688254200331)
                ·
                  refine ⟨6673046703403032381300497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4448697802268688254200331 6673046703403032381300497)
                  ·
                    refine ⟨5004785027552274285975373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6673046703403032381300497 5004785027552274285975373)
                    ·
                      refine ⟨1876794385332102857240765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5004785027552274285975373 1876794385332102857240765)
                      ·
                        rfl

theorem cell23_3655044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_3655044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655044 prefixEnd_3655044 := by exact prefixLift 3655044
  have htrace : WordTrace (prefixWord ++ tailWord_3655044) baseStart_3655044 baseEnd_3655044 := by
    simpa [prefixWord, tailWord_3655044, baseEnd_3655044] using wordTrace_append hprefix tailTrace_3655044
  have hstable : (prefixWord ++ tailWord_3655044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655044).length < 2 ^ (prefixWord ++ tailWord_3655044).sum := by decide
  have hdescent : baseEnd_3655044 < baseStart_3655044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655173 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_3655173 : Nat := 118140960795 + 3655173 * 2 ^ 59
def prefixEnd_3655173 : Nat := 4983230072969 + 3 ^ 40 * 3655173 * 2
def baseEnd_3655173 : Nat := 1876860624336532852527671

theorem tailTrace_3655173 : CollatzResearch.WordTrace tailWord_3655173 prefixEnd_3655173 1876860624336532852527671 := by
  unfold tailWord_3655173
  simp only [CollatzResearch.WordTrace]
  refine ⟨133315111586939949694122173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88876741057959966462748115 133315111586939949694122173)
  ·
    refine ⟨49993166845102481135295815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133315111586939949694122173 49993166845102481135295815)
    ·
      refine ⟨74989750267653721702943723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49993166845102481135295815 74989750267653721702943723)
      ·
        refine ⟨112484625401480582554415585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74989750267653721702943723 112484625401480582554415585)
        ·
          refine ⟨84363469051110436915811689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112484625401480582554415585 84363469051110436915811689)
          ·
            refine ⟨63272601788332827686858767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84363469051110436915811689 63272601788332827686858767)
            ·
              refine ⟨94908902682499241530288151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63272601788332827686858767 94908902682499241530288151)
              ·
                refine ⟨142363354023748862295432227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94908902682499241530288151 142363354023748862295432227)
                ·
                  refine ⟨213545031035623293443148341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142363354023748862295432227 213545031035623293443148341)
                  ·
                    refine ⟨20019846659589683760295157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 213545031035623293443148341 20019846659589683760295157)
                    ·
                      refine ⟨1876860624336532852527671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20019846659589683760295157 1876860624336532852527671)
                      ·
                        rfl

theorem cell23_3655173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_3655173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655173 prefixEnd_3655173 := by exact prefixLift 3655173
  have htrace : WordTrace (prefixWord ++ tailWord_3655173) baseStart_3655173 baseEnd_3655173 := by
    simpa [prefixWord, tailWord_3655173, baseEnd_3655173] using wordTrace_append hprefix tailTrace_3655173
  have hstable : (prefixWord ++ tailWord_3655173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655173).length < 2 ^ (prefixWord ++ tailWord_3655173).sum := by decide
  have hdescent : baseEnd_3655173 < baseStart_3655173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655181 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3655181 : Nat := 118140960795 + 3655181 * 2 ^ 59
def prefixEnd_3655181 : Nat := 4983230072969 + 3 ^ 40 * 3655181 * 2
def baseEnd_3655181 : Nat := 1876864732181768821227635

theorem tailTrace_3655181 : CollatzResearch.WordTrace tailWord_3655181 prefixEnd_3655181 1876864732181768821227635 := by
  unfold tailWord_3655181
  simp only [CollatzResearch.WordTrace]
  refine ⟨133315403370910967060413397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88876935580607311373608931 133315403370910967060413397)
  ·
    refine ⟨3124579766505725790478439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 133315403370910967060413397 3124579766505725790478439)
    ·
      refine ⟨4686869649758588685717659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3124579766505725790478439 4686869649758588685717659)
      ·
        refine ⟨7030304474637883028576489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4686869649758588685717659 7030304474637883028576489)
        ·
          refine ⟨5272728355978412271432367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7030304474637883028576489 5272728355978412271432367)
          ·
            refine ⟨7909092533967618407148551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272728355978412271432367 7909092533967618407148551)
            ·
              refine ⟨11863638800951427610722827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7909092533967618407148551 11863638800951427610722827)
              ·
                refine ⟨17795458201427141416084241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11863638800951427610722827 17795458201427141416084241)
                ·
                  refine ⟨13346593651070356062063181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17795458201427141416084241 13346593651070356062063181)
                  ·
                    refine ⟨5004972619151383523273693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13346593651070356062063181 5004972619151383523273693)
                    ·
                      refine ⟨1876864732181768821227635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5004972619151383523273693 1876864732181768821227635)
                      ·
                        rfl

theorem cell23_3655181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3655181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655181 prefixEnd_3655181 := by exact prefixLift 3655181
  have htrace : WordTrace (prefixWord ++ tailWord_3655181) baseStart_3655181 baseEnd_3655181 := by
    simpa [prefixWord, tailWord_3655181, baseEnd_3655181] using wordTrace_append hprefix tailTrace_3655181
  have hstable : (prefixWord ++ tailWord_3655181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655181).length < 2 ^ (prefixWord ++ tailWord_3655181).sum := by decide
  have hdescent : baseEnd_3655181 < baseStart_3655181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655187 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 2, 4, 2]
def baseStart_3655187 : Nat := 118140960795 + 3655187 * 2 ^ 59
def prefixEnd_3655187 : Nat := 4983230072969 + 3 ^ 40 * 3655187 * 2
def baseEnd_3655187 : Nat := 1876867813065695797752607

theorem tailTrace_3655187 : CollatzResearch.WordTrace tailWord_3655187 prefixEnd_3655187 1876867813065695797752607 := by
  unfold tailWord_3655187
  simp only [CollatzResearch.WordTrace]
  refine ⟨133315622208889230085131815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88877081472592820056754543 133315622208889230085131815)
  ·
    refine ⟨199973433313333845127697723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133315622208889230085131815 199973433313333845127697723)
    ·
      refine ⟨299960149970000767691546585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199973433313333845127697723 299960149970000767691546585)
      ·
        refine ⟨224970112477500575768659939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299960149970000767691546585 224970112477500575768659939)
        ·
          refine ⟨337455168716250863652989909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224970112477500575768659939 337455168716250863652989909)
          ·
            refine ⟨7909105516787129616866951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 337455168716250863652989909 7909105516787129616866951)
            ·
              refine ⟨11863658275180694425300427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7909105516787129616866951 11863658275180694425300427)
              ·
                refine ⟨17795487412771041637950641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11863658275180694425300427 17795487412771041637950641)
                ·
                  refine ⟨13346615559578281228462981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17795487412771041637950641 13346615559578281228462981)
                  ·
                    refine ⟨2502490417420927730336809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13346615559578281228462981 2502490417420927730336809)
                    ·
                      refine ⟨1876867813065695797752607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502490417420927730336809 1876867813065695797752607)
                      ·
                        rfl

theorem cell23_3655187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 4, 2].length) (baseStart_3655187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655187 prefixEnd_3655187 := by exact prefixLift 3655187
  have htrace : WordTrace (prefixWord ++ tailWord_3655187) baseStart_3655187 baseEnd_3655187 := by
    simpa [prefixWord, tailWord_3655187, baseEnd_3655187] using wordTrace_append hprefix tailTrace_3655187
  have hstable : (prefixWord ++ tailWord_3655187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655187).length < 2 ^ (prefixWord ++ tailWord_3655187).sum := by decide
  have hdescent : baseEnd_3655187 < baseStart_3655187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655197 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_3655197 : Nat := 118140960795 + 3655197 * 2 ^ 59
def prefixEnd_3655197 : Nat := 4983230072969 + 3 ^ 40 * 3655197 * 2
def baseEnd_3655197 : Nat := 625624315957413586209187

theorem tailTrace_3655197 : CollatzResearch.WordTrace tailWord_3655197 prefixEnd_3655197 625624315957413586209187 := by
  unfold tailWord_3655197
  simp only [CollatzResearch.WordTrace]
  refine ⟨133315986938853001792995845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88877324625902001195330563 133315986938853001792995845)
  ·
    refine ⟨24996747551034937836186721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133315986938853001792995845 24996747551034937836186721)
    ·
      refine ⟨18747560663276203377140041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24996747551034937836186721 18747560663276203377140041)
      ·
        refine ⟨14060670497457152532855031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18747560663276203377140041 14060670497457152532855031)
        ·
          refine ⟨21091005746185728799282547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14060670497457152532855031 21091005746185728799282547)
          ·
            refine ⟨31636508619278593198923821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21091005746185728799282547 31636508619278593198923821)
            ·
              refine ⟨11863690732229472449596433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31636508619278593198923821 11863690732229472449596433)
              ·
                refine ⟨8897768049172104337197325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11863690732229472449596433 8897768049172104337197325)
                ·
                  refine ⟨3336663018439539126448997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8897768049172104337197325 3336663018439539126448997)
                  ·
                    refine ⟨625624315957413586209187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3336663018439539126448997 625624315957413586209187)
                    ·
                      rfl

theorem cell23_3655197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_3655197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655197 prefixEnd_3655197 := by exact prefixLift 3655197
  have htrace : WordTrace (prefixWord ++ tailWord_3655197) baseStart_3655197 baseEnd_3655197 := by
    simpa [prefixWord, tailWord_3655197, baseEnd_3655197] using wordTrace_append hprefix tailTrace_3655197
  have hstable : (prefixWord ++ tailWord_3655197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655197).length < 2 ^ (prefixWord ++ tailWord_3655197).sum := by decide
  have hdescent : baseEnd_3655197 < baseStart_3655197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655210 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 8]
def baseStart_3655210 : Nat := 118140960795 + 3655210 * 2 ^ 59
def prefixEnd_3655210 : Nat := 4983230072969 + 3 ^ 40 * 3655210 * 2
def baseEnd_3655210 : Nat := 208542180346749911973889

theorem tailTrace_3655210 : CollatzResearch.WordTrace tailWord_3655210 prefixEnd_3655210 208542180346749911973889 := by
  unfold tailWord_3655210
  simp only [CollatzResearch.WordTrace]
  refine ⟨33329115271951476253304771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88877640725203936675479389 33329115271951476253304771)
  ·
    refine ⟨49993672907927214379957157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33329115271951476253304771 49993672907927214379957157)
    ·
      refine ⟨9373813670236352696241967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49993672907927214379957157 9373813670236352696241967)
      ·
        refine ⟨14060720505354529044362951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9373813670236352696241967 14060720505354529044362951)
        ·
          refine ⟨21091080758031793566544427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14060720505354529044362951 21091080758031793566544427)
          ·
            refine ⟨31636621137047690349816641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21091080758031793566544427 31636621137047690349816641)
            ·
              refine ⟨23727465852785767762362481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31636621137047690349816641 23727465852785767762362481)
              ·
                refine ⟨17795599389589325821771861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23727465852785767762362481 17795599389589325821771861)
                ·
                  refine ⟨208542180346749911973889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17795599389589325821771861 208542180346749911973889)
                  ·
                    rfl

theorem cell23_3655210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_3655210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655210 prefixEnd_3655210 := by exact prefixLift 3655210
  have htrace : WordTrace (prefixWord ++ tailWord_3655210) baseStart_3655210 baseEnd_3655210 := by
    simpa [prefixWord, tailWord_3655210, baseEnd_3655210] using wordTrace_append hprefix tailTrace_3655210
  have hstable : (prefixWord ++ tailWord_3655210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655210).length < 2 ^ (prefixWord ++ tailWord_3655210).sum := by decide
  have hdescent : baseEnd_3655210 < baseStart_3655210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655271 : List Nat := [1, 1, 5, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_3655271 : Nat := 118140960795 + 3655271 * 2 ^ 59
def prefixEnd_3655271 : Nat := 4983230072969 + 3 ^ 40 * 3655271 * 2
def baseEnd_3655271 : Nat := 1876910945440673469102221

theorem tailTrace_3655271 : CollatzResearch.WordTrace tailWord_3655271 prefixEnd_3655271 1876910945440673469102221 := by
  unfold tailWord_3655271
  simp only [CollatzResearch.WordTrace]
  refine ⟨133318685940584912431189667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88879123960389941620793111 133318685940584912431189667)
  ·
    refine ⟨199978028910877368646784501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133318685940584912431189667 199978028910877368646784501)
    ·
      refine ⟨18747940210394753310636047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199978028910877368646784501 18747940210394753310636047)
      ·
        refine ⟨28121910315592129965954071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18747940210394753310636047 28121910315592129965954071)
        ·
          refine ⟨42182865473388194948931107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28121910315592129965954071 42182865473388194948931107)
          ·
            refine ⟨63274298210082292423396661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42182865473388194948931107 63274298210082292423396661)
            ·
              refine ⟨5931965457195214914693437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63274298210082292423396661 5931965457195214914693437)
              ·
                refine ⟨2224487046448205593010039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5931965457195214914693437 2224487046448205593010039)
                ·
                  refine ⟨3336730569672308389515059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224487046448205593010039 3336730569672308389515059)
                  ·
                    refine ⟨5005095854508462584272589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3336730569672308389515059 5005095854508462584272589)
                    ·
                      refine ⟨1876910945440673469102221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5005095854508462584272589 1876910945440673469102221)
                      ·
                        rfl

theorem cell23_3655271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_3655271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655271 prefixEnd_3655271 := by exact prefixLift 3655271
  have htrace : WordTrace (prefixWord ++ tailWord_3655271) baseStart_3655271 baseEnd_3655271 := by
    simpa [prefixWord, tailWord_3655271, baseEnd_3655271] using wordTrace_append hprefix tailTrace_3655271
  have hstable : (prefixWord ++ tailWord_3655271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655271).length < 2 ^ (prefixWord ++ tailWord_3655271).sum := by decide
  have hdescent : baseEnd_3655271 < baseStart_3655271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655287 : List Nat := [1, 1, 3, 1, 1, 3, 1, 6, 2, 4]
def baseStart_3655287 : Nat := 118140960795 + 3655287 * 2 ^ 59
def prefixEnd_3655287 : Nat := 4983230072969 + 3 ^ 40 * 3655287 * 2
def baseEnd_3655287 : Nat := 625639720377048468834049

theorem tailTrace_3655287 : CollatzResearch.WordTrace tailWord_3655287 prefixEnd_3655287 625639720377048468834049 := by
  unfold tailWord_3655287
  simp only [CollatzResearch.WordTrace]
  refine ⟨133319269508526947163772115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88879513005684631442514743 133319269508526947163772115)
  ·
    refine ⟨199978904262790420745658173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133319269508526947163772115 199978904262790420745658173)
    ·
      refine ⟨74992089098546407779621815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199978904262790420745658173 74992089098546407779621815)
      ·
        refine ⟨112488133647819611669432723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74992089098546407779621815 112488133647819611669432723)
        ·
          refine ⟨168732200471729417504149085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112488133647819611669432723 168732200471729417504149085)
          ·
            refine ⟨63274575176898531564055907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168732200471729417504149085 63274575176898531564055907)
            ·
              refine ⟨94911862765347797346083861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63274575176898531564055907 94911862765347797346083861)
              ·
                refine ⟨4448993567125678000597681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94911862765347797346083861 4448993567125678000597681)
                ·
                  refine ⟨3336745175344258500448261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4448993567125678000597681 3336745175344258500448261)
                  ·
                    refine ⟨625639720377048468834049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3336745175344258500448261 625639720377048468834049)
                    ·
                      rfl

theorem cell23_3655287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 6, 2, 4].length) (baseStart_3655287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655287 prefixEnd_3655287 := by exact prefixLift 3655287
  have htrace : WordTrace (prefixWord ++ tailWord_3655287) baseStart_3655287 baseEnd_3655287 := by
    simpa [prefixWord, tailWord_3655287, baseEnd_3655287] using wordTrace_append hprefix tailTrace_3655287
  have hstable : (prefixWord ++ tailWord_3655287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655287).length < 2 ^ (prefixWord ++ tailWord_3655287).sum := by decide
  have hdescent : baseEnd_3655287 < baseStart_3655287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655290 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4]
def baseStart_3655290 : Nat := 118140960795 + 3655290 * 2 ^ 59
def prefixEnd_3655290 : Nat := 4983230072969 + 3 ^ 40 * 3655290 * 2
def baseEnd_3655290 : Nat := 1876920701573108894764633

theorem tailTrace_3655290 : CollatzResearch.WordTrace tailWord_3655290 prefixEnd_3655290 1876920701573108894764633 := by
  unfold tailWord_3655290
  simp only [CollatzResearch.WordTrace]
  refine ⟨33329844731879019669032831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88879585951677385784087549 33329844731879019669032831)
  ·
    refine ⟨49994767097818529503549247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33329844731879019669032831 49994767097818529503549247)
    ·
      refine ⟨74992150646727794255323871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49994767097818529503549247 74992150646727794255323871)
      ·
        refine ⟨112488225970091691382985807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74992150646727794255323871 112488225970091691382985807)
        ·
          refine ⟨168732338955137537074478711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112488225970091691382985807 168732338955137537074478711)
          ·
            refine ⟨253098508432706305611718067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168732338955137537074478711 253098508432706305611718067)
            ·
              refine ⟨379647762649059458417577101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253098508432706305611718067 379647762649059458417577101)
              ·
                refine ⟨142367910993397296906591413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 379647762649059458417577101 142367910993397296906591413)
                ·
                  refine ⟨13346991655630996584992945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142367910993397296906591413 13346991655630996584992945)
                  ·
                    refine ⟨10010243741723247438744709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13346991655630996584992945 10010243741723247438744709)
                    ·
                      refine ⟨1876920701573108894764633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10010243741723247438744709 1876920701573108894764633)
                      ·
                        rfl

theorem cell23_3655290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_3655290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655290 prefixEnd_3655290 := by exact prefixLift 3655290
  have htrace : WordTrace (prefixWord ++ tailWord_3655290) baseStart_3655290 baseEnd_3655290 := by
    simpa [prefixWord, tailWord_3655290, baseEnd_3655290] using wordTrace_append hprefix tailTrace_3655290
  have hstable : (prefixWord ++ tailWord_3655290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655290).length < 2 ^ (prefixWord ++ tailWord_3655290).sum := by decide
  have hdescent : baseEnd_3655290 < baseStart_3655290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655297 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3655297 : Nat := 118140960795 + 3655297 * 2 ^ 59
def prefixEnd_3655297 : Nat := 4983230072969 + 3 ^ 40 * 3655297 * 2
def baseEnd_3655297 : Nat := 1876924295937690367377101

theorem tailTrace_3655297 : CollatzResearch.WordTrace tailWord_3655297 prefixEnd_3655297 1876924295937690367377101 := by
  unfold tailWord_3655297
  simp only [CollatzResearch.WordTrace]
  refine ⟨133319634238490718871636145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88879756158993812581090763 133319634238490718871636145)
  ·
    refine ⟨99989725678868039153727109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133319634238490718871636145 99989725678868039153727109)
    ·
      refine ⟨18748073564787757341323833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99989725678868039153727109 18748073564787757341323833)
      ·
        refine ⟨14061055173590818005992875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18748073564787757341323833 14061055173590818005992875)
        ·
          refine ⟨21091582760386227008989313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14061055173590818005992875 21091582760386227008989313)
          ·
            refine ⟨15818687070289670256741985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21091582760386227008989313 15818687070289670256741985)
            ·
              refine ⟨11864015302717252692556489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15818687070289670256741985 11864015302717252692556489)
              ·
                refine ⟨8898011477037939519417367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11864015302717252692556489 8898011477037939519417367)
                ·
                  refine ⟨13347017215556909279126051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8898011477037939519417367 13347017215556909279126051)
                  ·
                    refine ⟨20020525823335363918689077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13347017215556909279126051 20020525823335363918689077)
                    ·
                      refine ⟨1876924295937690367377101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20020525823335363918689077 1876924295937690367377101)
                      ·
                        rfl

theorem cell23_3655297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3655297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655297 prefixEnd_3655297 := by exact prefixLift 3655297
  have htrace : WordTrace (prefixWord ++ tailWord_3655297) baseStart_3655297 baseEnd_3655297 := by
    simpa [prefixWord, tailWord_3655297, baseEnd_3655297] using wordTrace_append hprefix tailTrace_3655297
  have hstable : (prefixWord ++ tailWord_3655297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655297).length < 2 ^ (prefixWord ++ tailWord_3655297).sum := by decide
  have hdescent : baseEnd_3655297 < baseStart_3655297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655324 : List Nat := [2, 2, 3, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_3655324 : Nat := 118140960795 + 3655324 * 2 ^ 59
def prefixEnd_3655324 : Nat := 4983230072969 + 3 ^ 40 * 3655324 * 2
def baseEnd_3655324 : Nat := 1876938159915361761739477

theorem tailTrace_3655324 : CollatzResearch.WordTrace tailWord_3655324 prefixEnd_3655324 1876938159915361761739477 := by
  unfold tailWord_3655324
  simp only [CollatzResearch.WordTrace]
  refine ⟨66660309504696451241434513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88880412672928601655246017 66660309504696451241434513)
  ·
    refine ⟨49995232128522338431075885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66660309504696451241434513 49995232128522338431075885)
    ·
      refine ⟨18748212048195876911653457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49995232128522338431075885 18748212048195876911653457)
      ·
        refine ⟨14061159036146907683740093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18748212048195876911653457 14061159036146907683740093)
        ·
          refine ⟨5272934638555090381402535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14061159036146907683740093 5272934638555090381402535)
          ·
            refine ⟨7909401957832635572103803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272934638555090381402535 7909401957832635572103803)
            ·
              refine ⟨11864102936748953358155705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7909401957832635572103803 11864102936748953358155705)
              ·
                refine ⟨8898077202561715018616779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11864102936748953358155705 8898077202561715018616779)
                ·
                  refine ⟨13347115803842572527925169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8898077202561715018616779 13347115803842572527925169)
                  ·
                    refine ⟨10010336852881929395943877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13347115803842572527925169 10010336852881929395943877)
                    ·
                      refine ⟨1876938159915361761739477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10010336852881929395943877 1876938159915361761739477)
                      ·
                        rfl

theorem cell23_3655324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_3655324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655324 prefixEnd_3655324 := by exact prefixLift 3655324
  have htrace : WordTrace (prefixWord ++ tailWord_3655324) baseStart_3655324 baseEnd_3655324 := by
    simpa [prefixWord, tailWord_3655324, baseEnd_3655324] using wordTrace_append hprefix tailTrace_3655324
  have hstable : (prefixWord ++ tailWord_3655324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655324).length < 2 ^ (prefixWord ++ tailWord_3655324).sum := by decide
  have hdescent : baseEnd_3655324 < baseStart_3655324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655344 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 2, 1, 3]
def baseStart_3655344 : Nat := 118140960795 + 3655344 * 2 ^ 59
def prefixEnd_3655344 : Nat := 4983230072969 + 3 ^ 40 * 3655344 * 2
def baseEnd_3655344 : Nat := 1876948429528451683489385

theorem tailTrace_3655344 : CollatzResearch.WordTrace tailWord_3655344 prefixEnd_3655344 1876948429528451683489385 := by
  unfold tailWord_3655344
  simp only [CollatzResearch.WordTrace]
  refine ⟨66660674234660222949298543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88880898979546963932398057 66660674234660222949298543)
  ·
    refine ⟨99991011351990334423947815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66660674234660222949298543 99991011351990334423947815)
    ·
      refine ⟨149986517027985501635921723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99991011351990334423947815 149986517027985501635921723)
      ·
        refine ⟨224979775541978252453882585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149986517027985501635921723 224979775541978252453882585)
        ·
          refine ⟨168734831656483689340411939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224979775541978252453882585 168734831656483689340411939)
          ·
            refine ⟨253102247484725534010617909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168734831656483689340411939 253102247484725534010617909)
            ·
              refine ⟨23728335701693018813495429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253102247484725534010617909 23728335701693018813495429)
              ·
                refine ⟨4449062944067441027530393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23728335701693018813495429 4449062944067441027530393)
                ·
                  refine ⟨3336797208050580770647795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4449062944067441027530393 3336797208050580770647795)
                  ·
                    refine ⟨5005195812075871155971693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3336797208050580770647795 5005195812075871155971693)
                    ·
                      refine ⟨1876948429528451683489385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5005195812075871155971693 1876948429528451683489385)
                      ·
                        rfl

theorem cell23_3655344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2, 1, 3].length) (baseStart_3655344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655344 prefixEnd_3655344 := by exact prefixLift 3655344
  have htrace : WordTrace (prefixWord ++ tailWord_3655344) baseStart_3655344 baseEnd_3655344 := by
    simpa [prefixWord, tailWord_3655344, baseEnd_3655344] using wordTrace_append hprefix tailTrace_3655344
  have hstable : (prefixWord ++ tailWord_3655344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655344).length < 2 ^ (prefixWord ++ tailWord_3655344).sum := by decide
  have hdescent : baseEnd_3655344 < baseStart_3655344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655354 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2]
def baseStart_3655354 : Nat := 118140960795 + 3655354 * 2 ^ 59
def prefixEnd_3655354 : Nat := 4983230072969 + 3 ^ 40 * 3655354 * 2
def baseEnd_3655354 : Nat := 1876953564334996644364339

theorem tailTrace_3655354 : CollatzResearch.WordTrace tailWord_3655354 prefixEnd_3655354 1876953564334996644364339 := by
  unfold tailWord_3655354
  simp only [CollatzResearch.WordTrace]
  refine ⟨33330428299821054401615279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88881142132856145070974077 33330428299821054401615279)
  ·
    refine ⟨49995642449731581602422919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33330428299821054401615279 49995642449731581602422919)
    ·
      refine ⟨74993463674597372403634379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49995642449731581602422919 74993463674597372403634379)
      ·
        refine ⟨112490195511896058605451569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74993463674597372403634379 112490195511896058605451569)
        ·
          refine ⟨84367646633922043954088677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112490195511896058605451569 84367646633922043954088677)
          ·
            refine ⟨15818933743860383241391627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84367646633922043954088677 15818933743860383241391627)
            ·
              refine ⟨23728400615790574862087441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15818933743860383241391627 23728400615790574862087441)
              ·
                refine ⟨17796300461842931146565581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23728400615790574862087441 17796300461842931146565581)
                ·
                  refine ⟨6673612673191099179962093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17796300461842931146565581 6673612673191099179962093)
                  ·
                    refine ⟨2502604752446662192485785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6673612673191099179962093 2502604752446662192485785)
                    ·
                      refine ⟨1876953564334996644364339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502604752446662192485785 1876953564334996644364339)
                      ·
                        rfl

theorem cell23_3655354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2].length) (baseStart_3655354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655354 prefixEnd_3655354 := by exact prefixLift 3655354
  have htrace : WordTrace (prefixWord ++ tailWord_3655354) baseStart_3655354 baseEnd_3655354 := by
    simpa [prefixWord, tailWord_3655354, baseEnd_3655354] using wordTrace_append hprefix tailTrace_3655354
  have hstable : (prefixWord ++ tailWord_3655354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655354).length < 2 ^ (prefixWord ++ tailWord_3655354).sum := by decide
  have hdescent : baseEnd_3655354 < baseStart_3655354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655362 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_3655362 : Nat := 118140960795 + 3655362 * 2 ^ 59
def prefixEnd_3655362 : Nat := 4983230072969 + 3 ^ 40 * 3655362 * 2
def baseEnd_3655362 : Nat := 1876957672180232613064303

theorem tailTrace_3655362 : CollatzResearch.WordTrace tailWord_3655362 prefixEnd_3655362 1876957672180232613064303 := by
  unfold tailWord_3655362
  simp only [CollatzResearch.WordTrace]
  refine ⟨33330501245813808743188085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88881336655503489981834893 33330501245813808743188085)
  ·
    refine ⟨3124734491795044569673883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33330501245813808743188085 3124734491795044569673883)
    ·
      refine ⟨4687101737692566854510825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3124734491795044569673883 4687101737692566854510825)
      ·
        refine ⟨3515326303269425140883119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4687101737692566854510825 3515326303269425140883119)
        ·
          refine ⟨5272989454904137711324679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3515326303269425140883119 5272989454904137711324679)
          ·
            refine ⟨7909484182356206566987019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5272989454904137711324679 7909484182356206566987019)
            ·
              refine ⟨11864226273534309850480529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7909484182356206566987019 11864226273534309850480529)
              ·
                refine ⟨8898169705150732387860397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11864226273534309850480529 8898169705150732387860397)
                ·
                  refine ⟨3336813639431524645447649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8898169705150732387860397 3336813639431524645447649)
                  ·
                    refine ⟨2502610229573643484085737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3336813639431524645447649 2502610229573643484085737)
                    ·
                      refine ⟨1876957672180232613064303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502610229573643484085737 1876957672180232613064303)
                      ·
                        rfl

theorem cell23_3655362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_3655362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655362 prefixEnd_3655362 := by exact prefixLift 3655362
  have htrace : WordTrace (prefixWord ++ tailWord_3655362) baseStart_3655362 baseEnd_3655362 := by
    simpa [prefixWord, tailWord_3655362, baseEnd_3655362] using wordTrace_append hprefix tailTrace_3655362
  have hstable : (prefixWord ++ tailWord_3655362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655362).length < 2 ^ (prefixWord ++ tailWord_3655362).sum := by decide
  have hdescent : baseEnd_3655362 < baseStart_3655362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655382 : List Nat := [5, 2, 1, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_3655382 : Nat := 118140960795 + 3655382 * 2 ^ 59
def prefixEnd_3655382 : Nat := 4983230072969 + 3 ^ 40 * 3655382 * 2
def baseEnd_3655382 : Nat := 1876967941793322534814211

theorem tailTrace_3655382 : CollatzResearch.WordTrace tailWord_3655382 prefixEnd_3655382 1876967941793322534814211 := by
  unfold tailWord_3655382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8332670902698923649280025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88881822962121852258986933 8332670902698923649280025)
  ·
    refine ⟨6249503177024192736960019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8332670902698923649280025 6249503177024192736960019)
    ·
      refine ⟨9374254765536289105440029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6249503177024192736960019 9374254765536289105440029)
      ·
        refine ⟨3515345537076108414540011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9374254765536289105440029 3515345537076108414540011)
        ·
          refine ⟨5273018305614162621810017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3515345537076108414540011 5273018305614162621810017)
          ·
            refine ⟨3954763729210621966357513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5273018305614162621810017 3954763729210621966357513)
            ·
              refine ⟨2966072796907966474768135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3954763729210621966357513 2966072796907966474768135)
              ·
                refine ⟨4449109195361949712152203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966072796907966474768135 4449109195361949712152203)
                ·
                  refine ⟨6673663793042924568228305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4449109195361949712152203 6673663793042924568228305)
                  ·
                    refine ⟨5005247844782193426171229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6673663793042924568228305 5005247844782193426171229)
                    ·
                      refine ⟨1876967941793322534814211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5005247844782193426171229 1876967941793322534814211)
                      ·
                        rfl

theorem cell23_3655382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_3655382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655382 prefixEnd_3655382 := by exact prefixLift 3655382
  have htrace : WordTrace (prefixWord ++ tailWord_3655382) baseStart_3655382 baseEnd_3655382 := by
    simpa [prefixWord, tailWord_3655382, baseEnd_3655382] using wordTrace_append hprefix tailTrace_3655382
  have hstable : (prefixWord ++ tailWord_3655382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655382).length < 2 ^ (prefixWord ++ tailWord_3655382).sum := by decide
  have hdescent : baseEnd_3655382 < baseStart_3655382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655384 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 1, 4, 2]
def baseStart_3655384 : Nat := 118140960795 + 3655384 * 2 ^ 59
def prefixEnd_3655384 : Nat := 4983230072969 + 3 ^ 40 * 3655384 * 2
def baseEnd_3655384 : Nat := 1876968968754631526989201

theorem tailTrace_3655384 : CollatzResearch.WordTrace tailWord_3655384 prefixEnd_3655384 1876968968754631526989201 := by
  unfold tailWord_3655384
  simp only [CollatzResearch.WordTrace]
  refine ⟨66661403694587766365026603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88881871592783688486702137 66661403694587766365026603)
  ·
    refine ⟨99992105541881649547539905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66661403694587766365026603 99992105541881649547539905)
    ·
      refine ⟨74994079156411237160654929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99992105541881649547539905 74994079156411237160654929)
      ·
        refine ⟨56245559367308427870491197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74994079156411237160654929 56245559367308427870491197)
        ·
          refine ⟨21092084762740660451434199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56245559367308427870491197 21092084762740660451434199)
          ·
            refine ⟨31638127144110990677151299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21092084762740660451434199 31638127144110990677151299)
            ·
              refine ⟨47457190716166486015726949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31638127144110990677151299 47457190716166486015726949)
              ·
                refine ⟨8898223259281216127948803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47457190716166486015726949 8898223259281216127948803)
                ·
                  refine ⟨13347334888921824191923205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8898223259281216127948803 13347334888921824191923205)
                  ·
                    refine ⟨2502625291672842035985601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13347334888921824191923205 2502625291672842035985601)
                    ·
                      refine ⟨1876968968754631526989201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502625291672842035985601 1876968968754631526989201)
                      ·
                        rfl

theorem cell23_3655384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_3655384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655384 prefixEnd_3655384 := by exact prefixLift 3655384
  have htrace : WordTrace (prefixWord ++ tailWord_3655384) baseStart_3655384 baseEnd_3655384 := by
    simpa [prefixWord, tailWord_3655384, baseEnd_3655384] using wordTrace_append hprefix tailTrace_3655384
  have hstable : (prefixWord ++ tailWord_3655384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655384).length < 2 ^ (prefixWord ++ tailWord_3655384).sum := by decide
  have hdescent : baseEnd_3655384 < baseStart_3655384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655395 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 2, 1, 3]
def baseStart_3655395 : Nat := 118140960795 + 3655395 * 2 ^ 59
def prefixEnd_3655395 : Nat := 4983230072969 + 3 ^ 40 * 3655395 * 2
def baseEnd_3655395 : Nat := 1876974617041830983951651

theorem tailTrace_3655395 : CollatzResearch.WordTrace tailWord_3655395 prefixEnd_3655395 1876974617041830983951651 := by
  unfold tailWord_3655395
  simp only [CollatzResearch.WordTrace]
  refine ⟨133323208592135681608703639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88882139061423787739135759 133323208592135681608703639)
  ·
    refine ⟨199984812888203522413055459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133323208592135681608703639 199984812888203522413055459)
    ·
      refine ⟨299977219332305283619583189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199984812888203522413055459 299977219332305283619583189)
      ·
        refine ⟨7030716078100905084833981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 299977219332305283619583189 7030716078100905084833981)
        ·
          refine ⟨2636518529287839406812743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7030716078100905084833981 2636518529287839406812743)
          ·
            refine ⟨3954777793931759110219115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636518529287839406812743 3954777793931759110219115)
            ·
              refine ⟨5932166690897638665328673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954777793931759110219115 5932166690897638665328673)
              ·
                refine ⟨4449125018173228998996505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5932166690897638665328673 4449125018173228998996505)
                ·
                  refine ⟨3336843763629921749247379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4449125018173228998996505 3336843763629921749247379)
                  ·
                    refine ⟨5005265645444882623871069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3336843763629921749247379 5005265645444882623871069)
                    ·
                      refine ⟨1876974617041830983951651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5005265645444882623871069 1876974617041830983951651)
                      ·
                        rfl

theorem cell23_3655395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_3655395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655395 prefixEnd_3655395 := by exact prefixLift 3655395
  have htrace : WordTrace (prefixWord ++ tailWord_3655395) baseStart_3655395 baseEnd_3655395 := by
    simpa [prefixWord, tailWord_3655395, baseEnd_3655395] using wordTrace_append hprefix tailTrace_3655395
  have hstable : (prefixWord ++ tailWord_3655395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655395).length < 2 ^ (prefixWord ++ tailWord_3655395).sum := by decide
  have hdescent : baseEnd_3655395 < baseStart_3655395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655397 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3655397 : Nat := 118140960795 + 3655397 * 2 ^ 59
def prefixEnd_3655397 : Nat := 4983230072969 + 3 ^ 40 * 3655397 * 2
def baseEnd_3655397 : Nat := 1876975644003139976126641

theorem tailTrace_3655397 : CollatzResearch.WordTrace tailWord_3655397 prefixEnd_3655397 1876975644003139976126641 := by
  unfold tailWord_3655397
  simp only [CollatzResearch.WordTrace]
  refine ⟨133323281538128435950276445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88882187692085623966850963 133323281538128435950276445)
  ·
    refine ⟨49996230576798163481353667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133323281538128435950276445 49996230576798163481353667)
    ·
      refine ⟨74994345865197245222030501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49996230576798163481353667 74994345865197245222030501)
      ·
        refine ⟨14061439849724483479130719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74994345865197245222030501 14061439849724483479130719)
        ·
          refine ⟨21092159774586725218696079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14061439849724483479130719 21092159774586725218696079)
          ·
            refine ⟨31638239661880087828044119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21092159774586725218696079 31638239661880087828044119)
            ·
              refine ⟨47457359492820131742066179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31638239661880087828044119 47457359492820131742066179)
              ·
                refine ⟨71186039239230197613099269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47457359492820131742066179 71186039239230197613099269)
                ·
                  refine ⟨13347382357355662052456113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71186039239230197613099269 13347382357355662052456113)
                  ·
                    refine ⟨10010536768016746539342085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13347382357355662052456113 10010536768016746539342085)
                    ·
                      refine ⟨1876975644003139976126641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10010536768016746539342085 1876975644003139976126641)
                      ·
                        rfl

theorem cell23_3655397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3655397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655397 prefixEnd_3655397 := by exact prefixLift 3655397
  have htrace : WordTrace (prefixWord ++ tailWord_3655397) baseStart_3655397 baseEnd_3655397 := by
    simpa [prefixWord, tailWord_3655397, baseEnd_3655397] using wordTrace_append hprefix tailTrace_3655397
  have hstable : (prefixWord ++ tailWord_3655397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655397).length < 2 ^ (prefixWord ++ tailWord_3655397).sum := by decide
  have hdescent : baseEnd_3655397 < baseStart_3655397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655407 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 7]
def baseStart_3655407 : Nat := 118140960795 + 3655407 * 2 ^ 59
def prefixEnd_3655407 : Nat := 4983230072969 + 3 ^ 40 * 3655407 * 2
def baseEnd_3655407 : Nat := 208553419867742770777955

theorem tailTrace_3655407 : CollatzResearch.WordTrace tailWord_3655407 prefixEnd_3655407 208553419867742770777955 := by
  unfold tailWord_3655407
  simp only [CollatzResearch.WordTrace]
  refine ⟨133323646268092207658140475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88882430845394805105426983 133323646268092207658140475)
  ·
    refine ⟨199985469402138311487210713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133323646268092207658140475 199985469402138311487210713)
    ·
      refine ⟨149989102051603733615408035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199985469402138311487210713 149989102051603733615408035)
      ·
        refine ⟨224983653077405600423112053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149989102051603733615408035 224983653077405600423112053)
        ·
          refine ⟨21092217476006775039666755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224983653077405600423112053 21092217476006775039666755)
          ·
            refine ⟨31638326214010162559500133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21092217476006775039666755 31638326214010162559500133)
            ·
              refine ⟨5932186165126905479906275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31638326214010162559500133 5932186165126905479906275)
              ·
                refine ⟨8898279247690358219859413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932186165126905479906275 8898279247690358219859413)
                ·
                  refine ⟨208553419867742770777955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8898279247690358219859413 208553419867742770777955)
                  ·
                    rfl

theorem cell23_3655407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 7].length) (baseStart_3655407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655407 prefixEnd_3655407 := by exact prefixLift 3655407
  have htrace : WordTrace (prefixWord ++ tailWord_3655407) baseStart_3655407 baseEnd_3655407 := by
    simpa [prefixWord, tailWord_3655407, baseEnd_3655407] using wordTrace_append hprefix tailTrace_3655407
  have hstable : (prefixWord ++ tailWord_3655407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655407).length < 2 ^ (prefixWord ++ tailWord_3655407).sum := by decide
  have hdescent : baseEnd_3655407 < baseStart_3655407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655412 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_3655412 : Nat := 118140960795 + 3655412 * 2 ^ 59
def prefixEnd_3655412 : Nat := 4983230072969 + 3 ^ 40 * 3655412 * 2
def baseEnd_3655412 : Nat := 1876983346212957417439073

theorem tailTrace_3655412 : CollatzResearch.WordTrace tailWord_3655412 prefixEnd_3655412 1876983346212957417439073 := by
  unfold tailWord_3655412
  simp only [CollatzResearch.WordTrace]
  refine ⟨66661914316537046756036245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88882552422049395674714993 66661914316537046756036245)
  ·
    refine ⟨3124777233587674066689199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66661914316537046756036245 3124777233587674066689199)
    ·
      refine ⟨4687165850381511100033799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3124777233587674066689199 4687165850381511100033799)
      ·
        refine ⟨7030748775572266650050699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4687165850381511100033799 7030748775572266650050699)
        ·
          refine ⟨10546123163358399975076049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7030748775572266650050699 10546123163358399975076049)
          ·
            refine ⟨7909592372518799981307037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10546123163358399975076049 7909592372518799981307037)
            ·
              refine ⟨2966097139694549992990139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7909592372518799981307037 2966097139694549992990139)
              ·
                refine ⟨4449145709541824989485209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966097139694549992990139 4449145709541824989485209)
                ·
                  refine ⟨3336859282156368742113907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4449145709541824989485209 3336859282156368742113907)
                  ·
                    refine ⟨5005288923234553113170861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3336859282156368742113907 5005288923234553113170861)
                    ·
                      refine ⟨1876983346212957417439073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5005288923234553113170861 1876983346212957417439073)
                      ·
                        rfl

theorem cell23_3655412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_3655412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655412 prefixEnd_3655412 := by exact prefixLift 3655412
  have htrace : WordTrace (prefixWord ++ tailWord_3655412) baseStart_3655412 baseEnd_3655412 := by
    simpa [prefixWord, tailWord_3655412, baseEnd_3655412] using wordTrace_append hprefix tailTrace_3655412
  have hstable : (prefixWord ++ tailWord_3655412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655412).length < 2 ^ (prefixWord ++ tailWord_3655412).sum := by decide
  have hdescent : baseEnd_3655412 < baseStart_3655412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655414 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3655414 : Nat := 118140960795 + 3655414 * 2 ^ 59
def prefixEnd_3655414 : Nat := 4983230072969 + 3 ^ 40 * 3655414 * 2
def baseEnd_3655414 : Nat := 1876984373174266409614063

theorem tailTrace_3655414 : CollatzResearch.WordTrace tailWord_3655414 prefixEnd_3655414 1876984373174266409614063 := by
  unfold tailWord_3655414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8332743848691677990852831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88882601052711231902430197 8332743848691677990852831)
  ·
    refine ⟨12499115773037516986279247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8332743848691677990852831 12499115773037516986279247)
    ·
      refine ⟨18748673659556275479418871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12499115773037516986279247 18748673659556275479418871)
      ·
        refine ⟨28123010489334413219128307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18748673659556275479418871 28123010489334413219128307)
        ·
          refine ⟨42184515734001619828692461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28123010489334413219128307 42184515734001619828692461)
          ·
            refine ⟨15819193400250607435759673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42184515734001619828692461 15819193400250607435759673)
            ·
              refine ⟨11864395050187955576819755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15819193400250607435759673 11864395050187955576819755)
              ·
                refine ⟨17796592575281933365229633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11864395050187955576819755 17796592575281933365229633)
                ·
                  refine ⟨13347444431461450023922225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17796592575281933365229633 13347444431461450023922225)
                  ·
                    refine ⟨10010583323596087517941669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13347444431461450023922225 10010583323596087517941669)
                    ·
                      refine ⟨1876984373174266409614063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10010583323596087517941669 1876984373174266409614063)
                      ·
                        rfl

theorem cell23_3655414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3655414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655414 prefixEnd_3655414 := by exact prefixLift 3655414
  have htrace : WordTrace (prefixWord ++ tailWord_3655414) baseStart_3655414 baseEnd_3655414 := by
    simpa [prefixWord, tailWord_3655414, baseEnd_3655414] using wordTrace_append hprefix tailTrace_3655414
  have hstable : (prefixWord ++ tailWord_3655414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655414).length < 2 ^ (prefixWord ++ tailWord_3655414).sum := by decide
  have hdescent : baseEnd_3655414 < baseStart_3655414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655430 : List Nat := [6, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3655430 : Nat := 118140960795 + 3655430 * 2 ^ 59
def prefixEnd_3655430 : Nat := 4983230072969 + 3 ^ 40 * 3655430 * 2
def baseEnd_3655430 : Nat := 1876992588864738347013991

theorem tailTrace_3655430 : CollatzResearch.WordTrace tailWord_3655430 prefixEnd_3655430 1876992588864738347013991 := by
  unfold tailWord_3655430
  simp only [CollatzResearch.WordTrace]
  refine ⟨4166390160844027580819617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88882990098005921724151829 4166390160844027580819617)
  ·
    refine ⟨3124792620633020685614713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4166390160844027580819617 3124792620633020685614713)
    ·
      refine ⟨2343594465474765514211035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3124792620633020685614713 2343594465474765514211035)
      ·
        refine ⟨3515391698212148271316553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343594465474765514211035 3515391698212148271316553)
        ·
          refine ⟨2636543773659111203487415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3515391698212148271316553 2636543773659111203487415)
          ·
            refine ⟨3954815660488666805231123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636543773659111203487415 3954815660488666805231123)
            ·
              refine ⟨5932223490733000207846685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3954815660488666805231123 5932223490733000207846685)
              ·
                refine ⟨2224583809024875077942507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5932223490733000207846685 2224583809024875077942507)
                ·
                  refine ⟨3336875713537312616913761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224583809024875077942507 3336875713537312616913761)
                  ·
                    refine ⟨2502656785152984462685321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3336875713537312616913761 2502656785152984462685321)
                    ·
                      refine ⟨1876992588864738347013991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502656785152984462685321 1876992588864738347013991)
                      ·
                        rfl

theorem cell23_3655430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3655430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655430 prefixEnd_3655430 := by exact prefixLift 3655430
  have htrace : WordTrace (prefixWord ++ tailWord_3655430) baseStart_3655430 baseEnd_3655430 := by
    simpa [prefixWord, tailWord_3655430, baseEnd_3655430] using wordTrace_append hprefix tailTrace_3655430
  have hstable : (prefixWord ++ tailWord_3655430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655430).length < 2 ^ (prefixWord ++ tailWord_3655430).sum := by decide
  have hdescent : baseEnd_3655430 < baseStart_3655430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655464 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3655464 : Nat := 118140960795 + 3655464 * 2 ^ 59
def prefixEnd_3655464 : Nat := 4983230072969 + 3 ^ 40 * 3655464 * 2
def baseEnd_3655464 : Nat := 1877010047206991213988833

theorem tailTrace_3655464 : CollatzResearch.WordTrace tailWord_3655464 prefixEnd_3655464 1877010047206991213988833 := by
  unfold tailWord_3655464
  simp only [CollatzResearch.WordTrace]
  refine ⟨66662862614442853196482723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88883816819257137595310297 66662862614442853196482723)
  ·
    refine ⟨99994293921664279794724085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66662862614442853196482723 99994293921664279794724085)
    ·
      refine ⟨9374465055156026230755383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99994293921664279794724085 9374465055156026230755383)
      ·
        refine ⟨14061697582734039346133075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9374465055156026230755383 14061697582734039346133075)
        ·
          refine ⟨21092546374101059019199613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14061697582734039346133075 21092546374101059019199613)
          ·
            refine ⟨7909704890287897132199855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21092546374101059019199613 7909704890287897132199855)
            ·
              refine ⟨11864557335431845698299783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7909704890287897132199855 11864557335431845698299783)
              ·
                refine ⟨17796836003147768547449675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11864557335431845698299783 17796836003147768547449675)
                ·
                  refine ⟨26695254004721652821174513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17796836003147768547449675 26695254004721652821174513)
                  ·
                    refine ⟨20021440503541239615880885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26695254004721652821174513 20021440503541239615880885)
                    ·
                      refine ⟨1877010047206991213988833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20021440503541239615880885 1877010047206991213988833)
                      ·
                        rfl

theorem cell23_3655464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3655464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655464 prefixEnd_3655464 := by exact prefixLift 3655464
  have htrace : WordTrace (prefixWord ++ tailWord_3655464) baseStart_3655464 baseEnd_3655464 := by
    simpa [prefixWord, tailWord_3655464, baseEnd_3655464] using wordTrace_append hprefix tailTrace_3655464
  have hstable : (prefixWord ++ tailWord_3655464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655464).length < 2 ^ (prefixWord ++ tailWord_3655464).sum := by decide
  have hdescent : baseEnd_3655464 < baseStart_3655464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655484 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 3, 4]
def baseStart_3655484 : Nat := 118140960795 + 3655484 * 2 ^ 59
def prefixEnd_3655484 : Nat := 4983230072969 + 3 ^ 40 * 3655484 * 2
def baseEnd_3655484 : Nat := 625673438940027045246247

theorem tailTrace_3655484 : CollatzResearch.WordTrace tailWord_3655484 prefixEnd_3655484 625673438940027045246247 := by
  unfold tailWord_3655484
  simp only [CollatzResearch.WordTrace]
  refine ⟨66663227344406624904346753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88884303125875499872462337 66663227344406624904346753)
  ·
    refine ⟨49997420508304968678260065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66663227344406624904346753 49997420508304968678260065)
    ·
      refine ⟨37498065381228726508695049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49997420508304968678260065 37498065381228726508695049)
      ·
        refine ⟨28123549035921544881521287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37498065381228726508695049 28123549035921544881521287)
        ·
          refine ⟨42185323553882317322281931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28123549035921544881521287 42185323553882317322281931)
          ·
            refine ⟨63277985330823475983422897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42185323553882317322281931 63277985330823475983422897)
            ·
              refine ⟨47458488998117606987567173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63277985330823475983422897 47458488998117606987567173)
              ·
                refine ⟨8898466687147051310168845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47458488998117606987567173 8898466687147051310168845)
                ·
                  refine ⟨3336925007680144241313317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8898466687147051310168845 3336925007680144241313317)
                  ·
                    refine ⟨625673438940027045246247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3336925007680144241313317 625673438940027045246247)
                    ·
                      rfl

theorem cell23_3655484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_3655484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655484 prefixEnd_3655484 := by exact prefixLift 3655484
  have htrace : WordTrace (prefixWord ++ tailWord_3655484) baseStart_3655484 baseEnd_3655484 := by
    simpa [prefixWord, tailWord_3655484, baseEnd_3655484] using wordTrace_append hprefix tailTrace_3655484
  have hstable : (prefixWord ++ tailWord_3655484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655484).length < 2 ^ (prefixWord ++ tailWord_3655484).sum := by decide
  have hdescent : baseEnd_3655484 < baseStart_3655484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655514 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 6]
def baseStart_3655514 : Nat := 118140960795 + 3655514 * 2 ^ 59
def prefixEnd_3655514 : Nat := 4983230072969 + 3 ^ 40 * 3655514 * 2
def baseEnd_3655514 : Nat := 208559524582190668707067

theorem tailTrace_3655514 : CollatzResearch.WordTrace tailWord_3655514 prefixEnd_3655514 208559524582190668707067 := by
  unfold tailWord_3655514
  simp only [CollatzResearch.WordTrace]
  refine ⟨33331887219676141233071399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88885032585803043288190397 33331887219676141233071399)
  ·
    refine ⟨49997830829514211849607099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33331887219676141233071399 49997830829514211849607099)
    ·
      refine ⟨74996746244271317774410649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49997830829514211849607099 74996746244271317774410649)
      ·
        refine ⟨56247559683203488330807987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74996746244271317774410649 56247559683203488330807987)
        ·
          refine ⟨84371339524805232496211981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56247559683203488330807987 84371339524805232496211981)
          ·
            refine ⟨31639252321801962186079493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84371339524805232496211981 31639252321801962186079493)
            ·
              refine ⟨5932359810337867909889905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31639252321801962186079493 5932359810337867909889905)
              ·
                refine ⟨4449269857753400932417429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5932359810337867909889905 4449269857753400932417429)
                ·
                  refine ⟨208559524582190668707067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4449269857753400932417429 208559524582190668707067)
                  ·
                    rfl

theorem cell23_3655514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_3655514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655514 prefixEnd_3655514 := by exact prefixLift 3655514
  have htrace : WordTrace (prefixWord ++ tailWord_3655514) baseStart_3655514 baseEnd_3655514 := by
    simpa [prefixWord, tailWord_3655514, baseEnd_3655514] using wordTrace_append hprefix tailTrace_3655514
  have hstable : (prefixWord ++ tailWord_3655514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655514).length < 2 ^ (prefixWord ++ tailWord_3655514).sum := by decide
  have hdescent : baseEnd_3655514 < baseStart_3655514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655537 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_3655537 : Nat := 118140960795 + 3655537 * 2 ^ 59
def prefixEnd_3655537 : Nat := 4983230072969 + 3 ^ 40 * 3655537 * 2
def baseEnd_3655537 : Nat := 1877047531294769428375997

theorem tailTrace_3655537 : CollatzResearch.WordTrace tailWord_3655537 prefixEnd_3655537 1877047531294769428375997 := by
  unfold tailWord_3655537
  simp only [CollatzResearch.WordTrace]
  refine ⟨133328387757621239860372865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88885591838414159906915243 133328387757621239860372865)
  ·
    refine ⟨99996290818215929895279649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133328387757621239860372865 99996290818215929895279649)
    ·
      refine ⟨74997218113661947421459737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99996290818215929895279649 74997218113661947421459737)
      ·
        refine ⟨56247913585246460566094803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74997218113661947421459737 56247913585246460566094803)
        ·
          refine ⟨84371870377869690849142205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56247913585246460566094803 84371870377869690849142205)
          ·
            refine ⟨31639451391701134068428327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84371870377869690849142205 31639451391701134068428327)
            ·
              refine ⟨47459177087551701102642491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31639451391701134068428327 47459177087551701102642491)
              ·
                refine ⟨71188765631327551653963737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47459177087551701102642491 71188765631327551653963737)
                ·
                  refine ⟨53391574223495663740472803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71188765631327551653963737 53391574223495663740472803)
                  ·
                    refine ⟨80087361335243495610709205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53391574223495663740472803 80087361335243495610709205)
                    ·
                      refine ⟨1877047531294769428375997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80087361335243495610709205 1877047531294769428375997)
                      ·
                        rfl

theorem cell23_3655537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_3655537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655537 prefixEnd_3655537 := by exact prefixLift 3655537
  have htrace : WordTrace (prefixWord ++ tailWord_3655537) baseStart_3655537 baseEnd_3655537 := by
    simpa [prefixWord, tailWord_3655537, baseEnd_3655537] using wordTrace_append hprefix tailTrace_3655537
  have hstable : (prefixWord ++ tailWord_3655537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655537).length < 2 ^ (prefixWord ++ tailWord_3655537).sum := by decide
  have hdescent : baseEnd_3655537 < baseStart_3655537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655587 : List Nat := [1, 1, 1, 4, 1, 2, 1, 12]
def baseStart_3655587 : Nat := 118140960795 + 3655587 * 2 ^ 59
def prefixEnd_3655587 : Nat := 4983230072969 + 3 ^ 40 * 3655587 * 2
def baseEnd_3655587 : Nat := 69521229826944230842621

theorem tailTrace_3655587 : CollatzResearch.WordTrace tailWord_3655587 prefixEnd_3655587 69521229826944230842621 := by
  unfold tailWord_3655587
  simp only [CollatzResearch.WordTrace]
  refine ⟨133330211407440098399693015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88886807604960065599795343 133330211407440098399693015)
  ·
    refine ⟨199995317111160147599539523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133330211407440098399693015 199995317111160147599539523)
    ·
      refine ⟨299992975666740221399309285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199995317111160147599539523 299992975666740221399309285)
      ·
        refine ⟨56248682937513791512370491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299992975666740221399309285 56248682937513791512370491)
        ·
          refine ⟨84373024406270687268555737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56248682937513791512370491 84373024406270687268555737)
          ·
            refine ⟨63279768304703015451416803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84373024406270687268555737 63279768304703015451416803)
            ·
              refine ⟨94919652457054523177125205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63279768304703015451416803 94919652457054523177125205)
              ·
                refine ⟨69521229826944230842621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 94919652457054523177125205 69521229826944230842621)
                ·
                  rfl

theorem cell23_3655587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 12].length) (baseStart_3655587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655587 prefixEnd_3655587 := by exact prefixLift 3655587
  have htrace : WordTrace (prefixWord ++ tailWord_3655587) baseStart_3655587 baseEnd_3655587 := by
    simpa [prefixWord, tailWord_3655587, baseEnd_3655587] using wordTrace_append hprefix tailTrace_3655587
  have hstable : (prefixWord ++ tailWord_3655587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655587).length < 2 ^ (prefixWord ++ tailWord_3655587).sum := by decide
  have hdescent : baseEnd_3655587 < baseStart_3655587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655591 : List Nat := [1, 1, 6, 1, 2, 1, 3, 1, 1, 6]
def baseStart_3655591 : Nat := 118140960795 + 3655591 * 2 ^ 59
def prefixEnd_3655591 : Nat := 4983230072969 + 3 ^ 40 * 3655591 * 2
def baseEnd_3655591 : Nat := 625691753083370739033583

theorem tailTrace_3655591 : CollatzResearch.WordTrace tailWord_3655591 prefixEnd_3655591 625691753083370739033583 := by
  unfold tailWord_3655591
  simp only [CollatzResearch.WordTrace]
  refine ⟨133330357299425607082838627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88886904866283738055225751 133330357299425607082838627)
  ·
    refine ⟨199995535949138410624257941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133330357299425607082838627 199995535949138410624257941)
    ·
      refine ⟨9374790747615862998012091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 199995535949138410624257941 9374790747615862998012091)
      ·
        refine ⟨14062186121423794497018137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9374790747615862998012091 14062186121423794497018137)
        ·
          refine ⟨10546639591067845872763603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14062186121423794497018137 10546639591067845872763603)
          ·
            refine ⟨15819959386601768809145405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10546639591067845872763603 15819959386601768809145405)
            ·
              refine ⟨5932484769975663303429527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15819959386601768809145405 5932484769975663303429527)
              ·
                refine ⟨8898727154963494955144291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932484769975663303429527 8898727154963494955144291)
                ·
                  refine ⟨13348090732445242432716437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8898727154963494955144291 13348090732445242432716437)
                  ·
                    refine ⟨625691753083370739033583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13348090732445242432716437 625691753083370739033583)
                    ·
                      rfl

theorem cell23_3655591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_3655591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655591 prefixEnd_3655591 := by exact prefixLift 3655591
  have htrace : WordTrace (prefixWord ++ tailWord_3655591) baseStart_3655591 baseEnd_3655591 := by
    simpa [prefixWord, tailWord_3655591, baseEnd_3655591] using wordTrace_append hprefix tailTrace_3655591
  have hstable : (prefixWord ++ tailWord_3655591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655591).length < 2 ^ (prefixWord ++ tailWord_3655591).sum := by decide
  have hdescent : baseEnd_3655591 < baseStart_3655591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655631 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 4, 1, 3]
def baseStart_3655631 : Nat := 118140960795 + 3655631 * 2 ^ 59
def prefixEnd_3655631 : Nat := 4983230072969 + 3 ^ 40 * 3655631 * 2
def baseEnd_3655631 : Nat := 1877095798476292060600565

theorem tailTrace_3655631 : CollatzResearch.WordTrace tailWord_3655631 prefixEnd_3655631 1877095798476292060600565 := by
  unfold tailWord_3655631
  simp only [CollatzResearch.WordTrace]
  refine ⟨133331816219280693914294747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88887877479520462609529831 133331816219280693914294747)
  ·
    refine ⟨199997724328921040871442121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133331816219280693914294747 199997724328921040871442121)
    ·
      refine ⟨149998293246690780653581591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199997724328921040871442121 149998293246690780653581591)
      ·
        refine ⟨224997439870036170980372387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149998293246690780653581591 224997439870036170980372387)
        ·
          refine ⟨337496159805054256470558581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224997439870036170980372387 337496159805054256470558581)
          ·
            refine ⟨31640264981723836544114867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 337496159805054256470558581 31640264981723836544114867)
            ·
              refine ⟨47460397472585754816172301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31640264981723836544114867 47460397472585754816172301)
              ·
                refine ⟨17797649052219658056064613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47460397472585754816172301 17797649052219658056064613)
                ·
                  refine ⟨3337059197291185885512115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17797649052219658056064613 3337059197291185885512115)
                  ·
                    refine ⟨5005588795936778828268173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3337059197291185885512115 5005588795936778828268173)
                    ·
                      refine ⟨1877095798476292060600565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5005588795936778828268173 1877095798476292060600565)
                      ·
                        rfl

theorem cell23_3655631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 4, 1, 3].length) (baseStart_3655631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655631 prefixEnd_3655631 := by exact prefixLift 3655631
  have htrace : WordTrace (prefixWord ++ tailWord_3655631) baseStart_3655631 baseEnd_3655631 := by
    simpa [prefixWord, tailWord_3655631, baseEnd_3655631] using wordTrace_append hprefix tailTrace_3655631
  have hstable : (prefixWord ++ tailWord_3655631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655631).length < 2 ^ (prefixWord ++ tailWord_3655631).sum := by decide
  have hdescent : baseEnd_3655631 < baseStart_3655631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655638 : List Nat := [5, 2, 1, 1, 3, 1, 2, 8]
def baseStart_3655638 : Nat := 118140960795 + 3655638 * 2 ^ 59
def prefixEnd_3655638 : Nat := 4983230072969 + 3 ^ 40 * 3655638 * 2
def baseEnd_3655638 : Nat := 69522199734847167896779

theorem tailTrace_3655638 : CollatzResearch.WordTrace tailWord_3655638 prefixEnd_3655638 69522199734847167896779 := by
  unfold tailWord_3655638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8333254470640958381862473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88888047686836889406533045 8333254470640958381862473)
  ·
    refine ⟨6249940852980718786396855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8333254470640958381862473 6249940852980718786396855)
    ·
      refine ⟨9374911279471078179595283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6249940852980718786396855 9374911279471078179595283)
      ·
        refine ⟨14062366919206617269392925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9374911279471078179595283 14062366919206617269392925)
        ·
          refine ⟨5273387594702481476022347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14062366919206617269392925 5273387594702481476022347)
          ·
            refine ⟨7910081392053722214033521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5273387594702481476022347 7910081392053722214033521)
            ·
              refine ⟨5932561044040291660525141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7910081392053722214033521 5932561044040291660525141)
              ·
                refine ⟨69522199734847167896779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5932561044040291660525141 69522199734847167896779)
                ·
                  rfl

theorem cell23_3655638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_3655638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655638 prefixEnd_3655638 := by exact prefixLift 3655638
  have htrace : WordTrace (prefixWord ++ tailWord_3655638) baseStart_3655638 baseEnd_3655638 := by
    simpa [prefixWord, tailWord_3655638, baseEnd_3655638] using wordTrace_append hprefix tailTrace_3655638
  have hstable : (prefixWord ++ tailWord_3655638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655638).length < 2 ^ (prefixWord ++ tailWord_3655638).sum := by decide
  have hdescent : baseEnd_3655638 < baseStart_3655638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655642 : List Nat := [3, 1, 1, 2, 6, 1, 2, 1, 2, 4]
def baseStart_3655642 : Nat := 118140960795 + 3655642 * 2 ^ 59
def prefixEnd_3655642 : Nat := 4983230072969 + 3 ^ 40 * 3655642 * 2
def baseEnd_3655642 : Nat := 625700482254497172521005

theorem tailTrace_3655642 : CollatzResearch.WordTrace tailWord_3655642 prefixEnd_3655642 625700482254497172521005 := by
  unfold tailWord_3655642
  simp only [CollatzResearch.WordTrace]
  refine ⟨33333054355560210698236295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88888144948160561861963453 33333054355560210698236295)
  ·
    refine ⟨49999581533340316047354443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33333054355560210698236295 49999581533340316047354443)
    ·
      refine ⟨74999372300010474071031665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49999581533340316047354443 74999372300010474071031665)
      ·
        refine ⟨56249529225007855553273749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74999372300010474071031665 56249529225007855553273749)
        ·
          refine ⟨2636696682422243229059707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56249529225007855553273749 2636696682422243229059707)
          ·
            refine ⟨3955045023633364843589561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2636696682422243229059707 3955045023633364843589561)
            ·
              refine ⟨2966283767725023632692171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3955045023633364843589561 2966283767725023632692171)
              ·
                refine ⟨4449425651587535449038257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966283767725023632692171 4449425651587535449038257)
                ·
                  refine ⟨3337069238690651586778693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4449425651587535449038257 3337069238690651586778693)
                  ·
                    refine ⟨625700482254497172521005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3337069238690651586778693 625700482254497172521005)
                    ·
                      rfl

theorem cell23_3655642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_3655642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655642 prefixEnd_3655642 := by exact prefixLift 3655642
  have htrace : WordTrace (prefixWord ++ tailWord_3655642) baseStart_3655642 baseEnd_3655642 := by
    simpa [prefixWord, tailWord_3655642, baseEnd_3655642] using wordTrace_append hprefix tailTrace_3655642
  have hstable : (prefixWord ++ tailWord_3655642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655642).length < 2 ^ (prefixWord ++ tailWord_3655642).sum := by decide
  have hdescent : baseEnd_3655642 < baseStart_3655642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655658 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_3655658 : Nat := 118140960795 + 3655658 * 2 ^ 59
def prefixEnd_3655658 : Nat := 4983230072969 + 3 ^ 40 * 3655658 * 2
def baseEnd_3655658 : Nat := 1877109662453963454962941

theorem tailTrace_3655658 : CollatzResearch.WordTrace tailWord_3655658 prefixEnd_3655658 1877109662453963454962941 := by
  unfold tailWord_3655658
  simp only [CollatzResearch.WordTrace]
  refine ⟨33333200247545719381381907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88888533993455251683685085 33333200247545719381381907)
  ·
    refine ⟨49999800371318579072072861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33333200247545719381381907 49999800371318579072072861)
    ·
      refine ⟨18749925139244467152027323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49999800371318579072072861 18749925139244467152027323)
      ·
        refine ⟨28124887708866700728040985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18749925139244467152027323 28124887708866700728040985)
        ·
          refine ⟨21093665781650025546030739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28124887708866700728040985 21093665781650025546030739)
          ·
            refine ⟨31640498672475038319046109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21093665781650025546030739 31640498672475038319046109)
            ·
              refine ⟨11865187002178139369642291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31640498672475038319046109 11865187002178139369642291)
              ·
                refine ⟨17797780503267209054463437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11865187002178139369642291 17797780503267209054463437)
                ·
                  refine ⟨6674167688725203395423789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17797780503267209054463437 6674167688725203395423789)
                  ·
                    refine ⟨2502812883271951273283921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6674167688725203395423789 2502812883271951273283921)
                    ·
                      refine ⟨1877109662453963454962941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502812883271951273283921 1877109662453963454962941)
                      ·
                        rfl

theorem cell23_3655658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_3655658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655658 prefixEnd_3655658 := by exact prefixLift 3655658
  have htrace : WordTrace (prefixWord ++ tailWord_3655658) baseStart_3655658 baseEnd_3655658 := by
    simpa [prefixWord, tailWord_3655658, baseEnd_3655658] using wordTrace_append hprefix tailTrace_3655658
  have hstable : (prefixWord ++ tailWord_3655658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655658).length < 2 ^ (prefixWord ++ tailWord_3655658).sum := by decide
  have hdescent : baseEnd_3655658 < baseStart_3655658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655728 : List Nat := [2, 1, 1, 1, 2, 6, 2, 3, 5]
def baseStart_3655728 : Nat := 118140960795 + 3655728 * 2 ^ 59
def prefixEnd_3655728 : Nat := 4983230072969 + 3 ^ 40 * 3655728 * 2
def baseEnd_3655728 : Nat := 208571734011086464565291

theorem tailTrace_3655728 : CollatzResearch.WordTrace tailWord_3655728 prefixEnd_3655728 208571734011086464565291 := by
  unfold tailWord_3655728
  simp only [CollatzResearch.WordTrace]
  refine ⟨66667677049964639740287919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88890236066619519653717225 66667677049964639740287919)
  ·
    refine ⟨100001515574946959610431879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66667677049964639740287919 100001515574946959610431879)
    ·
      refine ⟨150002273362420439415647819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100001515574946959610431879 150002273362420439415647819)
      ·
        refine ⟨225003410043630659123471729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150002273362420439415647819 225003410043630659123471729)
        ·
          refine ⟨168752557532722994342603797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225003410043630659123471729 168752557532722994342603797)
          ·
            refine ⟨7910276134346390359809553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168752557532722994342603797 7910276134346390359809553)
            ·
              refine ⟨5932707100759792769857165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7910276134346390359809553 5932707100759792769857165)
              ·
                refine ⟨2224765162784922288696437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5932707100759792769857165 2224765162784922288696437)
                ·
                  refine ⟨208571734011086464565291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2224765162784922288696437 208571734011086464565291)
                  ·
                    rfl

theorem cell23_3655728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 5].length) (baseStart_3655728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655728 prefixEnd_3655728 := by exact prefixLift 3655728
  have htrace : WordTrace (prefixWord ++ tailWord_3655728) baseStart_3655728 baseEnd_3655728 := by
    simpa [prefixWord, tailWord_3655728, baseEnd_3655728] using wordTrace_append hprefix tailTrace_3655728
  have hstable : (prefixWord ++ tailWord_3655728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655728).length < 2 ^ (prefixWord ++ tailWord_3655728).sum := by decide
  have hdescent : baseEnd_3655728 < baseStart_3655728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655741 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_3655741 : Nat := 118140960795 + 3655741 * 2 ^ 59
def prefixEnd_3655741 : Nat := 4983230072969 + 3 ^ 40 * 3655741 * 2
def baseEnd_3655741 : Nat := 625717427116095543408353

theorem tailTrace_3655741 : CollatzResearch.WordTrace tailWord_3655741 prefixEnd_3655741 625717427116095543408353 := by
  unfold tailWord_3655741
  simp only [CollatzResearch.WordTrace]
  refine ⟨133335828248882182700799077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88890552165921455133866051 133335828248882182700799077)
  ·
    refine ⟨25000467796665409256399827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133335828248882182700799077 25000467796665409256399827)
    ·
      refine ⟨37500701694998113884599741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25000467796665409256399827 37500701694998113884599741)
      ·
        refine ⟨14062763135624292706724903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37500701694998113884599741 14062763135624292706724903)
        ·
          refine ⟨21094144703436439060087355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14062763135624292706724903 21094144703436439060087355)
          ·
            refine ⟨31641217055154658590131033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21094144703436439060087355 31641217055154658590131033)
            ·
              refine ⟨23730912791365993942598275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31641217055154658590131033 23730912791365993942598275)
              ·
                refine ⟨35596369187048990913897413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23730912791365993942598275 35596369187048990913897413)
                ·
                  refine ⟨6674319222571685796355765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35596369187048990913897413 6674319222571685796355765)
                  ·
                    refine ⟨625717427116095543408353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6674319222571685796355765 625717427116095543408353)
                    ·
                      rfl

theorem cell23_3655741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_3655741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655741 prefixEnd_3655741 := by exact prefixLift 3655741
  have htrace : WordTrace (prefixWord ++ tailWord_3655741) baseStart_3655741 baseEnd_3655741 := by
    simpa [prefixWord, tailWord_3655741, baseEnd_3655741] using wordTrace_append hprefix tailTrace_3655741
  have hstable : (prefixWord ++ tailWord_3655741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655741).length < 2 ^ (prefixWord ++ tailWord_3655741).sum := by decide
  have hdescent : baseEnd_3655741 < baseStart_3655741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655801 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 8]
def baseStart_3655801 : Nat := 118140960795 + 3655801 * 2 ^ 59
def prefixEnd_3655801 : Nat := 4983230072969 + 3 ^ 40 * 3655801 * 2
def baseEnd_3655801 : Nat := 208575898909728488386087

theorem tailTrace_3655801 : CollatzResearch.WordTrace tailWord_3655801 prefixEnd_3655801 208575898909728488386087 := by
  unfold tailWord_3655801
  simp only [CollatzResearch.WordTrace]
  refine ⟨133338016628664812947983257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88892011085776541965322171 133338016628664812947983257)
  ·
    refine ⟨100003512471498609710987443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133338016628664812947983257 100003512471498609710987443)
    ·
      refine ⟨150005268707247914566481165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100003512471498609710987443 150005268707247914566481165)
      ·
        refine ⟨56251975765217967962430437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150005268707247914566481165 56251975765217967962430437)
        ·
          refine ⟨10547245455978368992955707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56251975765217967962430437 10547245455978368992955707)
          ·
            refine ⟨15820868183967553489433561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10547245455978368992955707 15820868183967553489433561)
            ·
              refine ⟨11865651137975665117075171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15820868183967553489433561 11865651137975665117075171)
              ·
                refine ⟨17798476706963497675612757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11865651137975665117075171 17798476706963497675612757)
                ·
                  refine ⟨208575898909728488386087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17798476706963497675612757 208575898909728488386087)
                  ·
                    rfl

theorem cell23_3655801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 8].length) (baseStart_3655801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655801 prefixEnd_3655801 := by exact prefixLift 3655801
  have htrace : WordTrace (prefixWord ++ tailWord_3655801) baseStart_3655801 baseEnd_3655801 := by
    simpa [prefixWord, tailWord_3655801, baseEnd_3655801] using wordTrace_append hprefix tailTrace_3655801
  have hstable : (prefixWord ++ tailWord_3655801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655801).length < 2 ^ (prefixWord ++ tailWord_3655801).sum := by decide
  have hdescent : baseEnd_3655801 < baseStart_3655801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655805 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_3655805 : Nat := 118140960795 + 3655805 * 2 ^ 59
def prefixEnd_3655805 : Nat := 4983230072969 + 3 ^ 40 * 3655805 * 2
def baseEnd_3655805 : Nat := 625728381370058126608255

theorem tailTrace_3655805 : CollatzResearch.WordTrace tailWord_3655805 prefixEnd_3655805 625728381370058126608255 := by
  unfold tailWord_3655805
  simp only [CollatzResearch.WordTrace]
  refine ⟨133338162520650321631128869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88892108347100214420752579 133338162520650321631128869)
  ·
    refine ⟨25000905472621935305836663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133338162520650321631128869 25000905472621935305836663)
    ·
      refine ⟨37501358208932902958754995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25000905472621935305836663 37501358208932902958754995)
      ·
        refine ⟨56252037313399354438132493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37501358208932902958754995 56252037313399354438132493)
        ·
          refine ⟨21094513992524757914299685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56252037313399354438132493 21094513992524757914299685)
          ·
            refine ⟨3955221373598392108931191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21094513992524757914299685 3955221373598392108931191)
            ·
              refine ⟨5932832060397588163396787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955221373598392108931191 5932832060397588163396787)
              ·
                refine ⟨8899248090596382245095181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5932832060397588163396787 8899248090596382245095181)
                ·
                  refine ⟨3337218033973643341910693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8899248090596382245095181 3337218033973643341910693)
                  ·
                    refine ⟨625728381370058126608255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3337218033973643341910693 625728381370058126608255)
                    ·
                      rfl

theorem cell23_3655805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_3655805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655805 prefixEnd_3655805 := by exact prefixLift 3655805
  have htrace : WordTrace (prefixWord ++ tailWord_3655805) baseStart_3655805 baseEnd_3655805 := by
    simpa [prefixWord, tailWord_3655805, baseEnd_3655805] using wordTrace_append hprefix tailTrace_3655805
  have hstable : (prefixWord ++ tailWord_3655805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655805).length < 2 ^ (prefixWord ++ tailWord_3655805).sum := by decide
  have hdescent : baseEnd_3655805 < baseStart_3655805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655818 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 6]
def baseStart_3655818 : Nat := 118140960795 + 3655818 * 2 ^ 59
def prefixEnd_3655818 : Nat := 4983230072969 + 3 ^ 40 * 3655818 * 2
def baseEnd_3655818 : Nat := 208576868817631425440245

theorem tailTrace_3655818 : CollatzResearch.WordTrace tailWord_3655818 prefixEnd_3655818 208576868817631425440245 := by
  unfold tailWord_3655818
  simp only [CollatzResearch.WordTrace]
  refine ⟨33334659167400806212838027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88892424446402149900901405 33334659167400806212838027)
  ·
    refine ⟨50001988751101209319257041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33334659167400806212838027 50001988751101209319257041)
    ·
      refine ⟨37501491563325906989442781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50001988751101209319257041 37501491563325906989442781)
      ·
        refine ⟨14063059336247215121041043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37501491563325906989442781 14063059336247215121041043)
        ·
          refine ⟨21094589004370822681561565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14063059336247215121041043 21094589004370822681561565)
          ·
            refine ⟨7910470876639058505585587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21094589004370822681561565 7910470876639058505585587)
            ·
              refine ⟨11865706314958587758378381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7910470876639058505585587 11865706314958587758378381)
              ·
                refine ⟨4449639868109470409391893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11865706314958587758378381 4449639868109470409391893)
                ·
                  refine ⟨208576868817631425440245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4449639868109470409391893 208576868817631425440245)
                  ·
                    rfl

theorem cell23_3655818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_3655818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655818 prefixEnd_3655818 := by exact prefixLift 3655818
  have htrace : WordTrace (prefixWord ++ tailWord_3655818) baseStart_3655818 baseEnd_3655818 := by
    simpa [prefixWord, tailWord_3655818, baseEnd_3655818] using wordTrace_append hprefix tailTrace_3655818
  have hstable : (prefixWord ++ tailWord_3655818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655818).length < 2 ^ (prefixWord ++ tailWord_3655818).sum := by decide
  have hdescent : baseEnd_3655818 < baseStart_3655818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655871 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 5]
def baseStart_3655871 : Nat := 118140960795 + 3655871 * 2 ^ 59
def prefixEnd_3655871 : Nat := 4983230072969 + 3 ^ 40 * 3655871 * 2
def baseEnd_3655871 : Nat := 1877219033833371121599461

theorem tailTrace_3655871 : CollatzResearch.WordTrace tailWord_3655871 prefixEnd_3655871 1877219033833371121599461 := by
  unfold tailWord_3655871
  simp only [CollatzResearch.WordTrace]
  refine ⟨133340569738411214903031467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88893713158940809935354311 133340569738411214903031467)
  ·
    refine ⟨200010854607616822354547201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133340569738411214903031467 200010854607616822354547201)
    ·
      refine ⟨150008140955712616765910401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200010854607616822354547201 150008140955712616765910401)
      ·
        refine ⟨112506105716784462574432801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150008140955712616765910401 112506105716784462574432801)
        ·
          refine ⟨84379579287588346930824601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112506105716784462574432801 84379579287588346930824601)
          ·
            refine ⟨63284684465691260198118451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84379579287588346930824601 63284684465691260198118451)
            ·
              refine ⟨94927026698536890297177677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63284684465691260198118451 94927026698536890297177677)
              ·
                refine ⟨35597635011951333861441629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94927026698536890297177677 35597635011951333861441629)
                ·
                  refine ⟨13349113129481750198040611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35597635011951333861441629 13349113129481750198040611)
                  ·
                    refine ⟨20023669694222625297060917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13349113129481750198040611 20023669694222625297060917)
                    ·
                      refine ⟨1877219033833371121599461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20023669694222625297060917 1877219033833371121599461)
                      ·
                        rfl

theorem cell23_3655871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_3655871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655871 prefixEnd_3655871 := by exact prefixLift 3655871
  have htrace : WordTrace (prefixWord ++ tailWord_3655871) baseStart_3655871 baseEnd_3655871 := by
    simpa [prefixWord, tailWord_3655871, baseEnd_3655871] using wordTrace_append hprefix tailTrace_3655871
  have hstable : (prefixWord ++ tailWord_3655871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655871).length < 2 ^ (prefixWord ++ tailWord_3655871).sum := by decide
  have hdescent : baseEnd_3655871 < baseStart_3655871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655898 : List Nat := [3, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4]
def baseStart_3655898 : Nat := 118140960795 + 3655898 * 2 ^ 59
def prefixEnd_3655898 : Nat := 4983230072969 + 3 ^ 40 * 3655898 * 2
def baseEnd_3655898 : Nat := 1877232897811042515961837

theorem tailTrace_3655898 : CollatzResearch.WordTrace tailWord_3655898 prefixEnd_3655898 1877232897811042515961837 := by
  unfold tailWord_3655898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33335388627328349628566087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88894369672875599009509565 33335388627328349628566087)
  ·
    refine ⟨50003082940992524442849131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33335388627328349628566087 50003082940992524442849131)
    ·
      refine ⟨75004624411488786664273697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50003082940992524442849131 75004624411488786664273697)
      ·
        refine ⟨56253468308616589998205273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75004624411488786664273697 56253468308616589998205273)
        ·
          refine ⟨42190101231462442498653955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56253468308616589998205273 42190101231462442498653955)
          ·
            refine ⟨63285151847193663747980933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42190101231462442498653955 63285151847193663747980933)
            ·
              refine ⟨11865965971348811952746425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63285151847193663747980933 11865965971348811952746425)
              ·
                refine ⟨8899474478511608964559819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11865965971348811952746425 8899474478511608964559819)
                ·
                  refine ⟨13349211717767413446839729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8899474478511608964559819 13349211717767413446839729)
                  ·
                    refine ⟨10011908788325560085129797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13349211717767413446839729 10011908788325560085129797)
                    ·
                      refine ⟨1877232897811042515961837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10011908788325560085129797 1877232897811042515961837)
                      ·
                        rfl

theorem cell23_3655898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_3655898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655898 prefixEnd_3655898 := by exact prefixLift 3655898
  have htrace : WordTrace (prefixWord ++ tailWord_3655898) baseStart_3655898 baseEnd_3655898 := by
    simpa [prefixWord, tailWord_3655898, baseEnd_3655898] using wordTrace_append hprefix tailTrace_3655898
  have hstable : (prefixWord ++ tailWord_3655898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655898).length < 2 ^ (prefixWord ++ tailWord_3655898).sum := by decide
  have hdescent : baseEnd_3655898 < baseStart_3655898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655905 : List Nat := [1, 2, 3, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_3655905 : Nat := 118140960795 + 3655905 * 2 ^ 59
def prefixEnd_3655905 : Nat := 4983230072969 + 3 ^ 40 * 3655905 * 2
def baseEnd_3655905 : Nat := 1877236492175623988574305

theorem tailTrace_3655905 : CollatzResearch.WordTrace tailWord_3655905 prefixEnd_3655905 1877236492175623988574305 := by
  unfold tailWord_3655905
  simp only [CollatzResearch.WordTrace]
  refine ⟨133341809820288038709769169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88894539880192025806512779 133341809820288038709769169)
  ·
    refine ⟨100006357365216029032326877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133341809820288038709769169 100006357365216029032326877)
    ·
      refine ⟨37502384011956010887122579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100006357365216029032326877 37502384011956010887122579)
      ·
        refine ⟨56253576017934016330683869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37502384011956010887122579 56253576017934016330683869)
        ·
          refine ⟨21095091006725256124006451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56253576017934016330683869 21095091006725256124006451)
          ·
            refine ⟨31642636510087884186009677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21095091006725256124006451 31642636510087884186009677)
            ·
              refine ⟨11865988691282956569753629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31642636510087884186009677 11865988691282956569753629)
              ·
                refine ⟨4449745759231108713657611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11865988691282956569753629 4449745759231108713657611)
                ·
                  refine ⟨6674618638846663070486417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4449745759231108713657611 6674618638846663070486417)
                  ·
                    refine ⟨5005963979134997302864813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6674618638846663070486417 5005963979134997302864813)
                    ·
                      refine ⟨1877236492175623988574305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5005963979134997302864813 1877236492175623988574305)
                      ·
                        rfl

theorem cell23_3655905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_3655905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655905 prefixEnd_3655905 := by exact prefixLift 3655905
  have htrace : WordTrace (prefixWord ++ tailWord_3655905) baseStart_3655905 baseEnd_3655905 := by
    simpa [prefixWord, tailWord_3655905, baseEnd_3655905] using wordTrace_append hprefix tailTrace_3655905
  have hstable : (prefixWord ++ tailWord_3655905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655905).length < 2 ^ (prefixWord ++ tailWord_3655905).sum := by decide
  have hdescent : baseEnd_3655905 < baseStart_3655905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655912 : List Nat := [2, 1, 4, 1, 2, 4, 1, 2, 2, 4]
def baseStart_3655912 : Nat := 118140960795 + 3655912 * 2 ^ 59
def prefixEnd_3655912 : Nat := 4983230072969 + 3 ^ 40 * 3655912 * 2
def baseEnd_3655912 : Nat := 625746695513401820395591

theorem tailTrace_3655912 : CollatzResearch.WordTrace tailWord_3655912 prefixEnd_3655912 625746695513401820395591 := by
  unfold tailWord_3655912
  simp only [CollatzResearch.WordTrace]
  refine ⟨66671032565631339452636995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88894710087508452603515993 66671032565631339452636995)
  ·
    refine ⟨100006548848447009178955493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66671032565631339452636995 100006548848447009178955493)
    ·
      refine ⟨18751227909083814221054155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100006548848447009178955493 18751227909083814221054155)
      ·
        refine ⟨28126841863625721331581233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18751227909083814221054155 28126841863625721331581233)
        ·
          refine ⟨21095131397719290998685925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28126841863625721331581233 21095131397719290998685925)
          ·
            refine ⟨3955337137072367062253611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21095131397719290998685925 3955337137072367062253611)
            ·
              refine ⟨5933005705608550593380417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955337137072367062253611 5933005705608550593380417)
              ·
                refine ⟨4449754279206412945035313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5933005705608550593380417 4449754279206412945035313)
                ·
                  refine ⟨3337315709404809708776485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4449754279206412945035313 3337315709404809708776485)
                  ·
                    refine ⟨625746695513401820395591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3337315709404809708776485 625746695513401820395591)
                    ·
                      rfl

theorem cell23_3655912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_3655912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655912 prefixEnd_3655912 := by exact prefixLift 3655912
  have htrace : WordTrace (prefixWord ++ tailWord_3655912) baseStart_3655912 baseEnd_3655912 := by
    simpa [prefixWord, tailWord_3655912, baseEnd_3655912] using wordTrace_append hprefix tailTrace_3655912
  have hstable : (prefixWord ++ tailWord_3655912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655912).length < 2 ^ (prefixWord ++ tailWord_3655912).sum := by decide
  have hdescent : baseEnd_3655912 < baseStart_3655912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655919 : List Nat := [1, 1, 2, 1, 6, 1, 2, 4, 1, 2, 2]
def baseStart_3655919 : Nat := 118140960795 + 3655919 * 2 ^ 59
def prefixEnd_3655919 : Nat := 4983230072969 + 3 ^ 40 * 3655919 * 2
def baseEnd_3655919 : Nat := 1877243680904786933799241

theorem tailTrace_3655919 : CollatzResearch.WordTrace tailWord_3655919 prefixEnd_3655919 1877243680904786933799241 := by
  unfold tailWord_3655919
  simp only [CollatzResearch.WordTrace]
  refine ⟨133342320442237319100778811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88894880294824879400519207 133342320442237319100778811)
  ·
    refine ⟨200013480663355978651168217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133342320442237319100778811 200013480663355978651168217)
    ·
      refine ⟨150010110497516983988376163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200013480663355978651168217 150010110497516983988376163)
      ·
        refine ⟨225015165746275475982564245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150010110497516983988376163 225015165746275475982564245)
        ·
          refine ⟨10547585894356662936682699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225015165746275475982564245 10547585894356662936682699)
          ·
            refine ⟨15821378841534994405024049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10547585894356662936682699 15821378841534994405024049)
            ·
              refine ⟨11866034131151245803768037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15821378841534994405024049 11866034131151245803768037)
              ·
                refine ⟨2224881399590858588206507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11866034131151245803768037 2224881399590858588206507)
                ·
                  refine ⟨3337322099386287882309761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2224881399590858588206507 3337322099386287882309761)
                  ·
                    refine ⟨2502991574539715911732321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3337322099386287882309761 2502991574539715911732321)
                    ·
                      refine ⟨1877243680904786933799241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2502991574539715911732321 1877243680904786933799241)
                      ·
                        rfl

theorem cell23_3655919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 1, 2, 2].length) (baseStart_3655919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655919 prefixEnd_3655919 := by exact prefixLift 3655919
  have htrace : WordTrace (prefixWord ++ tailWord_3655919) baseStart_3655919 baseEnd_3655919 := by
    simpa [prefixWord, tailWord_3655919, baseEnd_3655919] using wordTrace_append hprefix tailTrace_3655919
  have hstable : (prefixWord ++ tailWord_3655919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655919).length < 2 ^ (prefixWord ++ tailWord_3655919).sum := by decide
  have hdescent : baseEnd_3655919 < baseStart_3655919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655921 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 1, 9]
def baseStart_3655921 : Nat := 118140960795 + 3655921 * 2 ^ 59
def prefixEnd_3655921 : Nat := 4983230072969 + 3 ^ 40 * 3655921 * 2
def baseEnd_3655921 : Nat := 625748235955365308658077

theorem tailTrace_3655921 : CollatzResearch.WordTrace tailWord_3655921 prefixEnd_3655921 625748235955365308658077 := by
  unfold tailWord_3655921
  simp only [CollatzResearch.WordTrace]
  refine ⟨133342393388230073442351617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88894928925486715628234411 133342393388230073442351617)
  ·
    refine ⟨100006795041172555081763713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133342393388230073442351617 100006795041172555081763713)
    ·
      refine ⟨75005096280879416311322785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100006795041172555081763713 75005096280879416311322785)
      ·
        refine ⟨56253822210659562233492089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75005096280879416311322785 56253822210659562233492089)
        ·
          refine ⟨42190366657994671675119067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56253822210659562233492089 42190366657994671675119067)
          ·
            refine ⟨63285549986992007512678601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42190366657994671675119067 63285549986992007512678601)
            ·
              refine ⟨47464162490244005634508951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63285549986992007512678601 47464162490244005634508951)
              ·
                refine ⟨71196243735366008451763427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47464162490244005634508951 71196243735366008451763427)
                ·
                  refine ⟨106794365603049012677645141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71196243735366008451763427 106794365603049012677645141)
                  ·
                    refine ⟨625748235955365308658077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 106794365603049012677645141 625748235955365308658077)
                    ·
                      rfl

theorem cell23_3655921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_3655921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655921 prefixEnd_3655921 := by exact prefixLift 3655921
  have htrace : WordTrace (prefixWord ++ tailWord_3655921) baseStart_3655921 baseEnd_3655921 := by
    simpa [prefixWord, tailWord_3655921, baseEnd_3655921] using wordTrace_append hprefix tailTrace_3655921
  have hstable : (prefixWord ++ tailWord_3655921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655921).length < 2 ^ (prefixWord ++ tailWord_3655921).sum := by decide
  have hdescent : baseEnd_3655921 < baseStart_3655921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655931 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 5]
def baseStart_3655931 : Nat := 118140960795 + 3655931 * 2 ^ 59
def prefixEnd_3655931 : Nat := 4983230072969 + 3 ^ 40 * 3655931 * 2
def baseEnd_3655931 : Nat := 1877249842672640886849185

theorem tailTrace_3655931 : CollatzResearch.WordTrace tailWord_3655931 prefixEnd_3655931 1877249842672640886849185 := by
  unfold tailWord_3655931
  simp only [CollatzResearch.WordTrace]
  refine ⟨133342758118193845150215647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88895172078795896766810431 133342758118193845150215647)
  ·
    refine ⟨200014137177290767725323471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133342758118193845150215647 200014137177290767725323471)
    ·
      refine ⟨300021205765936151587985207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200014137177290767725323471 300021205765936151587985207)
      ·
        refine ⟨450031808648904227381977811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300021205765936151587985207 450031808648904227381977811)
        ·
          refine ⟨675047712973356341072966717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450031808648904227381977811 675047712973356341072966717)
          ·
            refine ⟨253142892365008627902362519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675047712973356341072966717 253142892365008627902362519)
            ·
              refine ⟨379714338547512941853543779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253142892365008627902362519 379714338547512941853543779)
              ·
                refine ⟨569571507821269412780315669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379714338547512941853543779 569571507821269412780315669)
                ·
                  refine ⟨26698664429122003724077297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 569571507821269412780315669 26698664429122003724077297)
                  ·
                    refine ⟨20023998321841502793057973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26698664429122003724077297 20023998321841502793057973)
                    ·
                      refine ⟨1877249842672640886849185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20023998321841502793057973 1877249842672640886849185)
                      ·
                        rfl

theorem cell23_3655931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_3655931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655931 prefixEnd_3655931 := by exact prefixLift 3655931
  have htrace : WordTrace (prefixWord ++ tailWord_3655931) baseStart_3655931 baseEnd_3655931 := by
    simpa [prefixWord, tailWord_3655931, baseEnd_3655931] using wordTrace_append hprefix tailTrace_3655931
  have hstable : (prefixWord ++ tailWord_3655931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655931).length < 2 ^ (prefixWord ++ tailWord_3655931).sum := by decide
  have hdescent : baseEnd_3655931 < baseStart_3655931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655941 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_3655941 : Nat := 118140960795 + 3655941 * 2 ^ 59
def prefixEnd_3655941 : Nat := 4983230072969 + 3 ^ 40 * 3655941 * 2
def baseEnd_3655941 : Nat := 1877254977479185847724139

theorem tailTrace_3655941 : CollatzResearch.WordTrace tailWord_3655941 prefixEnd_3655941 1877254977479185847724139 := by
  unfold tailWord_3655941
  simp only [CollatzResearch.WordTrace]
  refine ⟨133343122848157616858079677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88895415232105077905386451 133343122848157616858079677)
  ·
    refine ⟨50003671068059106321779879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133343122848157616858079677 50003671068059106321779879)
    ·
      refine ⟨75005506602088659482669819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50003671068059106321779879 75005506602088659482669819)
      ·
        refine ⟨112508259903132989224004729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75005506602088659482669819 112508259903132989224004729)
        ·
          refine ⟨84381194927349741918003547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112508259903132989224004729 84381194927349741918003547)
          ·
            refine ⟨126571792391024612877005321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84381194927349741918003547 126571792391024612877005321)
            ·
              refine ⟨94928844293268459657753991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126571792391024612877005321 94928844293268459657753991)
              ·
                refine ⟨142393266439902689486630987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94928844293268459657753991 142393266439902689486630987)
                ·
                  refine ⟨213589899659854034229946481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142393266439902689486630987 213589899659854034229946481)
                  ·
                    refine ⟨160192424744890525672459861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 213589899659854034229946481 160192424744890525672459861)
                    ·
                      refine ⟨1877254977479185847724139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 160192424744890525672459861 1877254977479185847724139)
                      ·
                        rfl

theorem cell23_3655941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_3655941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655941 prefixEnd_3655941 := by exact prefixLift 3655941
  have htrace : WordTrace (prefixWord ++ tailWord_3655941) baseStart_3655941 baseEnd_3655941 := by
    simpa [prefixWord, tailWord_3655941, baseEnd_3655941] using wordTrace_append hprefix tailTrace_3655941
  have hstable : (prefixWord ++ tailWord_3655941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655941).length < 2 ^ (prefixWord ++ tailWord_3655941).sum := by decide
  have hdescent : baseEnd_3655941 < baseStart_3655941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655951 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 1, 8]
def baseStart_3655951 : Nat := 118140960795 + 3655951 * 2 ^ 59
def prefixEnd_3655951 : Nat := 4983230072969 + 3 ^ 40 * 3655951 * 2
def baseEnd_3655951 : Nat := 625753370761910269533031

theorem tailTrace_3655951 : CollatzResearch.WordTrace tailWord_3655951 prefixEnd_3655951 625753370761910269533031 := by
  unfold tailWord_3655951
  simp only [CollatzResearch.WordTrace]
  refine ⟨133343487578121388565943707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88895658385414259043962471 133343487578121388565943707)
  ·
    refine ⟨200015231367182082848915561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133343487578121388565943707 200015231367182082848915561)
    ·
      refine ⟨150011423525386562136686671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200015231367182082848915561 150011423525386562136686671)
      ·
        refine ⟨225017135288079843205030007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150011423525386562136686671 225017135288079843205030007)
        ·
          refine ⟨337525702932119764807545011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225017135288079843205030007 337525702932119764807545011)
          ·
            refine ⟨506288554398179647211317517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337525702932119764807545011 506288554398179647211317517)
            ·
              refine ⟨189858207899317367704244069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506288554398179647211317517 189858207899317367704244069)
              ·
                refine ⟨35598413981122006444545763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189858207899317367704244069 35598413981122006444545763)
                ·
                  refine ⟨53397620971683009666818645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35598413981122006444545763 53397620971683009666818645)
                  ·
                    refine ⟨625753370761910269533031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53397620971683009666818645 625753370761910269533031)
                    ·
                      rfl

theorem cell23_3655951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_3655951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655951 prefixEnd_3655951 := by exact prefixLift 3655951
  have htrace : WordTrace (prefixWord ++ tailWord_3655951) baseStart_3655951 baseEnd_3655951 := by
    simpa [prefixWord, tailWord_3655951, baseEnd_3655951] using wordTrace_append hprefix tailTrace_3655951
  have hstable : (prefixWord ++ tailWord_3655951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655951).length < 2 ^ (prefixWord ++ tailWord_3655951).sum := by decide
  have hdescent : baseEnd_3655951 < baseStart_3655951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655986 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3]
def baseStart_3655986 : Nat := 118140960795 + 3655986 * 2 ^ 59
def prefixEnd_3655986 : Nat := 4983230072969 + 3 ^ 40 * 3655986 * 2
def baseEnd_3655986 : Nat := 1877278084108638171661433

theorem tailTrace_3655986 : CollatzResearch.WordTrace tailWord_3655986 prefixEnd_3655986 1877278084108638171661433 := by
  unfold tailWord_3655986
  simp only [CollatzResearch.WordTrace]
  refine ⟨33336191033248647385866953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88896509421996393028978541 33336191033248647385866953)
  ·
    refine ⟨25002143274936485539400215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33336191033248647385866953 25002143274936485539400215)
    ·
      refine ⟨37503214912404728309100323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25002143274936485539400215 37503214912404728309100323)
      ·
        refine ⟨56254822368607092463650485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37503214912404728309100323 56254822368607092463650485)
        ·
          refine ⟨5273889597056914918467233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56254822368607092463650485 5273889597056914918467233)
          ·
            refine ⟨3955417197792686188850425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5273889597056914918467233 3955417197792686188850425)
            ·
              refine ⟨2966562898344514641637819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3955417197792686188850425 2966562898344514641637819)
              ·
                refine ⟨4449844347516771962456729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966562898344514641637819 4449844347516771962456729)
                ·
                  refine ⟨3337383260637578971842547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4449844347516771962456729 3337383260637578971842547)
                  ·
                    refine ⟨5006074890956368457763821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3337383260637578971842547 5006074890956368457763821)
                    ·
                      refine ⟨1877278084108638171661433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5006074890956368457763821 1877278084108638171661433)
                      ·
                        rfl

theorem cell23_3655986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3].length) (baseStart_3655986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3655986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3655986 prefixEnd_3655986 := by exact prefixLift 3655986
  have htrace : WordTrace (prefixWord ++ tailWord_3655986) baseStart_3655986 baseEnd_3655986 := by
    simpa [prefixWord, tailWord_3655986, baseEnd_3655986] using wordTrace_append hprefix tailTrace_3655986
  have hstable : (prefixWord ++ tailWord_3655986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655986).length < 2 ^ (prefixWord ++ tailWord_3655986).sum := by decide
  have hdescent : baseEnd_3655986 < baseStart_3655986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656032 : List Nat := [2, 1, 1, 3, 5, 1, 1, 4, 5]
def baseStart_3656032 : Nat := 118140960795 + 3656032 * 2 ^ 59
def prefixEnd_3656032 : Nat := 4983230072969 + 3 ^ 40 * 3656032 * 2
def baseEnd_3656032 : Nat := 208589078246527221298469

theorem tailTrace_3656032 : CollatzResearch.WordTrace tailWord_3656032 prefixEnd_3656032 208589078246527221298469 := by
  unfold tailWord_3656032
  simp only [CollatzResearch.WordTrace]
  refine ⟨66673220945413969699821175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88897627927218626266428233 66673220945413969699821175)
  ·
    refine ⟨100009831418120954549731763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66673220945413969699821175 100009831418120954549731763)
    ·
      refine ⟨150014747127181431824597645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100009831418120954549731763 150014747127181431824597645)
      ·
        refine ⟨56255530172693036934224117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150014747127181431824597645 56255530172693036934224117)
        ·
          refine ⟨5273955953689972212583511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56255530172693036934224117 5273955953689972212583511)
          ·
            refine ⟨7910933930534958318875267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5273955953689972212583511 7910933930534958318875267)
            ·
              refine ⟨11866400895802437478312901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7910933930534958318875267 11866400895802437478312901)
              ·
                refine ⟨2224950167962957027183669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11866400895802437478312901 2224950167962957027183669)
                ·
                  refine ⟨208589078246527221298469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2224950167962957027183669 208589078246527221298469)
                  ·
                    rfl

theorem cell23_3656032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 5].length) (baseStart_3656032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656032 prefixEnd_3656032 := by exact prefixLift 3656032
  have htrace : WordTrace (prefixWord ++ tailWord_3656032) baseStart_3656032 baseEnd_3656032 := by
    simpa [prefixWord, tailWord_3656032, baseEnd_3656032] using wordTrace_append hprefix tailTrace_3656032
  have hstable : (prefixWord ++ tailWord_3656032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656032).length < 2 ^ (prefixWord ++ tailWord_3656032).sum := by decide
  have hdescent : baseEnd_3656032 < baseStart_3656032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656035 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 1, 7, 2]
def baseStart_3656035 : Nat := 118140960795 + 3656035 * 2 ^ 59
def prefixEnd_3656035 : Nat := 4983230072969 + 3 ^ 40 * 3656035 * 2
def baseEnd_3656035 : Nat := 1877303244660708479948707

theorem tailTrace_3656035 : CollatzResearch.WordTrace tailWord_3656035 prefixEnd_3656035 1877303244660708479948707 := by
  unfold tailWord_3656035
  simp only [CollatzResearch.WordTrace]
  refine ⟨133346551309817070912001559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88897700873211380608001039 133346551309817070912001559)
  ·
    refine ⟨200019826964725606368002339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133346551309817070912001559 200019826964725606368002339)
    ·
      refine ⟨300029740447088409552003509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200019826964725606368002339 300029740447088409552003509)
      ·
        refine ⟨28127788166914538395500329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 300029740447088409552003509 28127788166914538395500329)
        ·
          refine ⟨21095841125185903796625247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28127788166914538395500329 21095841125185903796625247)
          ·
            refine ⟨31643761687778855694937871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21095841125185903796625247 31643761687778855694937871)
            ·
              refine ⟨47465642531668283542406807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31643761687778855694937871 47465642531668283542406807)
              ·
                refine ⟨71198463797502425313610211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47465642531668283542406807 71198463797502425313610211)
                ·
                  refine ⟨106797695696253637970415317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71198463797502425313610211 106797695696253637970415317)
                  ·
                    refine ⟨2503070992880944639931609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 106797695696253637970415317 2503070992880944639931609)
                    ·
                      refine ⟨1877303244660708479948707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2503070992880944639931609 1877303244660708479948707)
                      ·
                        rfl

theorem cell23_3656035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_3656035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656035 prefixEnd_3656035 := by exact prefixLift 3656035
  have htrace : WordTrace (prefixWord ++ tailWord_3656035) baseStart_3656035 baseEnd_3656035 := by
    simpa [prefixWord, tailWord_3656035, baseEnd_3656035] using wordTrace_append hprefix tailTrace_3656035
  have hstable : (prefixWord ++ tailWord_3656035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656035).length < 2 ^ (prefixWord ++ tailWord_3656035).sum := by decide
  have hdescent : baseEnd_3656035 < baseStart_3656035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656042 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3656042 : Nat := 118140960795 + 3656042 * 2 ^ 59
def prefixEnd_3656042 : Nat := 4983230072969 + 3 ^ 40 * 3656042 * 2
def baseEnd_3656042 : Nat := 1877306839025289952561175

theorem tailTrace_3656042 : CollatzResearch.WordTrace tailWord_3656042 prefixEnd_3656042 1877306839025289952561175 := by
  unfold tailWord_3656042
  simp only [CollatzResearch.WordTrace]
  refine ⟨33336701655197927776876595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88897871080527807405004253 33336701655197927776876595)
  ·
    refine ⟨50005052482796891665314893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33336701655197927776876595 50005052482796891665314893)
    ·
      refine ⟨18751894681048834374493085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50005052482796891665314893 18751894681048834374493085)
      ·
        refine ⟨7031960505393312890434907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18751894681048834374493085 7031960505393312890434907)
        ·
          refine ⟨10547940758089969335652361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7031960505393312890434907 10547940758089969335652361)
          ·
            refine ⟨7910955568567477001739271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10547940758089969335652361 7910955568567477001739271)
            ·
              refine ⟨11866433352851215502608907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7910955568567477001739271 11866433352851215502608907)
              ·
                refine ⟨17799650029276823253913361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11866433352851215502608907 17799650029276823253913361)
                ·
                  refine ⟨13349737521957617440435021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17799650029276823253913361 13349737521957617440435021)
                  ·
                    refine ⟨5006151570734106540163133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13349737521957617440435021 5006151570734106540163133)
                    ·
                      refine ⟨1877306839025289952561175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5006151570734106540163133 1877306839025289952561175)
                      ·
                        rfl

theorem cell23_3656042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3656042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656042 prefixEnd_3656042 := by exact prefixLift 3656042
  have htrace : WordTrace (prefixWord ++ tailWord_3656042) baseStart_3656042 baseEnd_3656042 := by
    simpa [prefixWord, tailWord_3656042, baseEnd_3656042] using wordTrace_append hprefix tailTrace_3656042
  have hstable : (prefixWord ++ tailWord_3656042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656042).length < 2 ^ (prefixWord ++ tailWord_3656042).sum := by decide
  have hdescent : baseEnd_3656042 < baseStart_3656042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656066 : List Nat := [3, 4, 2, 1, 2, 1, 2, 3, 5]
def baseStart_3656066 : Nat := 118140960795 + 3656066 * 2 ^ 59
def prefixEnd_3656066 : Nat := 4983230072969 + 3 ^ 40 * 3656066 * 2
def baseEnd_3656066 : Nat := 208591018062333095406785

theorem tailTrace_3656066 : CollatzResearch.WordTrace tailWord_3656066 prefixEnd_3656066 208591018062333095406785 := by
  unfold tailWord_3656066
  simp only [CollatzResearch.WordTrace]
  refine ⟨33336920493176190801595013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88898454648469842137586701 33336920493176190801595013)
  ·
    refine ⟨6250672592470535775299065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33336920493176190801595013 6250672592470535775299065)
    ·
      refine ⟨4688004444352901831474299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6250672592470535775299065 4688004444352901831474299)
      ·
        refine ⟨7032006666529352747211449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4688004444352901831474299 7032006666529352747211449)
        ·
          refine ⟨5274004999897014560408587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7032006666529352747211449 5274004999897014560408587)
          ·
            refine ⟨7911007499845521840612881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5274004999897014560408587 7911007499845521840612881)
            ·
              refine ⟨5933255624884141380459661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7911007499845521840612881 5933255624884141380459661)
              ·
                refine ⟨2224970859331553017672373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5933255624884141380459661 2224970859331553017672373)
                ·
                  refine ⟨208591018062333095406785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2224970859331553017672373 208591018062333095406785)
                  ·
                    rfl

theorem cell23_3656066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_3656066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656066 prefixEnd_3656066 := by exact prefixLift 3656066
  have htrace : WordTrace (prefixWord ++ tailWord_3656066) baseStart_3656066 baseEnd_3656066 := by
    simpa [prefixWord, tailWord_3656066, baseEnd_3656066] using wordTrace_append hprefix tailTrace_3656066
  have hstable : (prefixWord ++ tailWord_3656066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656066).length < 2 ^ (prefixWord ++ tailWord_3656066).sum := by decide
  have hdescent : baseEnd_3656066 < baseStart_3656066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656085 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_3656085 : Nat := 118140960795 + 3656085 * 2 ^ 59
def prefixEnd_3656085 : Nat := 4983230072969 + 3 ^ 40 * 3656085 * 2
def baseEnd_3656085 : Nat := 1877328918693433284323477

theorem tailTrace_3656085 : CollatzResearch.WordTrace tailWord_3656085 prefixEnd_3656085 1877328918693433284323477 := by
  unfold tailWord_3656085
  simp only [CollatzResearch.WordTrace]
  refine ⟨133348374959635929451321709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88898916639757286300881139 133348374959635929451321709)
  ·
    refine ⟨50005640609863473544245641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133348374959635929451321709 50005640609863473544245641)
    ·
      refine ⟨37504230457397605158184231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50005640609863473544245641 37504230457397605158184231)
      ·
        refine ⟨56256345686096407737276347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37504230457397605158184231 56256345686096407737276347)
        ·
          refine ⟨84384518529144611605914521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56256345686096407737276347 84384518529144611605914521)
          ·
            refine ⟨63288388896858458704435891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84384518529144611605914521 63288388896858458704435891)
            ·
              refine ⟨94932583345287688056653837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63288388896858458704435891 94932583345287688056653837)
              ·
                refine ⟨35599718754482883021245189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94932583345287688056653837 35599718754482883021245189)
                ·
                  refine ⟨6674947266465540566483473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35599718754482883021245189 6674947266465540566483473)
                  ·
                    refine ⟨5006210449849155424862605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6674947266465540566483473 5006210449849155424862605)
                    ·
                      refine ⟨1877328918693433284323477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5006210449849155424862605 1877328918693433284323477)
                      ·
                        rfl

theorem cell23_3656085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_3656085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656085 prefixEnd_3656085 := by exact prefixLift 3656085
  have htrace : WordTrace (prefixWord ++ tailWord_3656085) baseStart_3656085 baseEnd_3656085 := by
    simpa [prefixWord, tailWord_3656085, baseEnd_3656085] using wordTrace_append hprefix tailTrace_3656085
  have hstable : (prefixWord ++ tailWord_3656085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656085).length < 2 ^ (prefixWord ++ tailWord_3656085).sum := by decide
  have hdescent : baseEnd_3656085 < baseStart_3656085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656108 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_3656108 : Nat := 118140960795 + 3656108 * 2 ^ 59
def prefixEnd_3656108 : Nat := 4983230072969 + 3 ^ 40 * 3656108 * 2
def baseEnd_3656108 : Nat := 1877340728748486694335871

theorem tailTrace_3656108 : CollatzResearch.WordTrace tailWord_3656108 prefixEnd_3656108 1877340728748486694335871 := by
  unfold tailWord_3656108
  simp only [CollatzResearch.WordTrace]
  refine ⟨66674606919276302189704489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88899475892368402919605985 66674606919276302189704489)
  ·
    refine ⟨50005955189457226642278367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66674606919276302189704489 50005955189457226642278367)
    ·
      refine ⟨75008932784185839963417551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50005955189457226642278367 75008932784185839963417551)
      ·
        refine ⟨112513399176278759945126327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75008932784185839963417551 112513399176278759945126327)
        ·
          refine ⟨168770098764418139917689491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112513399176278759945126327 168770098764418139917689491)
          ·
            refine ⟨253155148146627209876534237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168770098764418139917689491 253155148146627209876534237)
            ·
              refine ⟨94933180554985203703700339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253155148146627209876534237 94933180554985203703700339)
              ·
                refine ⟨142399770832477805555550509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94933180554985203703700339 142399770832477805555550509)
                ·
                  refine ⟨53399914062179177083331441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142399770832477805555550509 53399914062179177083331441)
                  ·
                    refine ⟨40049935546634382812498581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53399914062179177083331441 40049935546634382812498581)
                    ·
                      refine ⟨1877340728748486694335871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40049935546634382812498581 1877340728748486694335871)
                      ·
                        rfl

theorem cell23_3656108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_3656108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656108 prefixEnd_3656108 := by exact prefixLift 3656108
  have htrace : WordTrace (prefixWord ++ tailWord_3656108) baseStart_3656108 baseEnd_3656108 := by
    simpa [prefixWord, tailWord_3656108, baseEnd_3656108] using wordTrace_append hprefix tailTrace_3656108
  have hstable : (prefixWord ++ tailWord_3656108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656108).length < 2 ^ (prefixWord ++ tailWord_3656108).sum := by decide
  have hdescent : baseEnd_3656108 < baseStart_3656108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656149 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_3656149 : Nat := 118140960795 + 3656149 * 2 ^ 59
def prefixEnd_3656149 : Nat := 4983230072969 + 3 ^ 40 * 3656149 * 2
def baseEnd_3656149 : Nat := 1877361781455321033923183

theorem tailTrace_3656149 : CollatzResearch.WordTrace tailWord_3656149 prefixEnd_3656149 1877361781455321033923183 := by
  unfold tailWord_3656149
  simp only [CollatzResearch.WordTrace]
  refine ⟨133350709231404068381651501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88900472820936045587767667 133350709231404068381651501)
  ·
    refine ⟨50006515961776525643119313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133350709231404068381651501 50006515961776525643119313)
    ·
      refine ⟨37504886971332394232339485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50006515961776525643119313 37504886971332394232339485)
      ·
        refine ⟨14064332614249647837127307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37504886971332394232339485 14064332614249647837127307)
        ·
          refine ⟨21096498921374471755690961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14064332614249647837127307 21096498921374471755690961)
          ·
            refine ⟨15822374191030853816768221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21096498921374471755690961 15822374191030853816768221)
            ·
              refine ⟨5933390321636570181288083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15822374191030853816768221 5933390321636570181288083)
              ·
                refine ⟨8900085482454855271932125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5933390321636570181288083 8900085482454855271932125)
                ·
                  refine ⟨3337532055920570726974547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8900085482454855271932125 3337532055920570726974547)
                  ·
                    refine ⟨5006298083880856090461821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3337532055920570726974547 5006298083880856090461821)
                    ·
                      refine ⟨1877361781455321033923183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5006298083880856090461821 1877361781455321033923183)
                      ·
                        rfl

theorem cell23_3656149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_3656149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656149 prefixEnd_3656149 := by exact prefixLift 3656149
  have htrace : WordTrace (prefixWord ++ tailWord_3656149) baseStart_3656149 baseEnd_3656149 := by
    simpa [prefixWord, tailWord_3656149, baseEnd_3656149] using wordTrace_append hprefix tailTrace_3656149
  have hstable : (prefixWord ++ tailWord_3656149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656149).length < 2 ^ (prefixWord ++ tailWord_3656149).sum := by decide
  have hdescent : baseEnd_3656149 < baseStart_3656149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656182 : List Nat := [5, 1, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_3656182 : Nat := 118140960795 + 3656182 * 2 ^ 59
def prefixEnd_3656182 : Nat := 4983230072969 + 3 ^ 40 * 3656182 * 2
def baseEnd_3656182 : Nat := 625792908772306468270177

theorem tailTrace_3656182 : CollatzResearch.WordTrace tailWord_3656182 prefixEnd_3656182 625792908772306468270177 := by
  unfold tailWord_3656182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8334494552517782188600175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88901275226856343345068533 8334494552517782188600175)
  ·
    refine ⟨12501741828776673282900263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8334494552517782188600175 12501741828776673282900263)
    ·
      refine ⟨18752612743165009924350395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12501741828776673282900263 18752612743165009924350395)
      ·
        refine ⟨28128919114747514886525593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18752612743165009924350395 28128919114747514886525593)
        ·
          refine ⟨21096689336060636164894195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28128919114747514886525593 21096689336060636164894195)
          ·
            refine ⟨31645034004090954247341293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21096689336060636164894195 31645034004090954247341293)
            ·
              refine ⟨11866887751534107842752985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31645034004090954247341293 11866887751534107842752985)
              ·
                refine ⟨8900165813650580882064739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11866887751534107842752985 8900165813650580882064739)
                ·
                  refine ⟨13350248720475871323097109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8900165813650580882064739 13350248720475871323097109)
                  ·
                    refine ⟨625792908772306468270177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13350248720475871323097109 625792908772306468270177)
                    ·
                      rfl

theorem cell23_3656182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_3656182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656182 prefixEnd_3656182 := by exact prefixLift 3656182
  have htrace : WordTrace (prefixWord ++ tailWord_3656182) baseStart_3656182 baseEnd_3656182 := by
    simpa [prefixWord, tailWord_3656182, baseEnd_3656182] using wordTrace_append hprefix tailTrace_3656182
  have hstable : (prefixWord ++ tailWord_3656182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656182).length < 2 ^ (prefixWord ++ tailWord_3656182).sum := by decide
  have hdescent : baseEnd_3656182 < baseStart_3656182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656185 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 4]
def baseStart_3656185 : Nat := 118140960795 + 3656185 * 2 ^ 59
def prefixEnd_3656185 : Nat := 4983230072969 + 3 ^ 40 * 3656185 * 2
def baseEnd_3656185 : Nat := 1877380266758882893073017

theorem tailTrace_3656185 : CollatzResearch.WordTrace tailWord_3656185 prefixEnd_3656185 1877380266758882893073017 := by
  unfold tailWord_3656185
  simp only [CollatzResearch.WordTrace]
  refine ⟨133352022259273646529962009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88901348172849097686641339 133352022259273646529962009)
  ·
    refine ⟨100014016694455234897471507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133352022259273646529962009 100014016694455234897471507)
    ·
      refine ⟨150021025041682852346207261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100014016694455234897471507 150021025041682852346207261)
      ·
        refine ⟨56257884390631069629827723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150021025041682852346207261 56257884390631069629827723)
        ·
          refine ⟨84386826585946604444741585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56257884390631069629827723 84386826585946604444741585)
          ·
            refine ⟨63290119939459953333556189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84386826585946604444741585 63290119939459953333556189)
            ·
              refine ⟨23733794977297482500083571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63290119939459953333556189 23733794977297482500083571)
              ·
                refine ⟨35600692465946223750125357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23733794977297482500083571 35600692465946223750125357)
                ·
                  refine ⟨13350259674729833906297009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35600692465946223750125357 13350259674729833906297009)
                  ·
                    refine ⟨10012694756047375429722757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13350259674729833906297009 10012694756047375429722757)
                    ·
                      refine ⟨1877380266758882893073017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10012694756047375429722757 1877380266758882893073017)
                      ·
                        rfl

theorem cell23_3656185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_3656185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656185 prefixEnd_3656185 := by exact prefixLift 3656185
  have htrace : WordTrace (prefixWord ++ tailWord_3656185) baseStart_3656185 baseEnd_3656185 := by
    simpa [prefixWord, tailWord_3656185, baseEnd_3656185] using wordTrace_append hprefix tailTrace_3656185
  have hstable : (prefixWord ++ tailWord_3656185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656185).length < 2 ^ (prefixWord ++ tailWord_3656185).sum := by decide
  have hdescent : baseEnd_3656185 < baseStart_3656185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656189 : List Nat := [1, 4, 1, 1, 1, 3, 5, 1, 1, 1, 4]
def baseStart_3656189 : Nat := 118140960795 + 3656189 * 2 ^ 59
def prefixEnd_3656189 : Nat := 4983230072969 + 3 ^ 40 * 3656189 * 2
def baseEnd_3656189 : Nat := 1877382320681500877422999

theorem tailTrace_3656189 : CollatzResearch.WordTrace tailWord_3656189 prefixEnd_3656189 1877382320681500877422999 := by
  unfold tailWord_3656189
  simp only [CollatzResearch.WordTrace]
  refine ⟨133352168151259155213107621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88901445434172770142071747 133352168151259155213107621)
  ·
    refine ⟨25003531528361091602457679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133352168151259155213107621 25003531528361091602457679)
    ·
      refine ⟨37505297292541637403686519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25003531528361091602457679 37505297292541637403686519)
      ·
        refine ⟨56257945938812456105529779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37505297292541637403686519 56257945938812456105529779)
        ·
          refine ⟨84386918908218684158294669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56257945938812456105529779 84386918908218684158294669)
          ·
            refine ⟨31645094590582006559360501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84386918908218684158294669 31645094590582006559360501)
            ·
              refine ⟨2966727617867063114940047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31645094590582006559360501 2966727617867063114940047)
              ·
                refine ⟨4450091426800594672410071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966727617867063114940047 4450091426800594672410071)
                ·
                  refine ⟨6675137140200892008615107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450091426800594672410071 6675137140200892008615107)
                  ·
                    refine ⟨10012705710301338012922661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6675137140200892008615107 10012705710301338012922661)
                    ·
                      refine ⟨1877382320681500877422999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10012705710301338012922661 1877382320681500877422999)
                      ·
                        rfl

theorem cell23_3656189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_3656189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656189 prefixEnd_3656189 := by exact prefixLift 3656189
  have htrace : WordTrace (prefixWord ++ tailWord_3656189) baseStart_3656189 baseEnd_3656189 := by
    simpa [prefixWord, tailWord_3656189, baseEnd_3656189] using wordTrace_append hprefix tailTrace_3656189
  have hstable : (prefixWord ++ tailWord_3656189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656189).length < 2 ^ (prefixWord ++ tailWord_3656189).sum := by decide
  have hdescent : baseEnd_3656189 < baseStart_3656189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656225 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 2, 7]
def baseStart_3656225 : Nat := 118140960795 + 3656225 * 2 ^ 59
def prefixEnd_3656225 : Nat := 4983230072969 + 3 ^ 40 * 3656225 * 2
def baseEnd_3656225 : Nat := 625800268661687578857611

theorem tailTrace_3656225 : CollatzResearch.WordTrace tailWord_3656225 prefixEnd_3656225 625800268661687578857611 := by
  unfold tailWord_3656225
  simp only [CollatzResearch.WordTrace]
  refine ⟨133353481179128733361418129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88902320786085822240945419 133353481179128733361418129)
  ·
    refine ⟨100015110884346550021063597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133353481179128733361418129 100015110884346550021063597)
    ·
      refine ⟨37505666581629956257898849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100015110884346550021063597 37505666581629956257898849)
      ·
        refine ⟨28129249936222467193424137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37505666581629956257898849 28129249936222467193424137)
        ·
          refine ⟨21096937452166850395068103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28129249936222467193424137 21096937452166850395068103)
          ·
            refine ⟨31645406178250275592602155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21096937452166850395068103 31645406178250275592602155)
            ·
              refine ⟨47468109267375413388903233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31645406178250275592602155 47468109267375413388903233)
              ·
                refine ⟨35601081950531560041677425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47468109267375413388903233 35601081950531560041677425)
                ·
                  refine ⟨26700811462898670031258069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35601081950531560041677425 26700811462898670031258069)
                  ·
                    refine ⟨625800268661687578857611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26700811462898670031258069 625800268661687578857611)
                    ·
                      rfl

theorem cell23_3656225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_3656225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656225 prefixEnd_3656225 := by exact prefixLift 3656225
  have htrace : WordTrace (prefixWord ++ tailWord_3656225) baseStart_3656225 baseEnd_3656225 := by
    simpa [prefixWord, tailWord_3656225, baseEnd_3656225] using wordTrace_append hprefix tailTrace_3656225
  have hstable : (prefixWord ++ tailWord_3656225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656225).length < 2 ^ (prefixWord ++ tailWord_3656225).sum := by decide
  have hdescent : baseEnd_3656225 < baseStart_3656225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656237 : List Nat := [1, 5, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3656237 : Nat := 118140960795 + 3656237 * 2 ^ 59
def prefixEnd_3656237 : Nat := 4983230072969 + 3 ^ 40 * 3656237 * 2
def baseEnd_3656237 : Nat := 625802322584305563207593

theorem tailTrace_3656237 : CollatzResearch.WordTrace tailWord_3656237 prefixEnd_3656237 625802322584305563207593 := by
  unfold tailWord_3656237
  simp only [CollatzResearch.WordTrace]
  refine ⟨133353918855085259410854965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88902612570056839607236643 133353918855085259410854965)
  ·
    refine ⟨12501929892664243069767653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133353918855085259410854965 12501929892664243069767653)
    ·
      refine ⟨2344111854874545575581435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12501929892664243069767653 2344111854874545575581435)
      ·
        refine ⟨3516167782311818363372153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2344111854874545575581435 3516167782311818363372153)
        ·
          refine ⟨2637125836733863772529115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3516167782311818363372153 2637125836733863772529115)
          ·
            refine ⟨3955688755100795658793673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637125836733863772529115 3955688755100795658793673)
            ·
              refine ⟨2966766566325596744095255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3955688755100795658793673 2966766566325596744095255)
              ·
                refine ⟨4450149849488395116142883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2966766566325596744095255 4450149849488395116142883)
                ·
                  refine ⟨6675224774232592674214325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450149849488395116142883 6675224774232592674214325)
                  ·
                    refine ⟨625802322584305563207593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6675224774232592674214325 625802322584305563207593)
                    ·
                      rfl

theorem cell23_3656237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3656237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656237 prefixEnd_3656237 := by exact prefixLift 3656237
  have htrace : WordTrace (prefixWord ++ tailWord_3656237) baseStart_3656237 baseEnd_3656237 := by
    simpa [prefixWord, tailWord_3656237, baseEnd_3656237] using wordTrace_append hprefix tailTrace_3656237
  have hstable : (prefixWord ++ tailWord_3656237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656237).length < 2 ^ (prefixWord ++ tailWord_3656237).sum := by decide
  have hdescent : baseEnd_3656237 < baseStart_3656237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656255 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 4, 6]
def baseStart_3656255 : Nat := 118140960795 + 3656255 * 2 ^ 59
def prefixEnd_3656255 : Nat := 4983230072969 + 3 ^ 40 * 3656255 * 2
def baseEnd_3656255 : Nat := 625805403468232539732565

theorem tailTrace_3656255 : CollatzResearch.WordTrace tailWord_3656255 prefixEnd_3656255 625805403468232539732565 := by
  unfold tailWord_3656255
  simp only [CollatzResearch.WordTrace]
  refine ⟨133354575369020048485010219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88903050246013365656673479 133354575369020048485010219)
  ·
    refine ⟨200031863053530072727515329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133354575369020048485010219 200031863053530072727515329)
    ·
      refine ⟨150023897290147554545636497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200031863053530072727515329 150023897290147554545636497)
      ·
        refine ⟨112517922967610665909227373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150023897290147554545636497 112517922967610665909227373)
        ·
          refine ⟨42194221112853999715960265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112517922967610665909227373 42194221112853999715960265)
          ·
            refine ⟨31645665834640499786970199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42194221112853999715960265 31645665834640499786970199)
            ·
              refine ⟨47468498751960749680455299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31645665834640499786970199 47468498751960749680455299)
              ·
                refine ⟨71202748127941124520682949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47468498751960749680455299 71202748127941124520682949)
                ·
                  refine ⟨13350515273988960847628053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71202748127941124520682949 13350515273988960847628053)
                  ·
                    refine ⟨625805403468232539732565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13350515273988960847628053 625805403468232539732565)
                    ·
                      rfl

theorem cell23_3656255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_3656255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656255 prefixEnd_3656255 := by exact prefixLift 3656255
  have htrace : WordTrace (prefixWord ++ tailWord_3656255) baseStart_3656255 baseEnd_3656255 := by
    simpa [prefixWord, tailWord_3656255, baseEnd_3656255] using wordTrace_append hprefix tailTrace_3656255
  have hstable : (prefixWord ++ tailWord_3656255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656255).length < 2 ^ (prefixWord ++ tailWord_3656255).sum := by decide
  have hdescent : baseEnd_3656255 < baseStart_3656255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656265 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 5]
def baseStart_3656265 : Nat := 118140960795 + 3656265 * 2 ^ 59
def prefixEnd_3656265 : Nat := 4983230072969 + 3 ^ 40 * 3656265 * 2
def baseEnd_3656265 : Nat := 1877421345211242580072649

theorem tailTrace_3656265 : CollatzResearch.WordTrace tailWord_3656265 prefixEnd_3656265 1877421345211242580072649 := by
  unfold tailWord_3656265
  simp only [CollatzResearch.WordTrace]
  refine ⟨133354940098983820192874249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88903293399322546795249499 133354940098983820192874249)
  ·
    refine ⟨100016205074237865144655687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133354940098983820192874249 100016205074237865144655687)
    ·
      refine ⟨150024307611356797716983531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100016205074237865144655687 150024307611356797716983531)
      ·
        refine ⟨225036461417035196575475297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150024307611356797716983531 225036461417035196575475297)
        ·
          refine ⟨168777346062776397431606473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225036461417035196575475297 168777346062776397431606473)
          ·
            refine ⟨126583009547082298073704855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168777346062776397431606473 126583009547082298073704855)
            ·
              refine ⟨189874514320623447110557283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126583009547082298073704855 189874514320623447110557283)
              ·
                refine ⟨284811771480935170665835925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189874514320623447110557283 284811771480935170665835925)
                ·
                  refine ⟨13350551788168836124961059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 284811771480935170665835925 13350551788168836124961059)
                  ·
                    refine ⟨20025827682253254187441589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13350551788168836124961059 20025827682253254187441589)
                    ·
                      refine ⟨1877421345211242580072649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20025827682253254187441589 1877421345211242580072649)
                      ·
                        rfl

theorem cell23_3656265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_3656265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656265 prefixEnd_3656265 := by exact prefixLift 3656265
  have htrace : WordTrace (prefixWord ++ tailWord_3656265) baseStart_3656265 baseEnd_3656265 := by
    simpa [prefixWord, tailWord_3656265, baseEnd_3656265] using wordTrace_append hprefix tailTrace_3656265
  have hstable : (prefixWord ++ tailWord_3656265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656265).length < 2 ^ (prefixWord ++ tailWord_3656265).sum := by decide
  have hdescent : baseEnd_3656265 < baseStart_3656265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656305 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_3656305 : Nat := 118140960795 + 3656305 * 2 ^ 59
def prefixEnd_3656305 : Nat := 4983230072969 + 3 ^ 40 * 3656305 * 2
def baseEnd_3656305 : Nat := 1877441884437422423572465

theorem tailTrace_3656305 : CollatzResearch.WordTrace tailWord_3656305 prefixEnd_3656305 1877441884437422423572465 := by
  unfold tailWord_3656305
  simp only [CollatzResearch.WordTrace]
  refine ⟨133356399018838907024330369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88904266012559271349553579 133356399018838907024330369)
  ·
    refine ⟨100017299264129180268247777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133356399018838907024330369 100017299264129180268247777)
    ·
      refine ⟨75012974448096885201185833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100017299264129180268247777 75012974448096885201185833)
      ·
        refine ⟨56259730836072663900889375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75012974448096885201185833 56259730836072663900889375)
        ·
          refine ⟨84389596254108995851334063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56259730836072663900889375 84389596254108995851334063)
          ·
            refine ⟨126584394381163493777001095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84389596254108995851334063 126584394381163493777001095)
            ·
              refine ⟨189876591571745240665501643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126584394381163493777001095 189876591571745240665501643)
              ·
                refine ⟨284814887357617860998252465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189876591571745240665501643 284814887357617860998252465)
                ·
                  refine ⟨213611165518213395748689349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284814887357617860998252465 213611165518213395748689349)
                  ·
                    refine ⟨40052093534665011702879253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 213611165518213395748689349 40052093534665011702879253)
                    ·
                      refine ⟨1877441884437422423572465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40052093534665011702879253 1877441884437422423572465)
                      ·
                        rfl

theorem cell23_3656305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_3656305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656305 prefixEnd_3656305 := by exact prefixLift 3656305
  have htrace : WordTrace (prefixWord ++ tailWord_3656305) baseStart_3656305 baseEnd_3656305 := by
    simpa [prefixWord, tailWord_3656305, baseEnd_3656305] using wordTrace_append hprefix tailTrace_3656305
  have hstable : (prefixWord ++ tailWord_3656305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656305).length < 2 ^ (prefixWord ++ tailWord_3656305).sum := by decide
  have hdescent : baseEnd_3656305 < baseStart_3656305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656315 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 3, 7]
def baseStart_3656315 : Nat := 118140960795 + 3656315 * 2 ^ 59
def prefixEnd_3656315 : Nat := 4983230072969 + 3 ^ 40 * 3656315 * 2
def baseEnd_3656315 : Nat := 625815673081322461482473

theorem tailTrace_3656315 : CollatzResearch.WordTrace tailWord_3656315 prefixEnd_3656315 625815673081322461482473 := by
  unfold tailWord_3656315
  simp only [CollatzResearch.WordTrace]
  refine ⟨133356763748802678732194399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88904509165868452488129599 133356763748802678732194399)
  ·
    refine ⟨200035145623204018098291599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133356763748802678732194399 200035145623204018098291599)
    ·
      refine ⟨300052718434806027147437399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200035145623204018098291599 300052718434806027147437399)
      ·
        refine ⟨450079077652209040721156099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300052718434806027147437399 450079077652209040721156099)
        ·
          refine ⟨675118616478313561081734149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450079077652209040721156099 675118616478313561081734149)
          ·
            refine ⟨126584740589683792702825153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 675118616478313561081734149 126584740589683792702825153)
            ·
              refine ⟨94938555442262844527118865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126584740589683792702825153 94938555442262844527118865)
              ·
                refine ⟨71203916581697133395339149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94938555442262844527118865 71203916581697133395339149)
                ·
                  refine ⟨26701468718136425023252181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71203916581697133395339149 26701468718136425023252181)
                  ·
                    refine ⟨625815673081322461482473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26701468718136425023252181 625815673081322461482473)
                    ·
                      rfl

theorem cell23_3656315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 7].length) (baseStart_3656315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656315 prefixEnd_3656315 := by exact prefixLift 3656315
  have htrace : WordTrace (prefixWord ++ tailWord_3656315) baseStart_3656315 baseEnd_3656315 := by
    simpa [prefixWord, tailWord_3656315, baseEnd_3656315] using wordTrace_append hprefix tailTrace_3656315
  have hstable : (prefixWord ++ tailWord_3656315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656315).length < 2 ^ (prefixWord ++ tailWord_3656315).sum := by decide
  have hdescent : baseEnd_3656315 < baseStart_3656315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656366 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3656366 : Nat := 118140960795 + 3656366 * 2 ^ 59
def prefixEnd_3656366 : Nat := 4983230072969 + 3 ^ 40 * 3656366 * 2
def baseEnd_3656366 : Nat := 625824402252448894969895

theorem tailTrace_3656366 : CollatzResearch.WordTrace tailWord_3656366 prefixEnd_3656366 625824402252448894969895 := by
  unfold tailWord_3656366
  simp only [CollatzResearch.WordTrace]
  refine ⟨16669827983952239305287619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88905749247745276294867301 16669827983952239305287619)
  ·
    refine ⟨25004741975928358957931429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16669827983952239305287619 25004741975928358957931429)
    ·
      refine ⟨4688389120486567304612143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25004741975928358957931429 4688389120486567304612143)
      ·
        refine ⟨7032583680729850956918215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4688389120486567304612143 7032583680729850956918215)
        ·
          refine ⟨10548875521094776435377323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7032583680729850956918215 10548875521094776435377323)
          ·
            refine ⟨15823313281642164653065985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10548875521094776435377323 15823313281642164653065985)
            ·
              refine ⟨11867484961231623489799489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15823313281642164653065985 11867484961231623489799489)
              ·
                refine ⟨8900613720923717617349617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11867484961231623489799489 8900613720923717617349617)
                ·
                  refine ⟨6675460290692788213012213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8900613720923717617349617 6675460290692788213012213)
                  ·
                    refine ⟨625824402252448894969895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6675460290692788213012213 625824402252448894969895)
                    ·
                      rfl

theorem cell23_3656366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3656366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656366 prefixEnd_3656366 := by exact prefixLift 3656366
  have htrace : WordTrace (prefixWord ++ tailWord_3656366) baseStart_3656366 baseEnd_3656366 := by
    simpa [prefixWord, tailWord_3656366, baseEnd_3656366] using wordTrace_append hprefix tailTrace_3656366
  have hstable : (prefixWord ++ tailWord_3656366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656366).length < 2 ^ (prefixWord ++ tailWord_3656366).sum := by decide
  have hdescent : baseEnd_3656366 < baseStart_3656366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656396 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 3, 4]
def baseStart_3656396 : Nat := 118140960795 + 3656396 * 2 ^ 59
def prefixEnd_3656396 : Nat := 4983230072969 + 3 ^ 40 * 3656396 * 2
def baseEnd_3656396 : Nat := 625829537058993855844849

theorem tailTrace_3656396 : CollatzResearch.WordTrace tailWord_3656396 prefixEnd_3656396 625829537058993855844849 := by
  unfold tailWord_3656396
  simp only [CollatzResearch.WordTrace]
  refine ⟨66679859030754614782946521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88906478707672819710595361 66679859030754614782946521)
  ·
    refine ⟨50009894273065961087209891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66679859030754614782946521 50009894273065961087209891)
    ·
      refine ⟨75014841409598941630814837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50009894273065961087209891 75014841409598941630814837)
      ·
        refine ⟨7032641382149900777888891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75014841409598941630814837 7032641382149900777888891)
        ·
          refine ⟨10548962073224851166833337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7032641382149900777888891 10548962073224851166833337)
          ·
            refine ⟨7911721554918638375125003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10548962073224851166833337 7911721554918638375125003)
            ·
              refine ⟨11867582332377957562687505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7911721554918638375125003 11867582332377957562687505)
              ·
                refine ⟨8900686749283468172015629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11867582332377957562687505 8900686749283468172015629)
                ·
                  refine ⟨3337757530981300564505861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8900686749283468172015629 3337757530981300564505861)
                  ·
                    refine ⟨625829537058993855844849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3337757530981300564505861 625829537058993855844849)
                    ·
                      rfl

theorem cell23_3656396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_3656396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656396 prefixEnd_3656396 := by exact prefixLift 3656396
  have htrace : WordTrace (prefixWord ++ tailWord_3656396) baseStart_3656396 baseEnd_3656396 := by
    simpa [prefixWord, tailWord_3656396, baseEnd_3656396] using wordTrace_append hprefix tailTrace_3656396
  have hstable : (prefixWord ++ tailWord_3656396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656396).length < 2 ^ (prefixWord ++ tailWord_3656396).sum := by decide
  have hdescent : baseEnd_3656396 < baseStart_3656396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656456 : List Nat := [2, 1, 3, 2, 2, 3, 2, 2, 1, 5]
def baseStart_3656456 : Nat := 118140960795 + 3656456 * 2 ^ 59
def prefixEnd_3656456 : Nat := 4983230072969 + 3 ^ 40 * 3656456 * 2
def baseEnd_3656456 : Nat := 625839806672083777594757

theorem tailTrace_3656456 : CollatzResearch.WordTrace tailWord_3656456 prefixEnd_3656456 625839806672083777594757 := by
  unfold tailWord_3656456
  simp only [CollatzResearch.WordTrace]
  refine ⟨66680953220645929906538611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88907937627527906542051481 66680953220645929906538611)
  ·
    refine ⟨100021429830968894859807917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66680953220645929906538611 100021429830968894859807917)
    ·
      refine ⟨37508036186613335572427969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100021429830968894859807917 37508036186613335572427969)
      ·
        refine ⟨28131027139960001679320977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37508036186613335572427969 28131027139960001679320977)
        ·
          refine ⟨21098270354970001259490733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28131027139960001679320977 21098270354970001259490733)
          ·
            refine ⟨7911851383113750472309025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21098270354970001259490733 7911851383113750472309025)
            ·
              refine ⟨5933888537335312854231769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7911851383113750472309025 5933888537335312854231769)
              ·
                refine ⟨4450416403001484640673827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5933888537335312854231769 4450416403001484640673827)
                ·
                  refine ⟨6675624604502226961010741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450416403001484640673827 6675624604502226961010741)
                  ·
                    refine ⟨625839806672083777594757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6675624604502226961010741 625839806672083777594757)
                    ·
                      rfl

theorem cell23_3656456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_3656456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656456 prefixEnd_3656456 := by exact prefixLift 3656456
  have htrace : WordTrace (prefixWord ++ tailWord_3656456) baseStart_3656456 baseEnd_3656456 := by
    simpa [prefixWord, tailWord_3656456, baseEnd_3656456] using wordTrace_append hprefix tailTrace_3656456
  have hstable : (prefixWord ++ tailWord_3656456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656456).length < 2 ^ (prefixWord ++ tailWord_3656456).sum := by decide
  have hdescent : baseEnd_3656456 < baseStart_3656456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656459 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 1, 8, 2]
def baseStart_3656459 : Nat := 118140960795 + 3656459 * 2 ^ 59
def prefixEnd_3656459 : Nat := 4983230072969 + 3 ^ 40 * 3656459 * 2
def baseEnd_3656459 : Nat := 1877520960458214821046757

theorem tailTrace_3656459 : CollatzResearch.WordTrace tailWord_3656459 prefixEnd_3656459 1877520960458214821046757 := by
  unfold tailWord_3656459
  simp only [CollatzResearch.WordTrace]
  refine ⟨133362015860280991325436431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88908010573520660883624287 133362015860280991325436431)
  ·
    refine ⟨200043023790421486988154647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133362015860280991325436431 200043023790421486988154647)
    ·
      refine ⟨300064535685632230482231971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200043023790421486988154647 300064535685632230482231971)
      ·
        refine ⟨450096803528448345723347957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300064535685632230482231971 450096803528448345723347957)
        ·
          refine ⟨42196575330792032411563871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 450096803528448345723347957 42196575330792032411563871)
          ·
            refine ⟨63294862996188048617345807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42196575330792032411563871 63294862996188048617345807)
            ·
              refine ⟨94942294494282072926018711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63294862996188048617345807 94942294494282072926018711)
              ·
                refine ⟨142413441741423109389028067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94942294494282072926018711 142413441741423109389028067)
                ·
                  refine ⟨213620162612134664083542101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142413441741423109389028067 213620162612134664083542101)
                  ·
                    refine ⟨2503361280610953094729009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 213620162612134664083542101 2503361280610953094729009)
                    ·
                      refine ⟨1877520960458214821046757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2503361280610953094729009 1877520960458214821046757)
                      ·
                        rfl

theorem cell23_3656459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 8, 2].length) (baseStart_3656459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656459 prefixEnd_3656459 := by exact prefixLift 3656459
  have htrace : WordTrace (prefixWord ++ tailWord_3656459) baseStart_3656459 baseEnd_3656459 := by
    simpa [prefixWord, tailWord_3656459, baseEnd_3656459] using wordTrace_append hprefix tailTrace_3656459
  have hstable : (prefixWord ++ tailWord_3656459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656459).length < 2 ^ (prefixWord ++ tailWord_3656459).sum := by decide
  have hdescent : baseEnd_3656459 < baseStart_3656459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656469 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 6, 4]
def baseStart_3656469 : Nat := 118140960795 + 3656469 * 2 ^ 59
def prefixEnd_3656469 : Nat := 4983230072969 + 3 ^ 40 * 3656469 * 2
def baseEnd_3656469 : Nat := 625842031754919927307237

theorem tailTrace_3656469 : CollatzResearch.WordTrace tailWord_3656469 prefixEnd_3656469 625842031754919927307237 := by
  unfold tailWord_3656469
  simp only [CollatzResearch.WordTrace]
  refine ⟨133362380590244763033300461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88908253726829842022200307 133362380590244763033300461)
  ·
    refine ⟨50010892721341786137487673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133362380590244763033300461 50010892721341786137487673)
    ·
      refine ⟨37508169541006339603115755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50010892721341786137487673 37508169541006339603115755)
      ·
        refine ⟨56262254311509509404673633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37508169541006339603115755 56262254311509509404673633)
        ·
          refine ⟨42196690733632132053505225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56262254311509509404673633 42196690733632132053505225)
          ·
            refine ⟨31647518050224099040128919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42196690733632132053505225 31647518050224099040128919)
            ·
              refine ⟨47471277075336148560193379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31647518050224099040128919 47471277075336148560193379)
              ·
                refine ⟨71206915613004222840290069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47471277075336148560193379 71206915613004222840290069)
                ·
                  refine ⟨3337824169359572945638597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71206915613004222840290069 3337824169359572945638597)
                  ·
                    refine ⟨625842031754919927307237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3337824169359572945638597 625842031754919927307237)
                    ·
                      rfl

theorem cell23_3656469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_3656469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656469 prefixEnd_3656469 := by exact prefixLift 3656469
  have htrace : WordTrace (prefixWord ++ tailWord_3656469) baseStart_3656469 baseEnd_3656469 := by
    simpa [prefixWord, tailWord_3656469, baseEnd_3656469] using wordTrace_append hprefix tailTrace_3656469
  have hstable : (prefixWord ++ tailWord_3656469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656469).length < 2 ^ (prefixWord ++ tailWord_3656469).sum := by decide
  have hdescent : baseEnd_3656469 < baseStart_3656469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656476 : List Nat := [2, 2, 3, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_3656476 : Nat := 118140960795 + 3656476 * 2 ^ 59
def prefixEnd_3656476 : Nat := 4983230072969 + 3 ^ 40 * 3656476 * 2
def baseEnd_3656476 : Nat := 1877529689629341254534179

theorem tailTrace_3656476 : CollatzResearch.WordTrace tailWord_3656476 prefixEnd_3656476 1877529689629341254534179 := by
  unfold tailWord_3656476
  simp only [CollatzResearch.WordTrace]
  refine ⟨66681317950609701614402641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88908423934146268819203521 66681317950609701614402641)
  ·
    refine ⟨50010988462957276210801981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66681317950609701614402641 50010988462957276210801981)
    ·
      refine ⟨18754120673608978579050743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50010988462957276210801981 18754120673608978579050743)
      ·
        refine ⟨28131181010413467868576115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18754120673608978579050743 28131181010413467868576115)
        ·
          refine ⟨42196771515620201802864173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28131181010413467868576115 42196771515620201802864173)
          ·
            refine ⟨15823789318357575676074065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42196771515620201802864173 15823789318357575676074065)
            ·
              refine ⟨11867841988768181757055549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15823789318357575676074065 11867841988768181757055549)
              ·
                refine ⟨4450440745788068158895831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11867841988768181757055549 4450440745788068158895831)
                ·
                  refine ⟨6675661118682102238343747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450440745788068158895831 6675661118682102238343747)
                  ·
                    refine ⟨10013491678023153357515621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6675661118682102238343747 10013491678023153357515621)
                    ·
                      refine ⟨1877529689629341254534179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10013491678023153357515621 1877529689629341254534179)
                      ·
                        rfl

theorem cell23_3656476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_3656476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656476 prefixEnd_3656476 := by exact prefixLift 3656476
  have htrace : WordTrace (prefixWord ++ tailWord_3656476) baseStart_3656476 baseEnd_3656476 := by
    simpa [prefixWord, tailWord_3656476, baseEnd_3656476] using wordTrace_append hprefix tailTrace_3656476
  have hstable : (prefixWord ++ tailWord_3656476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656476).length < 2 ^ (prefixWord ++ tailWord_3656476).sum := by decide
  have hdescent : baseEnd_3656476 < baseStart_3656476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656479 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 5]
def baseStart_3656479 : Nat := 118140960795 + 3656479 * 2 ^ 59
def prefixEnd_3656479 : Nat := 4983230072969 + 3 ^ 40 * 3656479 * 2
def baseEnd_3656479 : Nat := 1877531230071304742796665

theorem tailTrace_3656479 : CollatzResearch.WordTrace tailWord_3656479 prefixEnd_3656479 1877531230071304742796665 := by
  unfold tailWord_3656479
  simp only [CollatzResearch.WordTrace]
  refine ⟨133362745320208534741164491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88908496880139023160776327 133362745320208534741164491)
  ·
    refine ⟨200044117980312802111746737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133362745320208534741164491 200044117980312802111746737)
    ·
      refine ⟨150033088485234601583810053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200044117980312802111746737 150033088485234601583810053)
      ·
        refine ⟨28131204090981487796964385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150033088485234601583810053 28131204090981487796964385)
        ·
          refine ⟨21098403068236115847723289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28131204090981487796964385 21098403068236115847723289)
          ·
            refine ⟨15823802301177086885792467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21098403068236115847723289 15823802301177086885792467)
            ·
              refine ⟨23735703451765630328688701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15823802301177086885792467 23735703451765630328688701)
              ·
                refine ⟨8900888794412111373258263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23735703451765630328688701 8900888794412111373258263)
                ·
                  refine ⟨13351333191618167059887395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8900888794412111373258263 13351333191618167059887395)
                  ·
                    refine ⟨20026999787427250589831093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13351333191618167059887395 20026999787427250589831093)
                    ·
                      refine ⟨1877531230071304742796665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20026999787427250589831093 1877531230071304742796665)
                      ·
                        rfl

theorem cell23_3656479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_3656479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656479 prefixEnd_3656479 := by exact prefixLift 3656479
  have htrace : WordTrace (prefixWord ++ tailWord_3656479) baseStart_3656479 baseEnd_3656479 := by
    simpa [prefixWord, tailWord_3656479, baseEnd_3656479] using wordTrace_append hprefix tailTrace_3656479
  have hstable : (prefixWord ++ tailWord_3656479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656479).length < 2 ^ (prefixWord ++ tailWord_3656479).sum := by decide
  have hdescent : baseEnd_3656479 < baseStart_3656479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656499 : List Nat := [1, 1, 1, 2, 6, 2, 2, 8]
def baseStart_3656499 : Nat := 118140960795 + 3656499 * 2 ^ 59
def prefixEnd_3656499 : Nat := 4983230072969 + 3 ^ 40 * 3656499 * 2
def baseEnd_3656499 : Nat := 69538574062384987575799

theorem tailTrace_3656499 : CollatzResearch.WordTrace tailWord_3656499 prefixEnd_3656499 69538574062384987575799 := by
  unfold tailWord_3656499
  simp only [CollatzResearch.WordTrace]
  refine ⟨133363474780136078156892551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88908983186757385437928367 133363474780136078156892551)
  ·
    refine ⟨200045212170204117235338827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133363474780136078156892551 200045212170204117235338827)
    ·
      refine ⟨300067818255306175853008241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200045212170204117235338827 300067818255306175853008241)
      ·
        refine ⟨225050863691479631889756181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300067818255306175853008241 225050863691479631889756181)
        ·
          refine ⟨10549259235538107744832321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225050863691479631889756181 10549259235538107744832321)
          ·
            refine ⟨7911944426653580808624241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10549259235538107744832321 7911944426653580808624241)
            ·
              refine ⟨5933958319990185606468181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7911944426653580808624241 5933958319990185606468181)
              ·
                refine ⟨69538574062384987575799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5933958319990185606468181 69538574062384987575799)
                ·
                  rfl

theorem cell23_3656499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 8].length) (baseStart_3656499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656499 prefixEnd_3656499 := by exact prefixLift 3656499
  have htrace : WordTrace (prefixWord ++ tailWord_3656499) baseStart_3656499 baseEnd_3656499 := by
    simpa [prefixWord, tailWord_3656499, baseEnd_3656499] using wordTrace_append hprefix tailTrace_3656499
  have hstable : (prefixWord ++ tailWord_3656499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656499).length < 2 ^ (prefixWord ++ tailWord_3656499).sum := by decide
  have hdescent : baseEnd_3656499 < baseStart_3656499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656510 : List Nat := [4, 2, 1, 2, 3, 2, 1, 2, 1, 1, 4]
def baseStart_3656510 : Nat := 118140960795 + 3656510 * 2 ^ 59
def prefixEnd_3656510 : Nat := 4983230072969 + 3 ^ 40 * 3656510 * 2
def baseEnd_3656510 : Nat := 1877547147971594121509023

theorem tailTrace_3656510 : CollatzResearch.WordTrace tailWord_3656510 prefixEnd_3656510 1877547147971594121509023 := by
  unfold tailWord_3656510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16670484497887028379442873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88909250655397484690361989 16670484497887028379442873)
  ·
    refine ⟨12502863373415271284582155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16670484497887028379442873 12502863373415271284582155)
    ·
      refine ⟨18754295060122906926873233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12502863373415271284582155 18754295060122906926873233)
      ·
        refine ⟨14065721295092180195154925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18754295060122906926873233 14065721295092180195154925)
        ·
          refine ⟨5274645485659567573183097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14065721295092180195154925 5274645485659567573183097)
          ·
            refine ⟨3955984114244675679887323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5274645485659567573183097 3955984114244675679887323)
            ·
              refine ⟨5933976171367013519830985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955984114244675679887323 5933976171367013519830985)
              ·
                refine ⟨4450482128525260139873239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5933976171367013519830985 4450482128525260139873239)
                ·
                  refine ⟨6675723192787890209809859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450482128525260139873239 6675723192787890209809859)
                  ·
                    refine ⟨10013584789181835314714789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6675723192787890209809859 10013584789181835314714789)
                    ·
                      refine ⟨1877547147971594121509023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10013584789181835314714789 1877547147971594121509023)
                      ·
                        rfl

theorem cell23_3656510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_3656510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656510 prefixEnd_3656510 := by exact prefixLift 3656510
  have htrace : WordTrace (prefixWord ++ tailWord_3656510) baseStart_3656510 baseEnd_3656510 := by
    simpa [prefixWord, tailWord_3656510, baseEnd_3656510] using wordTrace_append hprefix tailTrace_3656510
  have hstable : (prefixWord ++ tailWord_3656510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656510).length < 2 ^ (prefixWord ++ tailWord_3656510).sum := by decide
  have hdescent : baseEnd_3656510 < baseStart_3656510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656526 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_3656526 : Nat := 118140960795 + 3656526 * 2 ^ 59
def prefixEnd_3656526 : Nat := 4983230072969 + 3 ^ 40 * 3656526 * 2
def baseEnd_3656526 : Nat := 1877555363662066058908949

theorem tailTrace_3656526 : CollatzResearch.WordTrace tailWord_3656526 prefixEnd_3656526 1877555363662066058908949 := by
  unfold tailWord_3656526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16670557443879782721015679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88909639700692174512083621 16670557443879782721015679)
  ·
    refine ⟨25005836165819674081523519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16670557443879782721015679 25005836165819674081523519)
    ·
      refine ⟨37508754248729511122285279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25005836165819674081523519 37508754248729511122285279)
      ·
        refine ⟨56263131373094266683427919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37508754248729511122285279 56263131373094266683427919)
        ·
          refine ⟨84394697059641400025141879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56263131373094266683427919 84394697059641400025141879)
          ·
            refine ⟨126592045589462100037712819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84394697059641400025141879 126592045589462100037712819)
            ·
              refine ⟨189888068384193150056569229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126592045589462100037712819 189888068384193150056569229)
              ·
                refine ⟨71208025644072431271213461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189888068384193150056569229 71208025644072431271213461)
                ·
                  refine ⟨3337876202065895215838131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71208025644072431271213461 3337876202065895215838131)
                  ·
                    refine ⟨5006814303098842823757197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3337876202065895215838131 5006814303098842823757197)
                    ·
                      refine ⟨1877555363662066058908949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5006814303098842823757197 1877555363662066058908949)
                      ·
                        rfl

theorem cell23_3656526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_3656526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656526 prefixEnd_3656526 := by exact prefixLift 3656526
  have htrace : WordTrace (prefixWord ++ tailWord_3656526) baseStart_3656526 baseEnd_3656526 := by
    simpa [prefixWord, tailWord_3656526, baseEnd_3656526] using wordTrace_append hprefix tailTrace_3656526
  have hstable : (prefixWord ++ tailWord_3656526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656526).length < 2 ^ (prefixWord ++ tailWord_3656526).sum := by decide
  have hdescent : baseEnd_3656526 < baseStart_3656526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656543 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 2, 1, 3]
def baseStart_3656543 : Nat := 118140960795 + 3656543 * 2 ^ 59
def prefixEnd_3656543 : Nat := 4983230072969 + 3 ^ 40 * 3656543 * 2
def baseEnd_3656543 : Nat := 1877564092833192492396371

theorem tailTrace_3656543 : CollatzResearch.WordTrace tailWord_3656543 prefixEnd_3656543 1877564092833192492396371 := by
  unfold tailWord_3656543
  simp only [CollatzResearch.WordTrace]
  refine ⟨133365079591976673671494283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88910053061317782447662855 133365079591976673671494283)
  ·
    refine ⟨200047619387965010507241425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133365079591976673671494283 200047619387965010507241425)
    ·
      refine ⟨150035714540973757880431069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200047619387965010507241425 150035714540973757880431069)
      ·
        refine ⟨56263392952865159205161651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150035714540973757880431069 56263392952865159205161651)
        ·
          refine ⟨84395089429297738807742477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56263392952865159205161651 84395089429297738807742477)
          ·
            refine ⟨31648158535986652052903429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84395089429297738807742477 31648158535986652052903429)
            ·
              refine ⟨5934029725497497259919393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31648158535986652052903429 5934029725497497259919393)
              ·
                refine ⟨4450522294123122944939545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5934029725497497259919393 4450522294123122944939545)
                ·
                  refine ⟨3337891720592342208704659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4450522294123122944939545 3337891720592342208704659)
                  ·
                    refine ⟨5006837580888513313056989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3337891720592342208704659 5006837580888513313056989)
                    ·
                      refine ⟨1877564092833192492396371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5006837580888513313056989 1877564092833192492396371)
                      ·
                        rfl

theorem cell23_3656543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_3656543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656543 prefixEnd_3656543 := by exact prefixLift 3656543
  have htrace : WordTrace (prefixWord ++ tailWord_3656543) baseStart_3656543 baseEnd_3656543 := by
    simpa [prefixWord, tailWord_3656543, baseEnd_3656543] using wordTrace_append hprefix tailTrace_3656543
  have hstable : (prefixWord ++ tailWord_3656543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656543).length < 2 ^ (prefixWord ++ tailWord_3656543).sum := by decide
  have hdescent : baseEnd_3656543 < baseStart_3656543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656549 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3656549 : Nat := 118140960795 + 3656549 * 2 ^ 59
def prefixEnd_3656549 : Nat := 4983230072969 + 3 ^ 40 * 3656549 * 2
def baseEnd_3656549 : Nat := 1877567173717119468921343

theorem tailTrace_3656549 : CollatzResearch.WordTrace tailWord_3656549 prefixEnd_3656549 1877567173717119468921343 := by
  unfold tailWord_3656549
  simp only [CollatzResearch.WordTrace]
  refine ⟨133365298429954936696212701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88910198953303291130808467 133365298429954936696212701)
  ·
    refine ⟨50011986911233101261079763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133365298429954936696212701 50011986911233101261079763)
    ·
      refine ⟨75017980366849651891619645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50011986911233101261079763 75017980366849651891619645)
      ·
        refine ⟨28131742637568619459357367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75017980366849651891619645 28131742637568619459357367)
        ·
          refine ⟨42197613956352929189036051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28131742637568619459357367 42197613956352929189036051)
          ·
            refine ⟨63296420934529393783554077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42197613956352929189036051 63296420934529393783554077)
            ·
              refine ⟨23736157850448522668832779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63296420934529393783554077 23736157850448522668832779)
              ·
                refine ⟨35604236775672784003249169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23736157850448522668832779 35604236775672784003249169)
                ·
                  refine ⟨26703177581754588002436877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35604236775672784003249169 26703177581754588002436877)
                  ·
                    refine ⟨10013691593157970500913829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26703177581754588002436877 10013691593157970500913829)
                    ·
                      refine ⟨1877567173717119468921343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10013691593157970500913829 1877567173717119468921343)
                      ·
                        rfl

theorem cell23_3656549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3656549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656549 prefixEnd_3656549 := by exact prefixLift 3656549
  have htrace : WordTrace (prefixWord ++ tailWord_3656549) baseStart_3656549 baseEnd_3656549 := by
    simpa [prefixWord, tailWord_3656549, baseEnd_3656549] using wordTrace_append hprefix tailTrace_3656549
  have hstable : (prefixWord ++ tailWord_3656549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656549).length < 2 ^ (prefixWord ++ tailWord_3656549).sum := by decide
  have hdescent : baseEnd_3656549 < baseStart_3656549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656579 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 4]
def baseStart_3656579 : Nat := 118140960795 + 3656579 * 2 ^ 59
def prefixEnd_3656579 : Nat := 4983230072969 + 3 ^ 40 * 3656579 * 2
def baseEnd_3656579 : Nat := 1877582578136754351546205

theorem tailTrace_3656579 : CollatzResearch.WordTrace tailWord_3656579 prefixEnd_3656579 1877582578136754351546205 := by
  unfold tailWord_3656579
  simp only [CollatzResearch.WordTrace]
  refine ⟨133366392619846251819804791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88910928413230834546536527 133366392619846251819804791)
  ·
    refine ⟨200049588929769377729707187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133366392619846251819804791 200049588929769377729707187)
    ·
      refine ⟨300074383394654066594560781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200049588929769377729707187 300074383394654066594560781)
      ·
        refine ⟨112527893772995274972960293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300074383394654066594560781 112527893772995274972960293)
        ·
          refine ⟨21098980082436614057430055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112527893772995274972960293 21098980082436614057430055)
          ·
            refine ⟨31648470123654921086145083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21098980082436614057430055 31648470123654921086145083)
            ·
              refine ⟨47472705185482381629217625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31648470123654921086145083 47472705185482381629217625)
              ·
                refine ⟨35604528889111786221913219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47472705185482381629217625 35604528889111786221913219)
                ·
                  refine ⟨53406793333667679332869829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35604528889111786221913219 53406793333667679332869829)
                  ·
                    refine ⟨10013773750062689874913093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53406793333667679332869829 10013773750062689874913093)
                    ·
                      refine ⟨1877582578136754351546205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10013773750062689874913093 1877582578136754351546205)
                      ·
                        rfl

theorem cell23_3656579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_3656579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656579 prefixEnd_3656579 := by exact prefixLift 3656579
  have htrace : WordTrace (prefixWord ++ tailWord_3656579) baseStart_3656579 baseEnd_3656579 := by
    simpa [prefixWord, tailWord_3656579, baseEnd_3656579] using wordTrace_append hprefix tailTrace_3656579
  have hstable : (prefixWord ++ tailWord_3656579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656579).length < 2 ^ (prefixWord ++ tailWord_3656579).sum := by decide
  have hdescent : baseEnd_3656579 < baseStart_3656579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656583 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 1, 4, 2]
def baseStart_3656583 : Nat := 118140960795 + 3656583 * 2 ^ 59
def prefixEnd_3656583 : Nat := 4983230072969 + 3 ^ 40 * 3656583 * 2
def baseEnd_3656583 : Nat := 1877584632059372335896187

theorem tailTrace_3656583 : CollatzResearch.WordTrace tailWord_3656583 prefixEnd_3656583 1877584632059372335896187 := by
  unfold tailWord_3656583
  simp only [CollatzResearch.WordTrace]
  refine ⟨133366538511831760502950403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88911025674554507001966935 133366538511831760502950403)
  ·
    refine ⟨200049807767747640754425605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133366538511831760502950403 200049807767747640754425605)
    ·
      refine ⟨37509338956452682641454801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200049807767747640754425605 37509338956452682641454801)
      ·
        refine ⟨28132004217339511981091101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37509338956452682641454801 28132004217339511981091101)
        ·
          refine ⟨10549501581502316992909163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28132004217339511981091101 10549501581502316992909163)
          ·
            refine ⟨15824252372253475489363745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10549501581502316992909163 15824252372253475489363745)
            ·
              refine ⟨11868189279190106617022809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15824252372253475489363745 11868189279190106617022809)
              ·
                refine ⟨8901141959392579962767107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11868189279190106617022809 8901141959392579962767107)
                ·
                  refine ⟨13351712939088869944150661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8901141959392579962767107 13351712939088869944150661)
                  ·
                    refine ⟨2503446176079163114528249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13351712939088869944150661 2503446176079163114528249)
                    ·
                      refine ⟨1877584632059372335896187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2503446176079163114528249 1877584632059372335896187)
                      ·
                        rfl

theorem cell23_3656583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_3656583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656583 prefixEnd_3656583 := by exact prefixLift 3656583
  have htrace : WordTrace (prefixWord ++ tailWord_3656583) baseStart_3656583 baseEnd_3656583 := by
    simpa [prefixWord, tailWord_3656583, baseEnd_3656583] using wordTrace_append hprefix tailTrace_3656583
  have hstable : (prefixWord ++ tailWord_3656583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656583).length < 2 ^ (prefixWord ++ tailWord_3656583).sum := by decide
  have hdescent : baseEnd_3656583 < baseStart_3656583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656594 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 2, 1, 3]
def baseStart_3656594 : Nat := 118140960795 + 3656594 * 2 ^ 59
def prefixEnd_3656594 : Nat := 4983230072969 + 3 ^ 40 * 3656594 * 2
def baseEnd_3656594 : Nat := 1877590280346571792858637

theorem tailTrace_3656594 : CollatzResearch.WordTrace tailWord_3656594 prefixEnd_3656594 1877590280346571792858637 := by
  unfold tailWord_3656594
  simp only [CollatzResearch.WordTrace]
  refine ⟨33341734928697977345400209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88911293143194606254400557 33341734928697977345400209)
  ·
    refine ⟨25006301196523483009050157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33341734928697977345400209 25006301196523483009050157)
    ·
      refine ⟨9377362948696306128393809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25006301196523483009050157 9377362948696306128393809)
      ·
        refine ⟨7033022211522229596295357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9377362948696306128393809 7033022211522229596295357)
        ·
          refine ⟨2637383329320836098610759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7033022211522229596295357 2637383329320836098610759)
          ·
            refine ⟨3956074993981254147916139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637383329320836098610759 3956074993981254147916139)
            ·
              refine ⟨5934112490971881221874209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956074993981254147916139 5934112490971881221874209)
              ·
                refine ⟨4450584368228910916405657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5934112490971881221874209 4450584368228910916405657)
                ·
                  refine ⟨3337938276171683187304243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4450584368228910916405657 3337938276171683187304243)
                  ·
                    refine ⟨5006907414257524780956365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3337938276171683187304243 5006907414257524780956365)
                    ·
                      refine ⟨1877590280346571792858637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5006907414257524780956365 1877590280346571792858637)
                      ·
                        rfl

theorem cell23_3656594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_3656594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656594 prefixEnd_3656594 := by exact prefixLift 3656594
  have htrace : WordTrace (prefixWord ++ tailWord_3656594) baseStart_3656594 baseEnd_3656594 := by
    simpa [prefixWord, tailWord_3656594, baseEnd_3656594] using wordTrace_append hprefix tailTrace_3656594
  have hstable : (prefixWord ++ tailWord_3656594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656594).length < 2 ^ (prefixWord ++ tailWord_3656594).sum := by decide
  have hdescent : baseEnd_3656594 < baseStart_3656594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656596 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3656596 : Nat := 118140960795 + 3656596 * 2 ^ 59
def prefixEnd_3656596 : Nat := 4983230072969 + 3 ^ 40 * 3656596 * 2
def baseEnd_3656596 : Nat := 1877591307307880785033627

theorem tailTrace_3656596 : CollatzResearch.WordTrace tailWord_3656596 prefixEnd_3656596 1877591307307880785033627 := by
  unfold tailWord_3656596
  simp only [CollatzResearch.WordTrace]
  refine ⟨66683506330392331861586821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88911341773856442482115761 66683506330392331861586821)
  ·
    refine ⟨12503157436948562224047529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66683506330392331861586821 12503157436948562224047529)
    ·
      refine ⟨9377368077711421668035647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12503157436948562224047529 9377368077711421668035647)
      ·
        refine ⟨14066052116567132502053471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9377368077711421668035647 14066052116567132502053471)
        ·
          refine ⟨21099078174850698753080207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14066052116567132502053471 21099078174850698753080207)
          ·
            refine ⟨31648617262276048129620311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21099078174850698753080207 31648617262276048129620311)
            ·
              refine ⟨47472925893414072194430467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31648617262276048129620311 47472925893414072194430467)
              ·
                refine ⟨71209388840121108291645701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47472925893414072194430467 71209388840121108291645701)
                ·
                  refine ⟨13351760407522707804683569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71209388840121108291645701 13351760407522707804683569)
                  ·
                    refine ⟨10013820305642030853512677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13351760407522707804683569 10013820305642030853512677)
                    ·
                      refine ⟨1877591307307880785033627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10013820305642030853512677 1877591307307880785033627)
                      ·
                        rfl

theorem cell23_3656596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3656596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656596 prefixEnd_3656596 := by exact prefixLift 3656596
  have htrace : WordTrace (prefixWord ++ tailWord_3656596) baseStart_3656596 baseEnd_3656596 := by
    simpa [prefixWord, tailWord_3656596, baseEnd_3656596] using wordTrace_append hprefix tailTrace_3656596
  have hstable : (prefixWord ++ tailWord_3656596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656596).length < 2 ^ (prefixWord ++ tailWord_3656596).sum := by decide
  have hdescent : baseEnd_3656596 < baseStart_3656596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656619 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 4, 5]
def baseStart_3656619 : Nat := 118140960795 + 3656619 * 2 ^ 59
def prefixEnd_3656619 : Nat := 4983230072969 + 3 ^ 40 * 3656619 * 2
def baseEnd_3656619 : Nat := 625867705787644731682007

theorem tailTrace_3656619 : CollatzResearch.WordTrace tailWord_3656619 prefixEnd_3656619 625867705787644731682007 := by
  unfold tailWord_3656619
  simp only [CollatzResearch.WordTrace]
  refine ⟨133367851539701338651260911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88911901026467559100840607 133367851539701338651260911)
  ·
    refine ⟨200051777309552007976891367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133367851539701338651260911 200051777309552007976891367)
    ·
      refine ⟨300077665964328011965337051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200051777309552007976891367 300077665964328011965337051)
      ·
        refine ⟨450116498946492017948005577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300077665964328011965337051 450116498946492017948005577)
        ·
          refine ⟨337587374209869013461004183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450116498946492017948005577 337587374209869013461004183)
          ·
            refine ⟨506381061314803520191506275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337587374209869013461004183 506381061314803520191506275)
            ·
              refine ⟨759571591972205280287259413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506381061314803520191506275 759571591972205280287259413)
              ·
                refine ⟨35604918373697122513465285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 759571591972205280287259413 35604918373697122513465285)
                ·
                  refine ⟨6675922195068210471274741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35604918373697122513465285 6675922195068210471274741)
                  ·
                    refine ⟨625867705787644731682007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6675922195068210471274741 625867705787644731682007)
                    ·
                      rfl

theorem cell23_3656619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 5].length) (baseStart_3656619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656619 prefixEnd_3656619 := by exact prefixLift 3656619
  have htrace : WordTrace (prefixWord ++ tailWord_3656619) baseStart_3656619 baseEnd_3656619 := by
    simpa [prefixWord, tailWord_3656619, baseEnd_3656619] using wordTrace_append hprefix tailTrace_3656619
  have hstable : (prefixWord ++ tailWord_3656619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656619).length < 2 ^ (prefixWord ++ tailWord_3656619).sum := by decide
  have hdescent : baseEnd_3656619 < baseStart_3656619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656676 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 1, 4, 3]
def baseStart_3656676 : Nat := 118140960795 + 3656676 * 2 ^ 59
def prefixEnd_3656676 : Nat := 4983230072969 + 3 ^ 40 * 3656676 * 2
def baseEnd_3656676 : Nat := 1877632385760240472033259

theorem tailTrace_3656676 : CollatzResearch.WordTrace tailWord_3656676 prefixEnd_3656676 1877632385760240472033259 := by
  unfold tailWord_3656676
  simp only [CollatzResearch.WordTrace]
  refine ⟨66684965250247418693042941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88913287000329891590723921 66684965250247418693042941)
  ·
    refine ⟨25006861968842782009891103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66684965250247418693042941 25006861968842782009891103)
    ·
      refine ⟨37510292953264173014836655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25006861968842782009891103 37510292953264173014836655)
      ·
        refine ⟨56265439429896259522254983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37510292953264173014836655 56265439429896259522254983)
        ·
          refine ⟨84398159144844389283382475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56265439429896259522254983 84398159144844389283382475)
          ·
            refine ⟨126597238717266583925073713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84398159144844389283382475 126597238717266583925073713)
            ·
              refine ⟨94947929037949937943805285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126597238717266583925073713 94947929037949937943805285)
              ·
                refine ⟨17802736694615613364463491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94947929037949937943805285 17802736694615613364463491)
                ·
                  refine ⟨26704105041923420046695237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17802736694615613364463491 26704105041923420046695237)
                  ·
                    refine ⟨5007019695360641258755357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26704105041923420046695237 5007019695360641258755357)
                    ·
                      refine ⟨1877632385760240472033259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5007019695360641258755357 1877632385760240472033259)
                      ·
                        rfl

theorem cell23_3656676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_3656676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656676 prefixEnd_3656676 := by exact prefixLift 3656676
  have htrace : WordTrace (prefixWord ++ tailWord_3656676) baseStart_3656676 baseEnd_3656676 := by
    simpa [prefixWord, tailWord_3656676, baseEnd_3656676] using wordTrace_append hprefix tailTrace_3656676
  have hstable : (prefixWord ++ tailWord_3656676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656676).length < 2 ^ (prefixWord ++ tailWord_3656676).sum := by decide
  have hdescent : baseEnd_3656676 < baseStart_3656676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656699 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 8]
def baseStart_3656699 : Nat := 118140960795 + 3656699 * 2 ^ 59
def prefixEnd_3656699 : Nat := 4983230072969 + 3 ^ 40 * 3656699 * 2
def baseEnd_3656699 : Nat := 1877644195815293882045653

theorem tailTrace_3656699 : CollatzResearch.WordTrace tailWord_3656699 prefixEnd_3656699 1877644195815293882045653 := by
  unfold tailWord_3656699
  simp only [CollatzResearch.WordTrace]
  refine ⟨133370769379411512314173151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88913846252941008209448767 133370769379411512314173151)
  ·
    refine ⟨200056154069117268471259727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133370769379411512314173151 200056154069117268471259727)
    ·
      refine ⟨300084231103675902706889591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200056154069117268471259727 300084231103675902706889591)
      ·
        refine ⟨450126346655513854060334387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300084231103675902706889591 450126346655513854060334387)
        ·
          refine ⟨675189519983270781090501581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450126346655513854060334387 675189519983270781090501581)
          ·
            refine ⟨253196069993726542908938093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 675189519983270781090501581 253196069993726542908938093)
            ·
              refine ⟨94948526247647453590851785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253196069993726542908938093 94948526247647453590851785)
              ·
                refine ⟨71211394685735590193138839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94948526247647453590851785 71211394685735590193138839)
                ·
                  refine ⟨106817092028603385289708259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71211394685735590193138839 106817092028603385289708259)
                  ·
                    refine ⟨160225638042905077934562389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106817092028603385289708259 160225638042905077934562389)
                    ·
                      refine ⟨1877644195815293882045653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 160225638042905077934562389 1877644195815293882045653)
                      ·
                        rfl

theorem cell23_3656699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_3656699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656699 prefixEnd_3656699 := by exact prefixLift 3656699
  have htrace : WordTrace (prefixWord ++ tailWord_3656699) baseStart_3656699 baseEnd_3656699 := by
    simpa [prefixWord, tailWord_3656699, baseEnd_3656699] using wordTrace_append hprefix tailTrace_3656699
  have hstable : (prefixWord ++ tailWord_3656699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656699).length < 2 ^ (prefixWord ++ tailWord_3656699).sum := by decide
  have hdescent : baseEnd_3656699 < baseStart_3656699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656723 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 3, 1, 3]
def baseStart_3656723 : Nat := 118140960795 + 3656723 * 2 ^ 59
def prefixEnd_3656723 : Nat := 4983230072969 + 3 ^ 40 * 3656723 * 2
def baseEnd_3656723 : Nat := 1877656519351001788145543

theorem tailTrace_3656723 : CollatzResearch.WordTrace tailWord_3656723 prefixEnd_3656723 1877656519351001788145543 := by
  unfold tailWord_3656723
  simp only [CollatzResearch.WordTrace]
  refine ⟨133371644731324564413046823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88914429820883042942031215 133371644731324564413046823)
  ·
    refine ⟨200057467096986846619570235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133371644731324564413046823 200057467096986846619570235)
    ·
      refine ⟨300086200645480269929355353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200057467096986846619570235 300086200645480269929355353)
      ·
        refine ⟨225064650484110202447016515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300086200645480269929355353 225064650484110202447016515)
        ·
          refine ⟨337596975726165303670524773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225064650484110202447016515 337596975726165303670524773)
          ·
            refine ⟨63299432948655994438223395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337596975726165303670524773 63299432948655994438223395)
            ·
              refine ⟨94949149422983991657335093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63299432948655994438223395 94949149422983991657335093)
              ·
                refine ⟨8901482758404749217875165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94949149422983991657335093 8901482758404749217875165)
                ·
                  refine ⟨3338056034401780956703187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8901482758404749217875165 3338056034401780956703187)
                  ·
                    refine ⟨5007084051602671435054781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3338056034401780956703187 5007084051602671435054781)
                    ·
                      refine ⟨1877656519351001788145543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5007084051602671435054781 1877656519351001788145543)
                      ·
                        rfl

theorem cell23_3656723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3, 1, 3].length) (baseStart_3656723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656723 prefixEnd_3656723 := by exact prefixLift 3656723
  have htrace : WordTrace (prefixWord ++ tailWord_3656723) baseStart_3656723 baseEnd_3656723 := by
    simpa [prefixWord, tailWord_3656723, baseEnd_3656723] using wordTrace_append hprefix tailTrace_3656723
  have hstable : (prefixWord ++ tailWord_3656723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656723).length < 2 ^ (prefixWord ++ tailWord_3656723).sum := by decide
  have hdescent : baseEnd_3656723 < baseStart_3656723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656740 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3656740 : Nat := 118140960795 + 3656740 * 2 ^ 59
def prefixEnd_3656740 : Nat := 4983230072969 + 3 ^ 40 * 3656740 * 2
def baseEnd_3656740 : Nat := 1877665248522128221632965

theorem tailTrace_3656740 : CollatzResearch.WordTrace tailWord_3656740 prefixEnd_3656740 1877665248522128221632965 := by
  unfold tailWord_3656740
  simp only [CollatzResearch.WordTrace]
  refine ⟨66686132386131488158207837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88914843181508650877610449 66686132386131488158207837)
  ·
    refine ⟨25007299644799308059327939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66686132386131488158207837 25007299644799308059327939)
    ·
      refine ⟨37510949467198962088991909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25007299644799308059327939 37510949467198962088991909)
      ·
        refine ⟨7033303025099805391685983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37510949467198962088991909 7033303025099805391685983)
        ·
          refine ⟨10549954537649708087528975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033303025099805391685983 10549954537649708087528975)
          ·
            refine ⟨15824931806474562131293463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10549954537649708087528975 15824931806474562131293463)
            ·
              refine ⟨23737397709711843196940195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15824931806474562131293463 23737397709711843196940195)
              ·
                refine ⟨35606096564567764795410293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23737397709711843196940195 35606096564567764795410293)
                ·
                  refine ⟨3338071552928227949569715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35606096564567764795410293 3338071552928227949569715)
                  ·
                    refine ⟨5007107329392341924354573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3338071552928227949569715 5007107329392341924354573)
                    ·
                      refine ⟨1877665248522128221632965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5007107329392341924354573 1877665248522128221632965)
                      ·
                        rfl

theorem cell23_3656740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3656740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656740 prefixEnd_3656740 := by exact prefixLift 3656740
  have htrace : WordTrace (prefixWord ++ tailWord_3656740) baseStart_3656740 baseEnd_3656740 := by
    simpa [prefixWord, tailWord_3656740, baseEnd_3656740] using wordTrace_append hprefix tailTrace_3656740
  have hstable : (prefixWord ++ tailWord_3656740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656740).length < 2 ^ (prefixWord ++ tailWord_3656740).sum := by decide
  have hdescent : baseEnd_3656740 < baseStart_3656740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656750 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_3656750 : Nat := 118140960795 + 3656750 * 2 ^ 59
def prefixEnd_3656750 : Nat := 4983230072969 + 3 ^ 40 * 3656750 * 2
def baseEnd_3656750 : Nat := 1877670383328673182507919

theorem tailTrace_3656750 : CollatzResearch.WordTrace tailWord_3656750 prefixEnd_3656750 1877670383328673182507919 := by
  unfold tailWord_3656750
  simp only [CollatzResearch.WordTrace]
  refine ⟨16671578687778343503034963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88915086334817832016186469 16671578687778343503034963)
  ·
    refine ⟨25007368031667515254552445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16671578687778343503034963 25007368031667515254552445)
    ·
      refine ⟨9377763011875318220457167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25007368031667515254552445 9377763011875318220457167)
      ·
        refine ⟨14066644517812977330685751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9377763011875318220457167 14066644517812977330685751)
        ·
          refine ⟨21099966776719465996028627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14066644517812977330685751 21099966776719465996028627)
          ·
            refine ⟨31649950165079198994042941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21099966776719465996028627 31649950165079198994042941)
            ·
              refine ⟨11868731311904699622766103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31649950165079198994042941 11868731311904699622766103)
              ·
                refine ⟨17803096967857049434149155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11868731311904699622766103 17803096967857049434149155)
                ·
                  refine ⟨26704645451785574151223733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17803096967857049434149155 26704645451785574151223733)
                  ·
                    refine ⟨2503560511104897576677225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26704645451785574151223733 2503560511104897576677225)
                    ·
                      refine ⟨1877670383328673182507919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2503560511104897576677225 1877670383328673182507919)
                      ·
                        rfl

theorem cell23_3656750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_3656750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656750 prefixEnd_3656750 := by exact prefixLift 3656750
  have htrace : WordTrace (prefixWord ++ tailWord_3656750) baseStart_3656750 baseEnd_3656750 := by
    simpa [prefixWord, tailWord_3656750, baseEnd_3656750] using wordTrace_append hprefix tailTrace_3656750
  have hstable : (prefixWord ++ tailWord_3656750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656750).length < 2 ^ (prefixWord ++ tailWord_3656750).sum := by decide
  have hdescent : baseEnd_3656750 < baseStart_3656750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656760 : List Nat := [2, 1, 2, 1, 5, 1, 4, 1, 1, 5]
def baseStart_3656760 : Nat := 118140960795 + 3656760 * 2 ^ 59
def prefixEnd_3656760 : Nat := 4983230072969 + 3 ^ 40 * 3656760 * 2
def baseEnd_3656760 : Nat := 625891839378406047794291

theorem tailTrace_3656760 : CollatzResearch.WordTrace tailWord_3656760 prefixEnd_3656760 625891839378406047794291 := by
  unfold tailWord_3656760
  simp only [CollatzResearch.WordTrace]
  refine ⟨66686497116095259866071867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88915329488127013154762489 66686497116095259866071867)
  ·
    refine ⟨100029745674142889799107801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66686497116095259866071867 100029745674142889799107801)
    ·
      refine ⟨75022309255607167349330851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100029745674142889799107801 75022309255607167349330851)
      ·
        refine ⟨112533463883410751023996277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75022309255607167349330851 112533463883410751023996277)
        ·
          refine ⟨10550012239069757908499651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112533463883410751023996277 10550012239069757908499651)
          ·
            refine ⟨15825018358604636862749477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10550012239069757908499651 15825018358604636862749477)
            ·
              refine ⟨2967190942238369411765527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15825018358604636862749477 2967190942238369411765527)
              ·
                refine ⟨4450786413357554117648291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967190942238369411765527 4450786413357554117648291)
                ·
                  refine ⟨6676179620036331176472437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450786413357554117648291 6676179620036331176472437)
                  ·
                    refine ⟨625891839378406047794291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6676179620036331176472437 625891839378406047794291)
                    ·
                      rfl

theorem cell23_3656760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_3656760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656760 prefixEnd_3656760 := by exact prefixLift 3656760
  have htrace : WordTrace (prefixWord ++ tailWord_3656760) baseStart_3656760 baseEnd_3656760 := by
    simpa [prefixWord, tailWord_3656760, baseEnd_3656760] using wordTrace_append hprefix tailTrace_3656760
  have hstable : (prefixWord ++ tailWord_3656760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656760).length < 2 ^ (prefixWord ++ tailWord_3656760).sum := by decide
  have hdescent : baseEnd_3656760 < baseStart_3656760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656774 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3656774 : Nat := 118140960795 + 3656774 * 2 ^ 59
def prefixEnd_3656774 : Nat := 4983230072969 + 3 ^ 40 * 3656774 * 2
def baseEnd_3656774 : Nat := 1877682706864381088607809

theorem tailTrace_3656774 : CollatzResearch.WordTrace tailWord_3656774 prefixEnd_3656774 1877682706864381088607809 := by
  unfold tailWord_3656774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4167922026691868753848543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88915669902759866748768917 4167922026691868753848543)
  ·
    refine ⟨6251883040037803130772815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4167922026691868753848543 6251883040037803130772815)
    ·
      refine ⟨9377824560056704696159223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6251883040037803130772815 9377824560056704696159223)
      ·
        refine ⟨14066736840085057044238835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9377824560056704696159223 14066736840085057044238835)
        ·
          refine ⟨21100105260127585566358253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14066736840085057044238835 21100105260127585566358253)
          ·
            refine ⟨7912539472547844587384345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21100105260127585566358253 7912539472547844587384345)
            ·
              refine ⟨5934404604410883440538259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7912539472547844587384345 5934404604410883440538259)
              ·
                refine ⟨8901606906616325160807389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5934404604410883440538259 8901606906616325160807389)
                ·
                  refine ⟨3338102589981121935302771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8901606906616325160807389 3338102589981121935302771)
                  ·
                    refine ⟨5007153884971682902954157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3338102589981121935302771 5007153884971682902954157)
                    ·
                      refine ⟨1877682706864381088607809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5007153884971682902954157 1877682706864381088607809)
                      ·
                        rfl

theorem cell23_3656774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3656774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656774 prefixEnd_3656774 := by exact prefixLift 3656774
  have htrace : WordTrace (prefixWord ++ tailWord_3656774) baseStart_3656774 baseEnd_3656774 := by
    simpa [prefixWord, tailWord_3656774, baseEnd_3656774] using wordTrace_append hprefix tailTrace_3656774
  have hstable : (prefixWord ++ tailWord_3656774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656774).length < 2 ^ (prefixWord ++ tailWord_3656774).sum := by decide
  have hdescent : baseEnd_3656774 < baseStart_3656774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656776 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_3656776 : Nat := 118140960795 + 3656776 * 2 ^ 59
def prefixEnd_3656776 : Nat := 4983230072969 + 3 ^ 40 * 3656776 * 2
def baseEnd_3656776 : Nat := 1877683733825690080782799

theorem tailTrace_3656776 : CollatzResearch.WordTrace tailWord_3656776 prefixEnd_3656776 1877683733825690080782799 := by
  unfold tailWord_3656776
  simp only [CollatzResearch.WordTrace]
  refine ⟨66686788900066277232363091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88915718533421702976484121 66686788900066277232363091)
  ·
    refine ⟨100030183350099415848544637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66686788900066277232363091 100030183350099415848544637)
    ·
      refine ⟨37511318756287280943204239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100030183350099415848544637 37511318756287280943204239)
      ·
        refine ⟨56266978134430921414806359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37511318756287280943204239 56266978134430921414806359)
        ·
          refine ⟨84400467201646382122209539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56266978134430921414806359 84400467201646382122209539)
          ·
            refine ⟨126600700802469573183314309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84400467201646382122209539 126600700802469573183314309)
            ·
              refine ⟨23737631400463044971871433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126600700802469573183314309 23737631400463044971871433)
              ·
                refine ⟨17803223550347283728903575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23737631400463044971871433 17803223550347283728903575)
                ·
                  refine ⟨26704835325520925593355363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17803223550347283728903575 26704835325520925593355363)
                  ·
                    refine ⟨40057252988281388390033045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26704835325520925593355363 40057252988281388390033045)
                    ·
                      refine ⟨1877683733825690080782799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40057252988281388390033045 1877683733825690080782799)
                      ·
                        rfl

theorem cell23_3656776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_3656776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656776 prefixEnd_3656776 := by exact prefixLift 3656776
  have htrace : WordTrace (prefixWord ++ tailWord_3656776) baseStart_3656776 baseEnd_3656776 := by
    simpa [prefixWord, tailWord_3656776, baseEnd_3656776] using wordTrace_append hprefix tailTrace_3656776
  have hstable : (prefixWord ++ tailWord_3656776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656776).length < 2 ^ (prefixWord ++ tailWord_3656776).sum := by decide
  have hdescent : baseEnd_3656776 < baseStart_3656776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656800 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 3]
def baseStart_3656800 : Nat := 118140960795 + 3656800 * 2 ^ 59
def prefixEnd_3656800 : Nat := 4983230072969 + 3 ^ 40 * 3656800 * 2
def baseEnd_3656800 : Nat := 1877696057361397986882689

theorem tailTrace_3656800 : CollatzResearch.WordTrace tailWord_3656800 prefixEnd_3656800 1877696057361397986882689 := by
  unfold tailWord_3656800
  simp only [CollatzResearch.WordTrace]
  refine ⟨66687226576022803281799927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88916302101363737709066569 66687226576022803281799927)
  ·
    refine ⟨100030839864034204922699891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66687226576022803281799927 100030839864034204922699891)
    ·
      refine ⟨150046259796051307384049837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100030839864034204922699891 150046259796051307384049837)
      ·
        refine ⟨56267347423519240269018689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150046259796051307384049837 56267347423519240269018689)
        ·
          refine ⟨42200510567639430201764017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56267347423519240269018689 42200510567639430201764017)
          ·
            refine ⟨31650382925729572651323013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42200510567639430201764017 31650382925729572651323013)
            ·
              refine ⟨5934446798574294872123065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31650382925729572651323013 5934446798574294872123065)
              ·
                refine ⟨4450835098930721154092299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5934446798574294872123065 4450835098930721154092299)
                ·
                  refine ⟨6676252648396081731138449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4450835098930721154092299 6676252648396081731138449)
                  ·
                    refine ⟨5007189486297061298353837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6676252648396081731138449 5007189486297061298353837)
                    ·
                      refine ⟨1877696057361397986882689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5007189486297061298353837 1877696057361397986882689)
                      ·
                        rfl

theorem cell23_3656800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_3656800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656800 prefixEnd_3656800 := by exact prefixLift 3656800
  have htrace : WordTrace (prefixWord ++ tailWord_3656800) baseStart_3656800 baseEnd_3656800 := by
    simpa [prefixWord, tailWord_3656800, baseEnd_3656800] using wordTrace_append hprefix tailTrace_3656800
  have hstable : (prefixWord ++ tailWord_3656800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656800).length < 2 ^ (prefixWord ++ tailWord_3656800).sum := by decide
  have hdescent : baseEnd_3656800 < baseStart_3656800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656808 : List Nat := [2, 1, 4, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3656808 : Nat := 118140960795 + 3656808 * 2 ^ 59
def prefixEnd_3656808 : Nat := 4983230072969 + 3 ^ 40 * 3656808 * 2
def baseEnd_3656808 : Nat := 1877700165206633955582653

theorem tailTrace_3656808 : CollatzResearch.WordTrace tailWord_3656808 prefixEnd_3656808 1877700165206633955582653 := by
  unfold tailWord_3656808
  simp only [CollatzResearch.WordTrace]
  refine ⟨66687372468008311964945539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88916496624011082619927385 66687372468008311964945539)
  ·
    refine ⟨100031058702012467947418309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66687372468008311964945539 100031058702012467947418309)
    ·
      refine ⟨18755823506627337740140933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100031058702012467947418309 18755823506627337740140933)
      ·
        refine ⟨3516716907492625826276425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18755823506627337740140933 3516716907492625826276425)
        ·
          refine ⟨2637537680619469369707319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3516716907492625826276425 2637537680619469369707319)
          ·
            refine ⟨3956306520929204054560979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637537680619469369707319 3956306520929204054560979)
            ·
              refine ⟨5934459781393806081841469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956306520929204054560979 5934459781393806081841469)
              ·
                refine ⟨2225422418022677280690551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5934459781393806081841469 2225422418022677280690551)
                ·
                  refine ⟨3338133627034015921035827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2225422418022677280690551 3338133627034015921035827)
                  ·
                    refine ⟨5007200440551023881553741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3338133627034015921035827 5007200440551023881553741)
                    ·
                      refine ⟨1877700165206633955582653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5007200440551023881553741 1877700165206633955582653)
                      ·
                        rfl

theorem cell23_3656808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3656808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656808 prefixEnd_3656808 := by exact prefixLift 3656808
  have htrace : WordTrace (prefixWord ++ tailWord_3656808) baseStart_3656808 baseEnd_3656808 := by
    simpa [prefixWord, tailWord_3656808, baseEnd_3656808] using wordTrace_append hprefix tailTrace_3656808
  have hstable : (prefixWord ++ tailWord_3656808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656808).length < 2 ^ (prefixWord ++ tailWord_3656808).sum := by decide
  have hdescent : baseEnd_3656808 < baseStart_3656808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656876 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 11]
def baseStart_3656876 : Nat := 118140960795 + 3656876 * 2 ^ 59
def prefixEnd_3656876 : Nat := 4983230072969 + 3 ^ 40 * 3656876 * 2
def baseEnd_3656876 : Nat := 208637231321237743281371

theorem tailTrace_3656876 : CollatzResearch.WordTrace tailWord_3656876 prefixEnd_3656876 208637231321237743281371 := by
  unfold tailWord_3656876
  simp only [CollatzResearch.WordTrace]
  refine ⟨66688612549885135771683241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88918150066513514362244321 66688612549885135771683241)
  ·
    refine ⟨50016459412413851828762431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66688612549885135771683241 50016459412413851828762431)
    ·
      refine ⟨75024689118620777743143647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50016459412413851828762431 75024689118620777743143647)
      ·
        refine ⟨112537033677931166614715471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75024689118620777743143647 112537033677931166614715471)
        ·
          refine ⟨168805550516896749922073207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112537033677931166614715471 168805550516896749922073207)
          ·
            refine ⟨253208325775345124883109811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168805550516896749922073207 253208325775345124883109811)
            ·
              refine ⟨379812488663017687324664717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253208325775345124883109811 379812488663017687324664717)
              ·
                refine ⟨142429683248631632746749269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 379812488663017687324664717 142429683248631632746749269)
                ·
                  refine ⟨208637231321237743281371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 142429683248631632746749269 208637231321237743281371)
                  ·
                    rfl

theorem cell23_3656876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_3656876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656876 prefixEnd_3656876 := by exact prefixLift 3656876
  have htrace : WordTrace (prefixWord ++ tailWord_3656876) baseStart_3656876 baseEnd_3656876 := by
    simpa [prefixWord, tailWord_3656876, baseEnd_3656876] using wordTrace_append hprefix tailTrace_3656876
  have hstable : (prefixWord ++ tailWord_3656876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656876).length < 2 ^ (prefixWord ++ tailWord_3656876).sum := by decide
  have hdescent : baseEnd_3656876 < baseStart_3656876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656910 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_3656910 : Nat := 118140960795 + 3656910 * 2 ^ 59
def prefixEnd_3656910 : Nat := 4983230072969 + 3 ^ 40 * 3656910 * 2
def baseEnd_3656910 : Nat := 208639171137043617389687

theorem tailTrace_3656910 : CollatzResearch.WordTrace tailWord_3656910 prefixEnd_3656910 208639171137043617389687 := by
  unfold tailWord_3656910
  simp only [CollatzResearch.WordTrace]
  refine ⟨16672308147705886918763023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88918976787764730233402789 16672308147705886918763023)
  ·
    refine ⟨25008462221558830378144535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16672308147705886918763023 25008462221558830378144535)
    ·
      refine ⟨37512693332338245567216803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25008462221558830378144535 37512693332338245567216803)
      ·
        refine ⟨56269039998507368350825205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37512693332338245567216803 56269039998507368350825205)
        ·
          refine ⟨5275222499860065782889863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56269039998507368350825205 5275222499860065782889863)
          ·
            refine ⟨7912833749790098674334795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275222499860065782889863 7912833749790098674334795)
            ·
              refine ⟨11869250624685148011502193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7912833749790098674334795 11869250624685148011502193)
              ·
                refine ⟨8901937968513861008626645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11869250624685148011502193 8901937968513861008626645)
                ·
                  refine ⟨208639171137043617389687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8901937968513861008626645 208639171137043617389687)
                  ·
                    rfl

theorem cell23_3656910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_3656910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656910 prefixEnd_3656910 := by exact prefixLift 3656910
  have htrace : WordTrace (prefixWord ++ tailWord_3656910) baseStart_3656910 baseEnd_3656910 := by
    simpa [prefixWord, tailWord_3656910, baseEnd_3656910] using wordTrace_append hprefix tailTrace_3656910
  have hstable : (prefixWord ++ tailWord_3656910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656910).length < 2 ^ (prefixWord ++ tailWord_3656910).sum := by decide
  have hdescent : baseEnd_3656910 < baseStart_3656910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656978 : List Nat := [3, 2, 4, 2, 2, 1, 1, 3, 5]
def baseStart_3656978 : Nat := 118140960795 + 3656978 * 2 ^ 59
def prefixEnd_3656978 : Nat := 4983230072969 + 3 ^ 40 * 3656978 * 2
def baseEnd_3656978 : Nat := 208643050768655365606319

theorem tailTrace_3656978 : CollatzResearch.WordTrace tailWord_3656978 prefixEnd_3656978 208643050768655365606319 := by
  unfold tailWord_3656978
  simp only [CollatzResearch.WordTrace]
  refine ⟨33345236336350185740894897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88920630230267161975719725 33345236336350185740894897)
  ·
    refine ⟨25008927252262639305671173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33345236336350185740894897 25008927252262639305671173)
    ·
      refine ⟨4689173859799244869813345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25008927252262639305671173 4689173859799244869813345)
      ·
        refine ⟨3516880394849433652360009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4689173859799244869813345 3516880394849433652360009)
        ·
          refine ⟨2637660296137075239270007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3516880394849433652360009 2637660296137075239270007)
          ·
            refine ⟨3956490444205612858905011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637660296137075239270007 3956490444205612858905011)
            ·
              refine ⟨5934735666308419288357517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956490444205612858905011 5934735666308419288357517)
              ·
                refine ⟨2225525874865657233134069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5934735666308419288357517 2225525874865657233134069)
                ·
                  refine ⟨208643050768655365606319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2225525874865657233134069 208643050768655365606319)
                  ·
                    rfl

theorem cell23_3656978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_3656978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656978 prefixEnd_3656978 := by exact prefixLift 3656978
  have htrace : WordTrace (prefixWord ++ tailWord_3656978) baseStart_3656978 baseEnd_3656978 := by
    simpa [prefixWord, tailWord_3656978, baseEnd_3656978] using wordTrace_append hprefix tailTrace_3656978
  have hstable : (prefixWord ++ tailWord_3656978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656978).length < 2 ^ (prefixWord ++ tailWord_3656978).sum := by decide
  have hdescent : baseEnd_3656978 < baseStart_3656978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656983 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 10]
def baseStart_3656983 : Nat := 118140960795 + 3656983 * 2 ^ 59
def prefixEnd_3656983 : Nat := 4983230072969 + 3 ^ 40 * 3656983 * 2
def baseEnd_3656983 : Nat := 208643336035685641210483

theorem tailTrace_3656983 : CollatzResearch.WordTrace tailWord_3656983 prefixEnd_3656983 208643336035685641210483 := by
  unfold tailWord_3656983
  simp only [CollatzResearch.WordTrace]
  refine ⟨133381127710382628817511603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88920751806921752545007735 133381127710382628817511603)
  ·
    refine ⟨200071691565573943226267405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133381127710382628817511603 200071691565573943226267405)
    ·
      refine ⟨75026884337090228709850277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200071691565573943226267405 75026884337090228709850277)
      ·
        refine ⟨14067540813204417883096927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75026884337090228709850277 14067540813204417883096927)
        ·
          refine ⟨21101311219806626824645391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14067540813204417883096927 21101311219806626824645391)
          ·
            refine ⟨31651966829709940236968087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21101311219806626824645391 31651966829709940236968087)
            ·
              refine ⟨47477950244564910355452131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31651966829709940236968087 47477950244564910355452131)
              ·
                refine ⟨71216925366847365533178197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47477950244564910355452131 71216925366847365533178197)
                ·
                  refine ⟨208643336035685641210483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 71216925366847365533178197 208643336035685641210483)
                  ·
                    rfl

theorem cell23_3656983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 10].length) (baseStart_3656983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656983 prefixEnd_3656983 := by exact prefixLift 3656983
  have htrace : WordTrace (prefixWord ++ tailWord_3656983) baseStart_3656983 baseEnd_3656983 := by
    simpa [prefixWord, tailWord_3656983, baseEnd_3656983] using wordTrace_append hprefix tailTrace_3656983
  have hstable : (prefixWord ++ tailWord_3656983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656983).length < 2 ^ (prefixWord ++ tailWord_3656983).sum := by decide
  have hdescent : baseEnd_3656983 < baseStart_3656983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656997 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 2, 2, 3]
def baseStart_3656997 : Nat := 118140960795 + 3656997 * 2 ^ 59
def prefixEnd_3656997 : Nat := 4983230072969 + 3 ^ 40 * 3656997 * 2
def baseEnd_3656997 : Nat := 1877797213050333716119283

theorem tailTrace_3656997 : CollatzResearch.WordTrace tailWord_3656997 prefixEnd_3656997 1877797213050333716119283 := by
  unfold tailWord_3656997
  simp only [CollatzResearch.WordTrace]
  refine ⟨133381638332331909208521245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88921092221554606139014163 133381638332331909208521245)
  ·
    refine ⟨50018114374624465953195467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133381638332331909208521245 50018114374624465953195467)
    ·
      refine ⟨75027171561936698929793201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50018114374624465953195467 75027171561936698929793201)
      ·
        refine ⟨56270378671452524197344901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75027171561936698929793201 56270378671452524197344901)
        ·
          refine ⟨10550696000897348287002169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56270378671452524197344901 10550696000897348287002169)
          ·
            refine ⟨7913022000673011215251627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10550696000897348287002169 7913022000673011215251627)
            ·
              refine ⟨11869533001009516822877441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7913022000673011215251627 11869533001009516822877441)
              ·
                refine ⟨8902149750757137617158081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11869533001009516822877441 8902149750757137617158081)
                ·
                  refine ⟨6676612313067853212868561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8902149750757137617158081 6676612313067853212868561)
                  ·
                    refine ⟨5007459234800889909651421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6676612313067853212868561 5007459234800889909651421)
                    ·
                      refine ⟨1877797213050333716119283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5007459234800889909651421 1877797213050333716119283)
                      ·
                        rfl

theorem cell23_3656997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_3656997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3656997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3656997 prefixEnd_3656997 := by exact prefixLift 3656997
  have htrace : WordTrace (prefixWord ++ tailWord_3656997) baseStart_3656997 baseEnd_3656997 := by
    simpa [prefixWord, tailWord_3656997, baseEnd_3656997] using wordTrace_append hprefix tailTrace_3656997
  have hstable : (prefixWord ++ tailWord_3656997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656997).length < 2 ^ (prefixWord ++ tailWord_3656997).sum := by decide
  have hdescent : baseEnd_3656997 < baseStart_3656997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657000 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 8]
def baseStart_3657000 : Nat := 118140960795 + 3657000 * 2 ^ 59
def prefixEnd_3657000 : Nat := 4983230072969 + 3 ^ 40 * 3657000 * 2
def baseEnd_3657000 : Nat := 208644305943588578264641

theorem tailTrace_3657000 : CollatzResearch.WordTrace tailWord_3657000 prefixEnd_3657000 208644305943588578264641 := by
  unfold tailWord_3657000
  simp only [CollatzResearch.WordTrace]
  refine ⟨66690873875660520360440227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88921165167547360480586969 66690873875660520360440227)
  ·
    refine ⟨100036310813490780540660341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66690873875660520360440227 100036310813490780540660341)
    ·
      refine ⟨9378404138764760675686907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100036310813490780540660341 9378404138764760675686907)
      ·
        refine ⟨14067606208147141013530361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9378404138764760675686907 14067606208147141013530361)
        ·
          refine ⟨10550704656110355760147771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14067606208147141013530361 10550704656110355760147771)
          ·
            refine ⟨15826056984165533640221657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10550704656110355760147771 15826056984165533640221657)
            ·
              refine ⟨11869542738124150230166243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15826056984165533640221657 11869542738124150230166243)
              ·
                refine ⟨17804314107186225345249365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11869542738124150230166243 17804314107186225345249365)
                ·
                  refine ⟨208644305943588578264641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17804314107186225345249365 208644305943588578264641)
                  ·
                    rfl

theorem cell23_3657000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 8].length) (baseStart_3657000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657000 prefixEnd_3657000 := by exact prefixLift 3657000
  have htrace : WordTrace (prefixWord ++ tailWord_3657000) baseStart_3657000 baseEnd_3657000 := by
    simpa [prefixWord, tailWord_3657000, baseEnd_3657000] using wordTrace_append hprefix tailTrace_3657000
  have hstable : (prefixWord ++ tailWord_3657000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657000).length < 2 ^ (prefixWord ++ tailWord_3657000).sum := by decide
  have hdescent : baseEnd_3657000 < baseStart_3657000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657017 : List Nat := [1, 2, 1, 6, 2, 1, 1, 3, 6]
def baseStart_3657017 : Nat := 118140960795 + 3657017 * 2 ^ 59
def prefixEnd_3657017 : Nat := 4983230072969 + 3 ^ 40 * 3657017 * 2
def baseEnd_3657017 : Nat := 208645275851491515318799

theorem tailTrace_3657017 : CollatzResearch.WordTrace tailWord_3657017 prefixEnd_3657017 208645275851491515318799 := by
  unfold tailWord_3657017
  simp only [CollatzResearch.WordTrace]
  refine ⟨133382367792259452624249305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88921578528172968416166203 133382367792259452624249305)
  ·
    refine ⟨100036775844194589468186979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133382367792259452624249305 100036775844194589468186979)
    ·
      refine ⟨150055163766291884202280469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100036775844194589468186979 150055163766291884202280469)
      ·
        refine ⟨7033835801544932071981897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150055163766291884202280469 7033835801544932071981897)
        ·
          refine ⟨5275376851158699053986423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7033835801544932071981897 5275376851158699053986423)
          ·
            refine ⟨7913065276738048580979635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275376851158699053986423 7913065276738048580979635)
            ·
              refine ⟨11869597915107072871469453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7913065276738048580979635 11869597915107072871469453)
              ·
                refine ⟨4451099218165152326801045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11869597915107072871469453 4451099218165152326801045)
                ·
                  refine ⟨208645275851491515318799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4451099218165152326801045 208645275851491515318799)
                  ·
                    rfl

theorem cell23_3657017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 3, 6].length) (baseStart_3657017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657017 prefixEnd_3657017 := by exact prefixLift 3657017
  have htrace : WordTrace (prefixWord ++ tailWord_3657017) baseStart_3657017 baseEnd_3657017 := by
    simpa [prefixWord, tailWord_3657017, baseEnd_3657017] using wordTrace_append hprefix tailTrace_3657017
  have hstable : (prefixWord ++ tailWord_3657017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657017).length < 2 ^ (prefixWord ++ tailWord_3657017).sum := by decide
  have hdescent : baseEnd_3657017 < baseStart_3657017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657084 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 3, 2, 2]
def baseStart_3657084 : Nat := 118140960795 + 3657084 * 2 ^ 59
def prefixEnd_3657084 : Nat := 4983230072969 + 3 ^ 40 * 3657084 * 2
def baseEnd_3657084 : Nat := 1877841885867274875731383

theorem tailTrace_3657084 : CollatzResearch.WordTrace tailWord_3657084 prefixEnd_3657084 1877841885867274875731383 := by
  unfold tailWord_3657084
  simp only [CollatzResearch.WordTrace]
  refine ⟨66692405741508361533469153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88923207655344482044625537 66692405741508361533469153)
  ·
    refine ⟨50019304306131271150101865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66692405741508361533469153 50019304306131271150101865)
    ·
      refine ⟨37514478229598453362576399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50019304306131271150101865 37514478229598453362576399)
      ·
        refine ⟨56271717344397680043864599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37514478229598453362576399 56271717344397680043864599)
        ·
          refine ⟨84407576016596520065796899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56271717344397680043864599 84407576016596520065796899)
          ·
            refine ⟨126611364024894780098695349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84407576016596520065796899 126611364024894780098695349)
            ·
              refine ⟨11869815377333885634252689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126611364024894780098695349 11869815377333885634252689)
              ·
                refine ⟨8902361533000414225689517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11869815377333885634252689 8902361533000414225689517)
                ·
                  refine ⟨3338385574875155334633569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8902361533000414225689517 3338385574875155334633569)
                  ·
                    refine ⟨2503789181156366500975177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3338385574875155334633569 2503789181156366500975177)
                    ·
                      refine ⟨1877841885867274875731383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2503789181156366500975177 1877841885867274875731383)
                      ·
                        rfl

theorem cell23_3657084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_3657084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657084 prefixEnd_3657084 := by exact prefixLift 3657084
  have htrace : WordTrace (prefixWord ++ tailWord_3657084) baseStart_3657084 baseEnd_3657084 := by
    simpa [prefixWord, tailWord_3657084, baseEnd_3657084] using wordTrace_append hprefix tailTrace_3657084
  have hstable : (prefixWord ++ tailWord_3657084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657084).length < 2 ^ (prefixWord ++ tailWord_3657084).sum := by decide
  have hdescent : baseEnd_3657084 < baseStart_3657084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657128 : List Nat := [2, 1, 6, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3657128 : Nat := 118140960795 + 3657128 * 2 ^ 59
def prefixEnd_3657128 : Nat := 4983230072969 + 3 ^ 40 * 3657128 * 2
def baseEnd_3657128 : Nat := 625954826338690901193727

theorem tailTrace_3657128 : CollatzResearch.WordTrace tailWord_3657128 prefixEnd_3657128 625954826338690901193727 := by
  unfold tailWord_3657128
  simp only [CollatzResearch.WordTrace]
  refine ⟨66693208147428659290770019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88924277529904879054360025 66693208147428659290770019)
  ·
    refine ⟨100039812221142988936155029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66693208147428659290770019 100039812221142988936155029)
    ·
      refine ⟨4689366197866077606382267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100039812221142988936155029 4689366197866077606382267)
      ·
        refine ⟨7034049296799116409573401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4689366197866077606382267 7034049296799116409573401)
        ·
          refine ⟨5275536972599337307180051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7034049296799116409573401 5275536972599337307180051)
          ·
            refine ⟨7913305458899005960770077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275536972599337307180051 7913305458899005960770077)
            ·
              refine ⟨2967489547087127235288779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7913305458899005960770077 2967489547087127235288779)
              ·
                refine ⟨4451234320630690852933169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967489547087127235288779 4451234320630690852933169)
                ·
                  refine ⟨3338425740473018139699877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4451234320630690852933169 3338425740473018139699877)
                  ·
                    refine ⟨625954826338690901193727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3338425740473018139699877 625954826338690901193727)
                    ·
                      rfl

theorem cell23_3657128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3657128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657128 prefixEnd_3657128 := by exact prefixLift 3657128
  have htrace : WordTrace (prefixWord ++ tailWord_3657128) baseStart_3657128 baseEnd_3657128 := by
    simpa [prefixWord, tailWord_3657128, baseEnd_3657128] using wordTrace_append hprefix tailTrace_3657128
  have hstable : (prefixWord ++ tailWord_3657128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657128).length < 2 ^ (prefixWord ++ tailWord_3657128).sum := by decide
  have hdescent : baseEnd_3657128 < baseStart_3657128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657144 : List Nat := [2, 1, 2, 1, 2, 2, 3, 4, 1, 3, 2]
def baseStart_3657144 : Nat := 118140960795 + 3657144 * 2 ^ 59
def prefixEnd_3657144 : Nat := 4983230072969 + 3 ^ 40 * 3657144 * 2
def baseEnd_3657144 : Nat := 1877872694706544640981107

theorem tailTrace_3657144 : CollatzResearch.WordTrace tailWord_3657144 prefixEnd_3657144 1877872694706544640981107 := by
  unfold tailWord_3657144
  simp only [CollatzResearch.WordTrace]
  refine ⟨66693499931399676657061243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88924666575199568876081657 66693499931399676657061243)
  ·
    refine ⟨100040249897099514985591865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66693499931399676657061243 100040249897099514985591865)
    ·
      refine ⟨75030187422824636239193899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100040249897099514985591865 75030187422824636239193899)
      ·
        refine ⟨112545281134236954358790849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75030187422824636239193899 112545281134236954358790849)
        ·
          refine ⟨84408960850677715769093137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112545281134236954358790849 84408960850677715769093137)
          ·
            refine ⟨63306720638008286826819853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84408960850677715769093137 63306720638008286826819853)
            ·
              refine ⟨23740020239253107560057445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63306720638008286826819853 23740020239253107560057445)
              ·
                refine ⟨4451253794859957667510771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23740020239253107560057445 4451253794859957667510771)
                ·
                  refine ⟨6676880692289936501266157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4451253794859957667510771 6676880692289936501266157)
                  ·
                    refine ⟨2503830259608726187974809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6676880692289936501266157 2503830259608726187974809)
                    ·
                      refine ⟨1877872694706544640981107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2503830259608726187974809 1877872694706544640981107)
                      ·
                        rfl

theorem cell23_3657144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 4, 1, 3, 2].length) (baseStart_3657144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657144 prefixEnd_3657144 := by exact prefixLift 3657144
  have htrace : WordTrace (prefixWord ++ tailWord_3657144) baseStart_3657144 baseEnd_3657144 := by
    simpa [prefixWord, tailWord_3657144, baseEnd_3657144] using wordTrace_append hprefix tailTrace_3657144
  have hstable : (prefixWord ++ tailWord_3657144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657144).length < 2 ^ (prefixWord ++ tailWord_3657144).sum := by decide
  have hdescent : baseEnd_3657144 < baseStart_3657144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657237 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_3657237 : Nat := 118140960795 + 3657237 * 2 ^ 59
def prefixEnd_3657237 : Nat := 4983230072969 + 3 ^ 40 * 3657237 * 2
def baseEnd_3657237 : Nat := 1877920448407412777118179

theorem tailTrace_3657237 : CollatzResearch.WordTrace tailWord_3657237 prefixEnd_3657237 1877920448407412777118179 := by
  unfold tailWord_3657237
  simp only [CollatzResearch.WordTrace]
  refine ⟨133390391851462430197257965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88926927900974953464838643 133390391851462430197257965)
  ·
    refine ⟨50021396944298411323971737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133390391851462430197257965 50021396944298411323971737)
    ·
      refine ⟨37516047708223808492978803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50021396944298411323971737 37516047708223808492978803)
      ·
        refine ⟨56274071562335712739468205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37516047708223808492978803 56274071562335712739468205)
        ·
          refine ⟨21102776835875892277300577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56274071562335712739468205 21102776835875892277300577)
          ·
            refine ⟨15827082626906919207975433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21102776835875892277300577 15827082626906919207975433)
            ·
              refine ⟨11870311970180189405981575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15827082626906919207975433 11870311970180189405981575)
              ·
                refine ⟨17805467955270284108972363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11870311970180189405981575 17805467955270284108972363)
                ·
                  refine ⟨26708201932905426163458545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17805467955270284108972363 26708201932905426163458545)
                  ·
                    refine ⟨20031151449679069622593909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26708201932905426163458545 20031151449679069622593909)
                    ·
                      refine ⟨1877920448407412777118179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20031151449679069622593909 1877920448407412777118179)
                      ·
                        rfl

theorem cell23_3657237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_3657237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657237 prefixEnd_3657237 := by exact prefixLift 3657237
  have htrace : WordTrace (prefixWord ++ tailWord_3657237) baseStart_3657237 baseEnd_3657237 := by
    simpa [prefixWord, tailWord_3657237, baseEnd_3657237] using wordTrace_append hprefix tailTrace_3657237
  have hstable : (prefixWord ++ tailWord_3657237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657237).length < 2 ^ (prefixWord ++ tailWord_3657237).sum := by decide
  have hdescent : baseEnd_3657237 < baseStart_3657237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657247 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 4]
def baseStart_3657247 : Nat := 118140960795 + 3657247 * 2 ^ 59
def prefixEnd_3657247 : Nat := 4983230072969 + 3 ^ 40 * 3657247 * 2
def baseEnd_3657247 : Nat := 1877925583213957737993133

theorem tailTrace_3657247 : CollatzResearch.WordTrace tailWord_3657247 prefixEnd_3657247 1877925583213957737993133 := by
  unfold tailWord_3657247
  simp only [CollatzResearch.WordTrace]
  refine ⟨133390756581426201905121995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88927171054284134603414663 133390756581426201905121995)
  ·
    refine ⟨200086134872139302857682993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133390756581426201905121995 200086134872139302857682993)
    ·
      refine ⟨150064601154104477143262245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200086134872139302857682993 150064601154104477143262245)
      ·
        refine ⟨28137112716394589464361671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150064601154104477143262245 28137112716394589464361671)
        ·
          refine ⟨42205669074591884196542507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28137112716394589464361671 42205669074591884196542507)
          ·
            refine ⟨63308503611887826294813761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42205669074591884196542507 63308503611887826294813761)
            ·
              refine ⟨47481377708915869721110321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63308503611887826294813761 47481377708915869721110321)
              ·
                refine ⟨35611033281686902290832741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47481377708915869721110321 35611033281686902290832741)
                ·
                  refine ⟨6677068740316294179531139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35611033281686902290832741 6677068740316294179531139)
                  ·
                    refine ⟨10015603110474441269296709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6677068740316294179531139 10015603110474441269296709)
                    ·
                      refine ⟨1877925583213957737993133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10015603110474441269296709 1877925583213957737993133)
                      ·
                        rfl

theorem cell23_3657247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_3657247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657247 prefixEnd_3657247 := by exact prefixLift 3657247
  have htrace : WordTrace (prefixWord ++ tailWord_3657247) baseStart_3657247 baseEnd_3657247 := by
    simpa [prefixWord, tailWord_3657247, baseEnd_3657247] using wordTrace_append hprefix tailTrace_3657247
  have hstable : (prefixWord ++ tailWord_3657247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657247).length < 2 ^ (prefixWord ++ tailWord_3657247).sum := by decide
  have hdescent : baseEnd_3657247 < baseStart_3657247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657325 : List Nat := [1, 5, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_3657325 : Nat := 118140960795 + 3657325 * 2 ^ 59
def prefixEnd_3657325 : Nat := 4983230072969 + 3 ^ 40 * 3657325 * 2
def baseEnd_3657325 : Nat := 625988544901669477605925

theorem tailTrace_3657325 : CollatzResearch.WordTrace tailWord_3657325 prefixEnd_3657325 625988544901669477605925 := by
  unfold tailWord_3657325
  simp only [CollatzResearch.WordTrace]
  refine ⟨133393601475143621226461429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88929067650095747484307619 133393601475143621226461429)
  ·
    refine ⟨12505650138294714489980759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133393601475143621226461429 12505650138294714489980759)
    ·
      refine ⟨18758475207442071734971139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12505650138294714489980759 18758475207442071734971139)
      ·
        refine ⟨28137712811163107602456709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18758475207442071734971139 28137712811163107602456709)
        ·
          refine ⟨5275821152093082675460633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28137712811163107602456709 5275821152093082675460633)
          ·
            refine ⟨3956865864069812006595475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5275821152093082675460633 3956865864069812006595475)
            ·
              refine ⟨5935298796104718009893213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956865864069812006595475 5935298796104718009893213)
              ·
                refine ⟨2225737048539269253709955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5935298796104718009893213 2225737048539269253709955)
                ·
                  refine ⟨3338605572808903880564933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2225737048539269253709955 3338605572808903880564933)
                  ·
                    refine ⟨625988544901669477605925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3338605572808903880564933 625988544901669477605925)
                    ·
                      rfl

theorem cell23_3657325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_3657325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657325 prefixEnd_3657325 := by exact prefixLift 3657325
  have htrace : WordTrace (prefixWord ++ tailWord_3657325) baseStart_3657325 baseEnd_3657325 := by
    simpa [prefixWord, tailWord_3657325, baseEnd_3657325] using wordTrace_append hprefix tailTrace_3657325
  have hstable : (prefixWord ++ tailWord_3657325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657325).length < 2 ^ (prefixWord ++ tailWord_3657325).sum := by decide
  have hdescent : baseEnd_3657325 < baseStart_3657325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657341 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 4, 3, 2]
def baseStart_3657341 : Nat := 118140960795 + 3657341 * 2 ^ 59
def prefixEnd_3657341 : Nat := 4983230072969 + 3 ^ 40 * 3657341 * 2
def baseEnd_3657341 : Nat := 1877973850395480370217701

theorem tailTrace_3657341 : CollatzResearch.WordTrace tailWord_3657341 prefixEnd_3657341 1877973850395480370217701 := by
  unfold tailWord_3657341
  simp only [CollatzResearch.WordTrace]
  refine ⟨133394185043085655959043877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88929456695390437306029251 133394185043085655959043877)
  ·
    refine ⟨25011409695578560492320727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133394185043085655959043877 25011409695578560492320727)
    ·
      refine ⟨37517114543367840738481091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25011409695578560492320727 37517114543367840738481091)
      ·
        refine ⟨56275671815051761107721637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37517114543367840738481091 56275671815051761107721637)
        ·
          refine ⟨10551688465322205207697807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56275671815051761107721637 10551688465322205207697807)
          ·
            refine ⟨15827532697983307811546711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10551688465322205207697807 15827532697983307811546711)
            ·
              refine ⟨23741299046974961717320067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15827532697983307811546711 23741299046974961717320067)
              ·
                refine ⟨35611948570462442575980101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23741299046974961717320067 35611948570462442575980101)
                ·
                  refine ⟨6677240356961707982996269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35611948570462442575980101 6677240356961707982996269)
                  ·
                    refine ⟨2503965133860640493623601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6677240356961707982996269 2503965133860640493623601)
                    ·
                      refine ⟨1877973850395480370217701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2503965133860640493623601 1877973850395480370217701)
                      ·
                        rfl

theorem cell23_3657341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_3657341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657341 prefixEnd_3657341 := by exact prefixLift 3657341
  have htrace : WordTrace (prefixWord ++ tailWord_3657341) baseStart_3657341 baseEnd_3657341 := by
    simpa [prefixWord, tailWord_3657341, baseEnd_3657341] using wordTrace_append hprefix tailTrace_3657341
  have hstable : (prefixWord ++ tailWord_3657341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657341).length < 2 ^ (prefixWord ++ tailWord_3657341).sum := by decide
  have hdescent : baseEnd_3657341 < baseStart_3657341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657375 : List Nat := [1, 1, 2, 7, 1, 1, 2, 1, 2, 3, 2]
def baseStart_3657375 : Nat := 118140960795 + 3657375 * 2 ^ 59
def prefixEnd_3657375 : Nat := 4983230072969 + 3 ^ 40 * 3657375 * 2
def baseEnd_3657375 : Nat := 1877991308737733237192545

theorem tailTrace_3657375 : CollatzResearch.WordTrace tailWord_3657375 prefixEnd_3657375 1877991308737733237192545 := by
  unfold tailWord_3657375
  simp only [CollatzResearch.WordTrace]
  refine ⟨133395425124962479765781579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88930283416641653177187719 133395425124962479765781579)
  ·
    refine ⟨200093137687443719648672369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133395425124962479765781579 200093137687443719648672369)
    ·
      refine ⟨150069853265582789736504277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200093137687443719648672369 150069853265582789736504277)
      ·
        refine ⟨3517262185912096634449319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 150069853265582789736504277 3517262185912096634449319)
        ·
          refine ⟨5275893278868144951673979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3517262185912096634449319 5275893278868144951673979)
          ·
            refine ⟨7913839918302217427510969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275893278868144951673979 7913839918302217427510969)
            ·
              refine ⟨5935379938726663070633227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7913839918302217427510969 5935379938726663070633227)
              ·
                refine ⟨8903069908089994605949841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5935379938726663070633227 8903069908089994605949841)
                ·
                  refine ⟨6677302431067495954462381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8903069908089994605949841 6677302431067495954462381)
                  ·
                    refine ⟨2503988411650310982923393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6677302431067495954462381 2503988411650310982923393)
                    ·
                      refine ⟨1877991308737733237192545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2503988411650310982923393 1877991308737733237192545)
                      ·
                        rfl

theorem cell23_3657375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_3657375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657375 prefixEnd_3657375 := by exact prefixLift 3657375
  have htrace : WordTrace (prefixWord ++ tailWord_3657375) baseStart_3657375 baseEnd_3657375 := by
    simpa [prefixWord, tailWord_3657375, baseEnd_3657375] using wordTrace_append hprefix tailTrace_3657375
  have hstable : (prefixWord ++ tailWord_3657375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657375).length < 2 ^ (prefixWord ++ tailWord_3657375).sum := by decide
  have hdescent : baseEnd_3657375 < baseStart_3657375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657405 : List Nat := [1, 4, 1, 2, 1, 2, 3, 4, 1, 2, 2]
def baseStart_3657405 : Nat := 118140960795 + 3657405 * 2 ^ 59
def prefixEnd_3657405 : Nat := 4983230072969 + 3 ^ 40 * 3657405 * 2
def baseEnd_3657405 : Nat := 1878006713157368119817407

theorem tailTrace_3657405 : CollatzResearch.WordTrace tailWord_3657405 prefixEnd_3657405 1878006713157368119817407 := by
  unfold tailWord_3657405
  simp only [CollatzResearch.WordTrace]
  refine ⟨133396519314853794889373669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88931012876569196592915779 133396519314853794889373669)
  ·
    refine ⟨25011847371535086541757563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133396519314853794889373669 25011847371535086541757563)
    ·
      refine ⟨37517771057302629812636345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25011847371535086541757563 37517771057302629812636345)
      ·
        refine ⟨28138328292976972359477259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37517771057302629812636345 28138328292976972359477259)
        ·
          refine ⟨42207492439465458539215889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28138328292976972359477259 42207492439465458539215889)
          ·
            refine ⟨31655619329599093904411917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42207492439465458539215889 31655619329599093904411917)
            ·
              refine ⟨11870857248599660214154469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31655619329599093904411917 11870857248599660214154469)
              ·
                refine ⟨2225785734112436290153963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11870857248599660214154469 2225785734112436290153963)
                ·
                  refine ⟨3338678601168654435230945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2225785734112436290153963 3338678601168654435230945)
                  ·
                    refine ⟨2504008950876490826423209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3338678601168654435230945 2504008950876490826423209)
                    ·
                      refine ⟨1878006713157368119817407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504008950876490826423209 1878006713157368119817407)
                      ·
                        rfl

theorem cell23_3657405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_3657405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657405 prefixEnd_3657405 := by exact prefixLift 3657405
  have htrace : WordTrace (prefixWord ++ tailWord_3657405) baseStart_3657405 baseEnd_3657405 := by
    simpa [prefixWord, tailWord_3657405, baseEnd_3657405] using wordTrace_append hprefix tailTrace_3657405
  have hstable : (prefixWord ++ tailWord_3657405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657405).length < 2 ^ (prefixWord ++ tailWord_3657405).sum := by decide
  have hdescent : baseEnd_3657405 < baseStart_3657405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657407 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 1, 9]
def baseStart_3657407 : Nat := 118140960795 + 3657407 * 2 ^ 59
def prefixEnd_3657407 : Nat := 4983230072969 + 3 ^ 40 * 3657407 * 2
def baseEnd_3657407 : Nat := 626002580039559037330799

theorem tailTrace_3657407 : CollatzResearch.WordTrace tailWord_3657407 prefixEnd_3657407 626002580039559037330799 := by
  unfold tailWord_3657407
  simp only [CollatzResearch.WordTrace]
  refine ⟨133396592260846549230946475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88931061507231032820630983 133396592260846549230946475)
  ·
    refine ⟨200094888391269823846419713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133396592260846549230946475 200094888391269823846419713)
    ·
      refine ⟨150071166293452367884814785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200094888391269823846419713 150071166293452367884814785)
      ·
        refine ⟨112553374720089275913611089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150071166293452367884814785 112553374720089275913611089)
        ·
          refine ⟨84415031040066956935208317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112553374720089275913611089 84415031040066956935208317)
          ·
            refine ⟨31655636640025108850703119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84415031040066956935208317 31655636640025108850703119)
            ·
              refine ⟨47483454960037663276054679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31655636640025108850703119 47483454960037663276054679)
              ·
                refine ⟨71225182440056494914082019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47483454960037663276054679 71225182440056494914082019)
                ·
                  refine ⟨106837773660084742371123029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71225182440056494914082019 106837773660084742371123029)
                  ·
                    refine ⟨626002580039559037330799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 106837773660084742371123029 626002580039559037330799)
                    ·
                      rfl

theorem cell23_3657407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_3657407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657407 prefixEnd_3657407 := by exact prefixLift 3657407
  have htrace : WordTrace (prefixWord ++ tailWord_3657407) baseStart_3657407 baseEnd_3657407 := by
    simpa [prefixWord, tailWord_3657407, baseEnd_3657407] using wordTrace_append hprefix tailTrace_3657407
  have hstable : (prefixWord ++ tailWord_3657407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657407).length < 2 ^ (prefixWord ++ tailWord_3657407).sum := by decide
  have hdescent : baseEnd_3657407 < baseStart_3657407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657431 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 3, 3, 2]
def baseStart_3657431 : Nat := 118140960795 + 3657431 * 2 ^ 59
def prefixEnd_3657431 : Nat := 4983230072969 + 3 ^ 40 * 3657431 * 2
def baseEnd_3657431 : Nat := 1878020063654385018092287

theorem tailTrace_3657431 : CollatzResearch.WordTrace tailWord_3657431 prefixEnd_3657431 1878020063654385018092287 := by
  unfold tailWord_3657431
  simp only [CollatzResearch.WordTrace]
  refine ⟨133397467612759601329820147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88931645075173067553213431 133397467612759601329820147)
  ·
    refine ⟨200096201419139401994730221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133397467612759601329820147 200096201419139401994730221)
    ·
      refine ⟨75036075532177275748023833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200096201419139401994730221 75036075532177275748023833)
      ·
        refine ⟨56277056649132956811017875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75036075532177275748023833 56277056649132956811017875)
        ·
          refine ⟨84415584973699435216526813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56277056649132956811017875 84415584973699435216526813)
          ·
            refine ⟨31655844365137288206197555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84415584973699435216526813 31655844365137288206197555)
            ·
              refine ⟨47483766547705932309296333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31655844365137288206197555 47483766547705932309296333)
              ·
                refine ⟨17806412455389724615986125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47483766547705932309296333 17806412455389724615986125)
                ·
                  refine ⟨6677404670771146730994797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17806412455389724615986125 6677404670771146730994797)
                  ·
                    refine ⟨2504026751539180024123049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6677404670771146730994797 2504026751539180024123049)
                    ·
                      refine ⟨1878020063654385018092287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504026751539180024123049 1878020063654385018092287)
                      ·
                        rfl

theorem cell23_3657431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_3657431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657431 prefixEnd_3657431 := by exact prefixLift 3657431
  have htrace : WordTrace (prefixWord ++ tailWord_3657431) baseStart_3657431 baseEnd_3657431 := by
    simpa [prefixWord, tailWord_3657431, baseEnd_3657431] using wordTrace_append hprefix tailTrace_3657431
  have hstable : (prefixWord ++ tailWord_3657431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657431).length < 2 ^ (prefixWord ++ tailWord_3657431).sum := by decide
  have hdescent : baseEnd_3657431 < baseStart_3657431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657454 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_3657454 : Nat := 118140960795 + 3657454 * 2 ^ 59
def prefixEnd_3657454 : Nat := 4983230072969 + 3 ^ 40 * 3657454 * 2
def baseEnd_3657454 : Nat := 626010624569812809368227

theorem tailTrace_3657454 : CollatzResearch.WordTrace tailWord_3657454 prefixEnd_3657454 626010624569812809368227 := by
  unfold tailWord_3657454
  simp only [CollatzResearch.WordTrace]
  refine ⟨16674788311459534532238427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88932204327784184171938277 16674788311459534532238427)
  ·
    refine ⟨25012182467189301798357641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16674788311459534532238427 25012182467189301798357641)
    ·
      refine ⟨18759136850391976348768231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25012182467189301798357641 18759136850391976348768231)
      ·
        refine ⟨28138705275587964523152347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18759136850391976348768231 28138705275587964523152347)
        ·
          refine ⟨42208057913381946784728521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28138705275587964523152347 42208057913381946784728521)
          ·
            refine ⟨31656043435036460088546391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42208057913381946784728521 31656043435036460088546391)
            ·
              refine ⟨47484065152554690132819587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31656043435036460088546391 47484065152554690132819587)
              ·
                refine ⟨71226097728832035199229381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47484065152554690132819587 71226097728832035199229381)
                ·
                  refine ⟨13354893324156006599855509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71226097728832035199229381 13354893324156006599855509)
                  ·
                    refine ⟨626010624569812809368227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13354893324156006599855509 626010624569812809368227)
                    ·
                      rfl

theorem cell23_3657454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_3657454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657454 prefixEnd_3657454 := by exact prefixLift 3657454
  have htrace : WordTrace (prefixWord ++ tailWord_3657454) baseStart_3657454 baseEnd_3657454 := by
    simpa [prefixWord, tailWord_3657454, baseEnd_3657454] using wordTrace_append hprefix tailTrace_3657454
  have hstable : (prefixWord ++ tailWord_3657454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657454).length < 2 ^ (prefixWord ++ tailWord_3657454).sum := by decide
  have hdescent : baseEnd_3657454 < baseStart_3657454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657464 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 2, 4, 3]
def baseStart_3657464 : Nat := 118140960795 + 3657464 * 2 ^ 59
def prefixEnd_3657464 : Nat := 4983230072969 + 3 ^ 40 * 3657464 * 2
def baseEnd_3657464 : Nat := 1878037008515983388979635

theorem tailTrace_3657464 : CollatzResearch.WordTrace tailWord_3657464 prefixEnd_3657464 1878037008515983388979635 := by
  unfold tailWord_3657464
  simp only [CollatzResearch.WordTrace]
  refine ⟨66699335610820023982885723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88932447481093365310514297 66699335610820023982885723)
  ·
    refine ⟨100049003416230035974328585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66699335610820023982885723 100049003416230035974328585)
    ·
      refine ⟨75036752562172526980746439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100049003416230035974328585 75036752562172526980746439)
      ·
        refine ⟨112555128843258790471119659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75036752562172526980746439 112555128843258790471119659)
        ·
          refine ⟨168832693264888185706679489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112555128843258790471119659 168832693264888185706679489)
          ·
            refine ⟨126624519948666139280009617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168832693264888185706679489 126624519948666139280009617)
            ·
              refine ⟨94968389961499604460007213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126624519948666139280009617 94968389961499604460007213)
              ·
                refine ⟨35613146235562351672502705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94968389961499604460007213 35613146235562351672502705)
                ·
                  refine ⟨26709859676671763754377029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35613146235562351672502705 26709859676671763754377029)
                  ·
                    refine ⟨5008098689375955703945693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26709859676671763754377029 5008098689375955703945693)
                    ·
                      refine ⟨1878037008515983388979635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5008098689375955703945693 1878037008515983388979635)
                      ·
                        rfl

theorem cell23_3657464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_3657464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657464 prefixEnd_3657464 := by exact prefixLift 3657464
  have htrace : WordTrace (prefixWord ++ tailWord_3657464) baseStart_3657464 baseEnd_3657464 := by
    simpa [prefixWord, tailWord_3657464, baseEnd_3657464] using wordTrace_append hprefix tailTrace_3657464
  have hstable : (prefixWord ++ tailWord_3657464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657464).length < 2 ^ (prefixWord ++ tailWord_3657464).sum := by decide
  have hdescent : baseEnd_3657464 < baseStart_3657464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657484 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 7]
def baseStart_3657484 : Nat := 118140960795 + 3657484 * 2 ^ 59
def prefixEnd_3657484 : Nat := 4983230072969 + 3 ^ 40 * 3657484 * 2
def baseEnd_3657484 : Nat := 208671919792119256747727

theorem tailTrace_3657484 : CollatzResearch.WordTrace tailWord_3657484 prefixEnd_3657484 208671919792119256747727 := by
  unfold tailWord_3657484
  simp only [CollatzResearch.WordTrace]
  refine ⟨66699700340783795690749753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88932933787711727587666337 66699700340783795690749753)
  ·
    refine ⟨50024775255587846768062315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66699700340783795690749753 50024775255587846768062315)
    ·
      refine ⟨75037162883381770152093473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50024775255587846768062315 75037162883381770152093473)
      ·
        refine ⟨56277872162536327614070105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75037162883381770152093473 56277872162536327614070105)
        ·
          refine ⟨42208404121902245710552579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56277872162536327614070105 42208404121902245710552579)
          ·
            refine ⟨63312606182853368565828869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42208404121902245710552579 63312606182853368565828869)
            ·
              refine ⟨11871113659285006606092913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63312606182853368565828869 11871113659285006606092913)
              ·
                refine ⟨8903335244463754954569685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11871113659285006606092913 8903335244463754954569685)
                ·
                  refine ⟨208671919792119256747727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8903335244463754954569685 208671919792119256747727)
                  ·
                    rfl

theorem cell23_3657484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_3657484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657484 prefixEnd_3657484 := by exact prefixLift 3657484
  have htrace : WordTrace (prefixWord ++ tailWord_3657484) baseStart_3657484 baseEnd_3657484 := by
    simpa [prefixWord, tailWord_3657484, baseEnd_3657484] using wordTrace_append hprefix tailTrace_3657484
  have hstable : (prefixWord ++ tailWord_3657484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657484).length < 2 ^ (prefixWord ++ tailWord_3657484).sum := by decide
  have hdescent : baseEnd_3657484 < baseStart_3657484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657548 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 2, 5]
def baseStart_3657548 : Nat := 118140960795 + 3657548 * 2 ^ 59
def prefixEnd_3657548 : Nat := 4983230072969 + 3 ^ 40 * 3657548 * 2
def baseEnd_3657548 : Nat := 626026713630320353443083

theorem tailTrace_3657548 : CollatzResearch.WordTrace tailWord_3657548 prefixEnd_3657548 626026713630320353443083 := by
  unfold tailWord_3657548
  simp only [CollatzResearch.WordTrace]
  refine ⟨66700867476667865155914649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88934489968890486874552865 66700867476667865155914649)
  ·
    refine ⟨50025650607500898866935987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66700867476667865155914649 50025650607500898866935987)
    ·
      refine ⟨75038475911251348300403981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50025650607500898866935987 75038475911251348300403981)
      ·
        refine ⟨28139428466719255612651493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75038475911251348300403981 28139428466719255612651493)
        ·
          refine ⟨5276142837509860427372155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28139428466719255612651493 5276142837509860427372155)
          ·
            refine ⟨7914214256264790641058233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5276142837509860427372155 7914214256264790641058233)
            ·
              refine ⟨5935660692198592980793675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7914214256264790641058233 5935660692198592980793675)
              ·
                refine ⟨8903491038297889471190513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5935660692198592980793675 8903491038297889471190513)
                ·
                  refine ⟨6677618278723417103392885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8903491038297889471190513 6677618278723417103392885)
                  ·
                    refine ⟨626026713630320353443083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6677618278723417103392885 626026713630320353443083)
                    ·
                      rfl

theorem cell23_3657548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_3657548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657548 prefixEnd_3657548 := by exact prefixLift 3657548
  have htrace : WordTrace (prefixWord ++ tailWord_3657548) baseStart_3657548 baseEnd_3657548 := by
    simpa [prefixWord, tailWord_3657548, baseEnd_3657548] using wordTrace_append hprefix tailTrace_3657548
  have hstable : (prefixWord ++ tailWord_3657548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657548).length < 2 ^ (prefixWord ++ tailWord_3657548).sum := by decide
  have hdescent : baseEnd_3657548 < baseStart_3657548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657641 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 4]
def baseStart_3657641 : Nat := 118140960795 + 3657641 * 2 ^ 59
def prefixEnd_3657641 : Nat := 4983230072969 + 3 ^ 40 * 3657641 * 2
def baseEnd_3657641 : Nat := 1878127894591829196466321

theorem tailTrace_3657641 : CollatzResearch.WordTrace tailWord_3657641 prefixEnd_3657641 1878127894591829196466321 := by
  unfold tailWord_3657641
  simp only [CollatzResearch.WordTrace]
  refine ⟨133405126941998807194964777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88936751294665871463309851 133405126941998807194964777)
  ·
    refine ⟨100053845206499105396223583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133405126941998807194964777 100053845206499105396223583)
    ·
      refine ⟨150080767809748658094335375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100053845206499105396223583 150080767809748658094335375)
      ·
        refine ⟨225121151714622987141503063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150080767809748658094335375 225121151714622987141503063)
        ·
          refine ⟨337681727571934480712254595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225121151714622987141503063 337681727571934480712254595)
          ·
            refine ⟨506522591357901721068381893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337681727571934480712254595 506522591357901721068381893)
            ·
              refine ⟨94972985879606572700321605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 506522591357901721068381893 94972985879606572700321605)
              ·
                refine ⟨17807434852426232381310301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94972985879606572700321605 17807434852426232381310301)
                ·
                  refine ⟨6677788069659837142991363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17807434852426232381310301 6677788069659837142991363)
                  ·
                    refine ⟨10016682104489755714487045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6677788069659837142991363 10016682104489755714487045)
                    ·
                      refine ⟨1878127894591829196466321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10016682104489755714487045 1878127894591829196466321)
                      ·
                        rfl

theorem cell23_3657641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_3657641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657641 prefixEnd_3657641 := by exact prefixLift 3657641
  have htrace : WordTrace (prefixWord ++ tailWord_3657641) baseStart_3657641 baseEnd_3657641 := by
    simpa [prefixWord, tailWord_3657641, baseEnd_3657641] using wordTrace_append hprefix tailTrace_3657641
  have hstable : (prefixWord ++ tailWord_3657641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657641).length < 2 ^ (prefixWord ++ tailWord_3657641).sum := by decide
  have hdescent : baseEnd_3657641 < baseStart_3657641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657671 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_3657671 : Nat := 118140960795 + 3657671 * 2 ^ 59
def prefixEnd_3657671 : Nat := 4983230072969 + 3 ^ 40 * 3657671 * 2
def baseEnd_3657671 : Nat := 1878143299011464079091183

theorem tailTrace_3657671 : CollatzResearch.WordTrace tailWord_3657671 prefixEnd_3657671 1878143299011464079091183 := by
  unfold tailWord_3657671
  simp only [CollatzResearch.WordTrace]
  refine ⟨133406221131890122318556867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88937480754593414879037911 133406221131890122318556867)
  ·
    refine ⟨200109331697835183477835301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133406221131890122318556867 200109331697835183477835301)
    ·
      refine ⟨37520499693344096902094119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200109331697835183477835301 37520499693344096902094119)
      ·
        refine ⟨56280749540016145353141179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37520499693344096902094119 56280749540016145353141179)
        ·
          refine ⟨84421124310024218029711769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56280749540016145353141179 84421124310024218029711769)
          ·
            refine ⟨63315843232518163522283827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84421124310024218029711769 63315843232518163522283827)
            ·
              refine ⟨94973764848777245283425741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63315843232518163522283827 94973764848777245283425741)
              ·
                refine ⟨35615161818291466981284653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94973764848777245283425741 35615161818291466981284653)
                ·
                  refine ⟨13355685681859300117981745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35615161818291466981284653 13355685681859300117981745)
                  ·
                    refine ⟨10016764261394475088486309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13355685681859300117981745 10016764261394475088486309)
                    ·
                      refine ⟨1878143299011464079091183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10016764261394475088486309 1878143299011464079091183)
                      ·
                        rfl

theorem cell23_3657671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_3657671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657671 prefixEnd_3657671 := by exact prefixLift 3657671
  have htrace : WordTrace (prefixWord ++ tailWord_3657671) baseStart_3657671 baseEnd_3657671 := by
    simpa [prefixWord, tailWord_3657671, baseEnd_3657671] using wordTrace_append hprefix tailTrace_3657671
  have hstable : (prefixWord ++ tailWord_3657671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657671).length < 2 ^ (prefixWord ++ tailWord_3657671).sum := by decide
  have hdescent : baseEnd_3657671 < baseStart_3657671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657678 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_3657678 : Nat := 118140960795 + 3657678 * 2 ^ 59
def prefixEnd_3657678 : Nat := 4983230072969 + 3 ^ 40 * 3657678 * 2
def baseEnd_3657678 : Nat := 1878146893376045551703651

theorem tailTrace_3657678 : CollatzResearch.WordTrace tailWord_3657678 prefixEnd_3657678 1878146893376045551703651 := by
  unfold tailWord_3657678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16675809555358095314257711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88937650961909841676041125 16675809555358095314257711)
  ·
    refine ⟨25013714333037142971386567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16675809555358095314257711 25013714333037142971386567)
    ·
      refine ⟨37520571499555714457079851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25013714333037142971386567 37520571499555714457079851)
      ·
        refine ⟨56280857249333571685619777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37520571499555714457079851 56280857249333571685619777)
        ·
          refine ⟨42210642937000178764214833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56280857249333571685619777 42210642937000178764214833)
          ·
            refine ⟨31657982202750134073161125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42210642937000178764214833 31657982202750134073161125)
            ·
              refine ⟨5935871663015650138717711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31657982202750134073161125 5935871663015650138717711)
              ·
                refine ⟨8903807494523475208076567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5935871663015650138717711 8903807494523475208076567)
                ·
                  refine ⟨13355711241785212812114851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8903807494523475208076567 13355711241785212812114851)
                  ·
                    refine ⟨20033566862677819218172277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13355711241785212812114851 20033566862677819218172277)
                    ·
                      refine ⟨1878146893376045551703651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20033566862677819218172277 1878146893376045551703651)
                      ·
                        rfl

theorem cell23_3657678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_3657678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657678 prefixEnd_3657678 := by exact prefixLift 3657678
  have htrace : WordTrace (prefixWord ++ tailWord_3657678) baseStart_3657678 baseEnd_3657678 := by
    simpa [prefixWord, tailWord_3657678, baseEnd_3657678] using wordTrace_append hprefix tailTrace_3657678
  have hstable : (prefixWord ++ tailWord_3657678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657678).length < 2 ^ (prefixWord ++ tailWord_3657678).sum := by decide
  have hdescent : baseEnd_3657678 < baseStart_3657678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657686 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_3657686 : Nat := 118140960795 + 3657686 * 2 ^ 59
def prefixEnd_3657686 : Nat := 4983230072969 + 3 ^ 40 * 3657686 * 2
def baseEnd_3657686 : Nat := 1878151001221281520403615

theorem tailTrace_3657686 : CollatzResearch.WordTrace tailWord_3657686 prefixEnd_3657686 1878151001221281520403615 := by
  unfold tailWord_3657686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8337923014177236242522057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88937845484557186586901941 8337923014177236242522057)
  ·
    refine ⟨6253442260632927181891543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8337923014177236242522057 6253442260632927181891543)
    ·
      refine ⟨9380163390949390772837315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6253442260632927181891543 9380163390949390772837315)
      ·
        refine ⟨14070245086424086159255973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9380163390949390772837315 14070245086424086159255973)
        ·
          refine ⟨2638170953704516154860495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14070245086424086159255973 2638170953704516154860495)
          ·
            refine ⟨3957256430556774232290743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638170953704516154860495 3957256430556774232290743)
            ·
              refine ⟨5935884645835161348436115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957256430556774232290743 5935884645835161348436115)
              ·
                refine ⟨8903826968752742022654173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5935884645835161348436115 8903826968752742022654173)
                ·
                  refine ⟨3338935113282278258495315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8903826968752742022654173 3338935113282278258495315)
                  ·
                    refine ⟨5008402669923417387742973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3338935113282278258495315 5008402669923417387742973)
                    ·
                      refine ⟨1878151001221281520403615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5008402669923417387742973 1878151001221281520403615)
                      ·
                        rfl

theorem cell23_3657686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_3657686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657686 prefixEnd_3657686 := by exact prefixLift 3657686
  have htrace : WordTrace (prefixWord ++ tailWord_3657686) baseStart_3657686 baseEnd_3657686 := by
    simpa [prefixWord, tailWord_3657686, baseEnd_3657686] using wordTrace_append hprefix tailTrace_3657686
  have hstable : (prefixWord ++ tailWord_3657686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657686).length < 2 ^ (prefixWord ++ tailWord_3657686).sum := by decide
  have hdescent : baseEnd_3657686 < baseStart_3657686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657709 : List Nat := [1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3657709 : Nat := 118140960795 + 3657709 * 2 ^ 59
def prefixEnd_3657709 : Nat := 4983230072969 + 3 ^ 40 * 3657709 * 2
def baseEnd_3657709 : Nat := 1878162811276334930416009

theorem tailTrace_3657709 : CollatzResearch.WordTrace tailWord_3657709 prefixEnd_3657709 1878162811276334930416009 := by
  unfold tailWord_3657709
  simp only [CollatzResearch.WordTrace]
  refine ⟨133407607105752454808440181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88938404737168303205626787 133407607105752454808440181)
  ·
    refine ⟨12506963166164292638291267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133407607105752454808440181 12506963166164292638291267)
    ·
      refine ⟨18760444749246438957436901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12506963166164292638291267 18760444749246438957436901)
      ·
        refine ⟨3517583390483707304519419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18760444749246438957436901 3517583390483707304519419)
        ·
          refine ⟨5276375085725560956779129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3517583390483707304519419 5276375085725560956779129)
          ·
            refine ⟨3957281314294170717584347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5276375085725560956779129 3957281314294170717584347)
            ·
              refine ⟨5935921971441256076376521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957281314294170717584347 5935921971441256076376521)
              ·
                refine ⟨4451941478580942057282391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5935921971441256076376521 4451941478580942057282391)
                ·
                  refine ⟨6677912217871413085923587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4451941478580942057282391 6677912217871413085923587)
                  ·
                    refine ⟨10016868326807119628885381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6677912217871413085923587 10016868326807119628885381)
                    ·
                      refine ⟨1878162811276334930416009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10016868326807119628885381 1878162811276334930416009)
                      ·
                        rfl

theorem cell23_3657709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3657709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657709 prefixEnd_3657709 := by exact prefixLift 3657709
  have htrace : WordTrace (prefixWord ++ tailWord_3657709) baseStart_3657709 baseEnd_3657709 := by
    simpa [prefixWord, tailWord_3657709, baseEnd_3657709] using wordTrace_append hprefix tailTrace_3657709
  have hstable : (prefixWord ++ tailWord_3657709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657709).length < 2 ^ (prefixWord ++ tailWord_3657709).sum := by decide
  have hdescent : baseEnd_3657709 < baseStart_3657709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657731 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 4]
def baseStart_3657731 : Nat := 118140960795 + 3657731 * 2 ^ 59
def prefixEnd_3657731 : Nat := 4983230072969 + 3 ^ 40 * 3657731 * 2
def baseEnd_3657731 : Nat := 1878174107850733844340907

theorem tailTrace_3657731 : CollatzResearch.WordTrace tailWord_3657731 prefixEnd_3657731 1878174107850733844340907 := by
  unfold tailWord_3657731
  simp only [CollatzResearch.WordTrace]
  refine ⟨133408409511672752565741047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88938939674448501710494031 133408409511672752565741047)
  ·
    refine ⟨200112614267509128848611571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133408409511672752565741047 200112614267509128848611571)
    ·
      refine ⟨300168921401263693272917357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200112614267509128848611571 300168921401263693272917357)
      ·
        refine ⟨112563345525473884977344009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300168921401263693272917357 112563345525473884977344009)
        ·
          refine ⟨84422509144105413733008007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112563345525473884977344009 84422509144105413733008007)
          ·
            refine ⟨126633763716158120599512011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84422509144105413733008007 126633763716158120599512011)
            ·
              refine ⟨189950645574237180899268017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126633763716158120599512011 189950645574237180899268017)
              ·
                refine ⟨142462984180677885674451013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189950645574237180899268017 142462984180677885674451013)
                ·
                  refine ⟨26711809533877103563959565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142462984180677885674451013 26711809533877103563959565)
                  ·
                    refine ⟨10016928575203913836484837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26711809533877103563959565 10016928575203913836484837)
                    ·
                      refine ⟨1878174107850733844340907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10016928575203913836484837 1878174107850733844340907)
                      ·
                        rfl

theorem cell23_3657731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_3657731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657731 prefixEnd_3657731 := by exact prefixLift 3657731
  have htrace : WordTrace (prefixWord ++ tailWord_3657731) baseStart_3657731 baseEnd_3657731 := by
    simpa [prefixWord, tailWord_3657731, baseEnd_3657731] using wordTrace_append hprefix tailTrace_3657731
  have hstable : (prefixWord ++ tailWord_3657731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657731).length < 2 ^ (prefixWord ++ tailWord_3657731).sum := by decide
  have hdescent : baseEnd_3657731 < baseStart_3657731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657742 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3657742 : Nat := 118140960795 + 3657742 * 2 ^ 59
def prefixEnd_3657742 : Nat := 4983230072969 + 3 ^ 40 * 3657742 * 2
def baseEnd_3657742 : Nat := 1878179756137933301303357

theorem tailTrace_3657742 : CollatzResearch.WordTrace tailWord_3657742 prefixEnd_3657742 1878179756137933301303357 := by
  unfold tailWord_3657742
  simp only [CollatzResearch.WordTrace]
  refine ⟨16676101339329112680548935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88939207143088600962927653 16676101339329112680548935)
  ·
    refine ⟨25014152008993669020823403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16676101339329112680548935 25014152008993669020823403)
    ·
      refine ⟨37521228013490503531235105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25014152008993669020823403 37521228013490503531235105)
      ·
        refine ⟨28140921010117877648426329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37521228013490503531235105 28140921010117877648426329)
        ·
          refine ⟨21105690757588408236319747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28140921010117877648426329 21105690757588408236319747)
          ·
            refine ⟨31658536136382612354479621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21105690757588408236319747 31658536136382612354479621)
            ·
              refine ⟨5935975525571739816464929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31658536136382612354479621 5935975525571739816464929)
              ·
                refine ⟨4451981644178804862348697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5935975525571739816464929 4451981644178804862348697)
                ·
                  refine ⟨3338986233134103646761523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4451981644178804862348697 3338986233134103646761523)
                  ·
                    refine ⟨5008479349701155470142285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3338986233134103646761523 5008479349701155470142285)
                    ·
                      refine ⟨1878179756137933301303357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5008479349701155470142285 1878179756137933301303357)
                      ·
                        rfl

theorem cell23_3657742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3657742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657742 prefixEnd_3657742 := by exact prefixLift 3657742
  have htrace : WordTrace (prefixWord ++ tailWord_3657742) baseStart_3657742 baseEnd_3657742 := by
    simpa [prefixWord, tailWord_3657742, baseEnd_3657742] using wordTrace_append hprefix tailTrace_3657742
  have hstable : (prefixWord ++ tailWord_3657742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657742).length < 2 ^ (prefixWord ++ tailWord_3657742).sum := by decide
  have hdescent : baseEnd_3657742 < baseStart_3657742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657765 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 1, 4, 2]
def baseStart_3657765 : Nat := 118140960795 + 3657765 * 2 ^ 59
def prefixEnd_3657765 : Nat := 4983230072969 + 3 ^ 40 * 3657765 * 2
def baseEnd_3657765 : Nat := 1878191566192986711315751

theorem tailTrace_3657765 : CollatzResearch.WordTrace tailWord_3657765 prefixEnd_3657765 1878191566192986711315751 := by
  unfold tailWord_3657765
  simp only [CollatzResearch.WordTrace]
  refine ⟨133409649593549576372478749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88939766395699717581652499 133409649593549576372478749)
  ·
    refine ⟨50028618597581091139679531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133409649593549576372478749 50028618597581091139679531)
    ·
      refine ⟨75042927896371636709519297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50028618597581091139679531 75042927896371636709519297)
      ·
        refine ⟨56282195922278727532139473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75042927896371636709519297 56282195922278727532139473)
        ·
          refine ⟨42211646941709045649104605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56282195922278727532139473 42211646941709045649104605)
          ·
            refine ⟨15829367603140892118414227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42211646941709045649104605 15829367603140892118414227)
            ·
              refine ⟨23744051404711338177621341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15829367603140892118414227 23744051404711338177621341)
              ·
                refine ⟨8904019276766751816608003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23744051404711338177621341 8904019276766751816608003)
                ·
                  refine ⟨13356028915150127724912005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8904019276766751816608003 13356028915150127724912005)
                  ·
                    refine ⟨2504255421590648948421001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13356028915150127724912005 2504255421590648948421001)
                    ·
                      refine ⟨1878191566192986711315751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504255421590648948421001 1878191566192986711315751)
                      ·
                        rfl

theorem cell23_3657765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 4, 2].length) (baseStart_3657765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657765 prefixEnd_3657765 := by exact prefixLift 3657765
  have htrace : WordTrace (prefixWord ++ tailWord_3657765) baseStart_3657765 baseEnd_3657765 := by
    simpa [prefixWord, tailWord_3657765, baseEnd_3657765] using wordTrace_append hprefix tailTrace_3657765
  have hstable : (prefixWord ++ tailWord_3657765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657765).length < 2 ^ (prefixWord ++ tailWord_3657765).sum := by decide
  have hdescent : baseEnd_3657765 < baseStart_3657765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657782 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_3657782 : Nat := 118140960795 + 3657782 * 2 ^ 59
def prefixEnd_3657782 : Nat := 4983230072969 + 3 ^ 40 * 3657782 * 2
def baseEnd_3657782 : Nat := 1878200295364113144803173

theorem tailTrace_3657782 : CollatzResearch.WordTrace tailWord_3657782 prefixEnd_3657782 1878200295364113144803173 := by
  unfold tailWord_3657782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8338141852155499267240475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88940179756325325517231733 8338141852155499267240475)
  ·
    refine ⟨12507212778233248900860713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8338141852155499267240475 12507212778233248900860713)
    ·
      refine ⟨9380409583674936675645535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12507212778233248900860713 9380409583674936675645535)
      ·
        refine ⟨14070614375512405013468303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9380409583674936675645535 14070614375512405013468303)
        ·
          refine ⟨21105921563268607520202455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14070614375512405013468303 21105921563268607520202455)
          ·
            refine ⟨31658882344902911280303683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21105921563268607520202455 31658882344902911280303683)
            ·
              refine ⟨47488323517354366920455525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31658882344902911280303683 47488323517354366920455525)
              ·
                refine ⟨8904060659503943797585411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47488323517354366920455525 8904060659503943797585411)
                ·
                  refine ⟨13356090989255915696378117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8904060659503943797585411 13356090989255915696378117)
                  ·
                    refine ⟨2504267060485484193070897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13356090989255915696378117 2504267060485484193070897)
                    ·
                      refine ⟨1878200295364113144803173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504267060485484193070897 1878200295364113144803173)
                      ·
                        rfl

theorem cell23_3657782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_3657782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657782 prefixEnd_3657782 := by exact prefixLift 3657782
  have htrace : WordTrace (prefixWord ++ tailWord_3657782) baseStart_3657782 baseEnd_3657782 := by
    simpa [prefixWord, tailWord_3657782, baseEnd_3657782] using wordTrace_append hprefix tailTrace_3657782
  have hstable : (prefixWord ++ tailWord_3657782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657782).length < 2 ^ (prefixWord ++ tailWord_3657782).sum := by decide
  have hdescent : baseEnd_3657782 < baseStart_3657782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657805 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 7]
def baseStart_3657805 : Nat := 118140960795 + 3657805 * 2 ^ 59
def prefixEnd_3657805 : Nat := 4983230072969 + 3 ^ 40 * 3657805 * 2
def baseEnd_3657805 : Nat := 208690233935462950535063

theorem tailTrace_3657805 : CollatzResearch.WordTrace tailWord_3657805 prefixEnd_3657805 208690233935462950535063 := by
  unfold tailWord_3657805
  simp only [CollatzResearch.WordTrace]
  refine ⟨133411108513404663203934869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88940739008936442135956579 133411108513404663203934869)
  ·
    refine ⟨6253645711565843587684447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133411108513404663203934869 6253645711565843587684447)
    ·
      refine ⟨9380468567348765381526671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6253645711565843587684447 9380468567348765381526671)
      ·
        refine ⟨14070702851023148072290007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9380468567348765381526671 14070702851023148072290007)
        ·
          refine ⟨21106054276534722108435011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14070702851023148072290007 21106054276534722108435011)
          ·
            refine ⟨31659081414802083162652517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21106054276534722108435011 31659081414802083162652517)
            ·
              refine ⟨5936077765275390592997347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31659081414802083162652517 5936077765275390592997347)
              ·
                refine ⟨8904116647913085889496021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936077765275390592997347 8904116647913085889496021)
                ·
                  refine ⟨208690233935462950535063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8904116647913085889496021 208690233935462950535063)
                  ·
                    rfl

theorem cell23_3657805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_3657805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657805 prefixEnd_3657805 := by exact prefixLift 3657805
  have htrace : WordTrace (prefixWord ++ tailWord_3657805) baseStart_3657805 baseEnd_3657805 := by
    simpa [prefixWord, tailWord_3657805, baseEnd_3657805] using wordTrace_append hprefix tailTrace_3657805
  have hstable : (prefixWord ++ tailWord_3657805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657805).length < 2 ^ (prefixWord ++ tailWord_3657805).sum := by decide
  have hdescent : baseEnd_3657805 < baseStart_3657805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657945 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 4]
def baseStart_3657945 : Nat := 118140960795 + 3657945 * 2 ^ 59
def prefixEnd_3657945 : Nat := 4983230072969 + 3 ^ 40 * 3657945 * 2
def baseEnd_3657945 : Nat := 1878283992710796007064923

theorem tailTrace_3657945 : CollatzResearch.WordTrace tailWord_3657945 prefixEnd_3657945 1878283992710796007064923 := by
  unfold tailWord_3657945
  simp only [CollatzResearch.WordTrace]
  refine ⟨133416214732897467114031289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88944143155264978076020859 133416214732897467114031289)
  ·
    refine ⟨100062161049673100335523467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133416214732897467114031289 100062161049673100335523467)
    ·
      refine ⟨150093241574509650503285201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100062161049673100335523467 150093241574509650503285201)
      ·
        refine ⟨112569931180882237877463901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150093241574509650503285201 112569931180882237877463901)
        ·
          refine ⟨42213724192830839204048963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112569931180882237877463901 42213724192830839204048963)
          ·
            refine ⟨63320586289246258806073445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42213724192830839204048963 63320586289246258806073445)
            ·
              refine ⟨11872609929233673526138771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63320586289246258806073445 11872609929233673526138771)
              ·
                refine ⟨17808914893850510289208157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11872609929233673526138771 17808914893850510289208157)
                ·
                  refine ⟨6678343085193941358453059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17808914893850510289208157 6678343085193941358453059)
                  ·
                    refine ⟨10017514627790912037679589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6678343085193941358453059 10017514627790912037679589)
                    ·
                      refine ⟨1878283992710796007064923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10017514627790912037679589 1878283992710796007064923)
                      ·
                        rfl

theorem cell23_3657945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_3657945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657945 prefixEnd_3657945 := by exact prefixLift 3657945
  have htrace : WordTrace (prefixWord ++ tailWord_3657945) baseStart_3657945 baseEnd_3657945 := by
    simpa [prefixWord, tailWord_3657945, baseEnd_3657945] using wordTrace_append hprefix tailTrace_3657945
  have hstable : (prefixWord ++ tailWord_3657945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657945).length < 2 ^ (prefixWord ++ tailWord_3657945).sum := by decide
  have hdescent : baseEnd_3657945 < baseStart_3657945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657949 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_3657949 : Nat := 118140960795 + 3657949 * 2 ^ 59
def prefixEnd_3657949 : Nat := 4983230072969 + 3 ^ 40 * 3657949 * 2
def baseEnd_3657949 : Nat := 1878286046633413991414905

theorem tailTrace_3657949 : CollatzResearch.WordTrace tailWord_3657949 prefixEnd_3657949 1878286046633413991414905 := by
  unfold tailWord_3657949
  simp only [CollatzResearch.WordTrace]
  refine ⟨133416360624882975797176901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88944240416588650531451267 133416360624882975797176901)
  ·
    refine ⟨25015567617165557961970669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133416360624882975797176901 25015567617165557961970669)
    ·
      refine ⟨9380837856437084235739001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25015567617165557961970669 9380837856437084235739001)
      ·
        refine ⟨7035628392327813176804251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9380837856437084235739001 7035628392327813176804251)
        ·
          refine ⟨10553442588491719765206377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7035628392327813176804251 10553442588491719765206377)
          ·
            refine ⟨7915081941368789823904783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10553442588491719765206377 7915081941368789823904783)
            ·
              refine ⟨11872622912053184735857175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915081941368789823904783 11872622912053184735857175)
              ·
                refine ⟨17808934368079777103785763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11872622912053184735857175 17808934368079777103785763)
                ·
                  refine ⟨26713401552119665655678645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17808934368079777103785763 26713401552119665655678645)
                  ·
                    refine ⟨2504381395511218655219873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26713401552119665655678645 2504381395511218655219873)
                    ·
                      refine ⟨1878286046633413991414905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504381395511218655219873 1878286046633413991414905)
                      ·
                        rfl

theorem cell23_3657949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_3657949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657949 prefixEnd_3657949 := by exact prefixLift 3657949
  have htrace : WordTrace (prefixWord ++ tailWord_3657949) baseStart_3657949 baseEnd_3657949 := by
    simpa [prefixWord, tailWord_3657949, baseEnd_3657949] using wordTrace_append hprefix tailTrace_3657949
  have hstable : (prefixWord ++ tailWord_3657949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657949).length < 2 ^ (prefixWord ++ tailWord_3657949).sum := by decide
  have hdescent : baseEnd_3657949 < baseStart_3657949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657959 : List Nat := [1, 1, 5, 3, 1, 1, 4, 1, 1, 5]
def baseStart_3657959 : Nat := 118140960795 + 3657959 * 2 ^ 59
def prefixEnd_3657959 : Nat := 4983230072969 + 3 ^ 40 * 3657959 * 2
def baseEnd_3657959 : Nat := 626097060479986317429953

theorem tailTrace_3657959 : CollatzResearch.WordTrace tailWord_3657959 prefixEnd_3657959 626097060479986317429953 := by
  unfold tailWord_3657959
  simp only [CollatzResearch.WordTrace]
  refine ⟨133416725354846747505040931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88944483569897831670027287 133416725354846747505040931)
  ·
    refine ⟨200125088032270121257561397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133416725354846747505040931 200125088032270121257561397)
    ·
      refine ⟨18761727003025323867896381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200125088032270121257561397 18761727003025323867896381)
      ·
        refine ⟨7035647626134496450461143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18761727003025323867896381 7035647626134496450461143)
        ·
          refine ⟨10553471439201744675691715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7035647626134496450461143 10553471439201744675691715)
          ·
            refine ⟨15830207158802617013537573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10553471439201744675691715 15830207158802617013537573)
            ·
              refine ⟨2968163842275490690038295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15830207158802617013537573 2968163842275490690038295)
              ·
                refine ⟨4452245763413236035057443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968163842275490690038295 4452245763413236035057443)
                ·
                  refine ⟨6678368645119854052586165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4452245763413236035057443 6678368645119854052586165)
                  ·
                    refine ⟨626097060479986317429953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6678368645119854052586165 626097060479986317429953)
                    ·
                      rfl

theorem cell23_3657959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_3657959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657959 prefixEnd_3657959 := by exact prefixLift 3657959
  have htrace : WordTrace (prefixWord ++ tailWord_3657959) baseStart_3657959 baseEnd_3657959 := by
    simpa [prefixWord, tailWord_3657959, baseEnd_3657959] using wordTrace_append hprefix tailTrace_3657959
  have hstable : (prefixWord ++ tailWord_3657959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657959).length < 2 ^ (prefixWord ++ tailWord_3657959).sum := by decide
  have hdescent : baseEnd_3657959 < baseStart_3657959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657962 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_3657962 : Nat := 118140960795 + 3657962 * 2 ^ 59
def prefixEnd_3657962 : Nat := 4983230072969 + 3 ^ 40 * 3657962 * 2
def baseEnd_3657962 : Nat := 1878292721881922440552345

theorem tailTrace_3657962 : CollatzResearch.WordTrace tailWord_3657962 prefixEnd_3657962 1878292721881922440552345 := by
  unfold tailWord_3657962
  simp only [CollatzResearch.WordTrace]
  refine ⟨33354208693458969754350035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88944556515890586011600093 33354208693458969754350035)
  ·
    refine ⟨50031313040188454631525053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33354208693458969754350035 50031313040188454631525053)
    ·
      refine ⟨18761742390070670486821895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50031313040188454631525053 18761742390070670486821895)
      ·
        refine ⟨28142613585106005730232843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18761742390070670486821895 28142613585106005730232843)
        ·
          refine ⟨42213920377659008595349265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28142613585106005730232843 42213920377659008595349265)
          ·
            refine ⟨31660440283244256446511949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42213920377659008595349265 31660440283244256446511949)
            ·
              refine ⟨11872665106216596167441981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31660440283244256446511949 11872665106216596167441981)
              ·
                refine ⟨4452249414831223562790743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11872665106216596167441981 4452249414831223562790743)
                ·
                  refine ⟨6678374122246835344186115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4452249414831223562790743 6678374122246835344186115)
                  ·
                    refine ⟨10017561183370253016279173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6678374122246835344186115 10017561183370253016279173)
                    ·
                      refine ⟨1878292721881922440552345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10017561183370253016279173 1878292721881922440552345)
                      ·
                        rfl

theorem cell23_3657962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_3657962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657962 prefixEnd_3657962 := by exact prefixLift 3657962
  have htrace : WordTrace (prefixWord ++ tailWord_3657962) baseStart_3657962 baseEnd_3657962 := by
    simpa [prefixWord, tailWord_3657962, baseEnd_3657962] using wordTrace_append hprefix tailTrace_3657962
  have hstable : (prefixWord ++ tailWord_3657962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657962).length < 2 ^ (prefixWord ++ tailWord_3657962).sum := by decide
  have hdescent : baseEnd_3657962 < baseStart_3657962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657982 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3657982 : Nat := 118140960795 + 3657982 * 2 ^ 59
def prefixEnd_3657982 : Nat := 4983230072969 + 3 ^ 40 * 3657982 * 2
def baseEnd_3657982 : Nat := 1878302991495012362302253

theorem tailTrace_3657982 : CollatzResearch.WordTrace tailWord_3657982 prefixEnd_3657982 1878302991495012362302253 := by
  unfold tailWord_3657982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16677195529220427804141025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88945042822508948288752133 16677195529220427804141025)
  ·
    refine ⟨12507896646915320853105769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16677195529220427804141025 12507896646915320853105769)
    ·
      refine ⟨9380922485186490639829327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12507896646915320853105769 9380922485186490639829327)
      ·
        refine ⟨14071383727779735959743991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9380922485186490639829327 14071383727779735959743991)
        ·
          refine ⟨21107075591669603939615987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14071383727779735959743991 21107075591669603939615987)
          ·
            refine ⟨31660613387504405909423981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21107075591669603939615987 31660613387504405909423981)
            ·
              refine ⟨11872730020314152216033993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31660613387504405909423981 11872730020314152216033993)
              ·
                refine ⟨8904547515235614162025495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11872730020314152216033993 8904547515235614162025495)
                ·
                  refine ⟨13356821272853421243038243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8904547515235614162025495 13356821272853421243038243)
                  ·
                    refine ⟨20035231909280131864557365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13356821272853421243038243 20035231909280131864557365)
                    ·
                      refine ⟨1878302991495012362302253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20035231909280131864557365 1878302991495012362302253)
                      ·
                        rfl

theorem cell23_3657982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3657982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657982 prefixEnd_3657982 := by exact prefixLift 3657982
  have htrace : WordTrace (prefixWord ++ tailWord_3657982) baseStart_3657982 baseEnd_3657982 := by
    simpa [prefixWord, tailWord_3657982, baseEnd_3657982] using wordTrace_append hprefix tailTrace_3657982
  have hstable : (prefixWord ++ tailWord_3657982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657982).length < 2 ^ (prefixWord ++ tailWord_3657982).sum := by decide
  have hdescent : baseEnd_3657982 < baseStart_3657982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657992 : List Nat := [2, 1, 3, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_3657992 : Nat := 118140960795 + 3657992 * 2 ^ 59
def prefixEnd_3657992 : Nat := 4983230072969 + 3 ^ 40 * 3657992 * 2
def baseEnd_3657992 : Nat := 1878308126301557323177207

theorem tailTrace_3657992 : CollatzResearch.WordTrace tailWord_3657992 prefixEnd_3657992 1878308126301557323177207 := by
  unfold tailWord_3657992
  simp only [CollatzResearch.WordTrace]
  refine ⟨66708964481863597070496115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88945285975818129427328153 66708964481863597070496115)
  ·
    refine ⟨100063446722795395605744173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66708964481863597070496115 100063446722795395605744173)
    ·
      refine ⟨37523792521048273352154065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100063446722795395605744173 37523792521048273352154065)
      ·
        refine ⟨28142844390786205014115549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37523792521048273352154065 28142844390786205014115549)
        ·
          refine ⟨10553566646544826880293331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28142844390786205014115549 10553566646544826880293331)
          ·
            refine ⟨15830349969817240320439997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10553566646544826880293331 15830349969817240320439997)
            ·
              refine ⟨5936381238681465120164999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15830349969817240320439997 5936381238681465120164999)
              ·
                refine ⟨8904571858022197680247499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936381238681465120164999 8904571858022197680247499)
                ·
                  refine ⟨13356857787033296520371249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8904571858022197680247499 13356857787033296520371249)
                  ·
                    refine ⟨10017643340274972390278437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13356857787033296520371249 10017643340274972390278437)
                    ·
                      refine ⟨1878308126301557323177207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10017643340274972390278437 1878308126301557323177207)
                      ·
                        rfl

theorem cell23_3657992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_3657992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3657992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3657992 prefixEnd_3657992 := by exact prefixLift 3657992
  have htrace : WordTrace (prefixWord ++ tailWord_3657992) baseStart_3657992 baseEnd_3657992 := by
    simpa [prefixWord, tailWord_3657992, baseEnd_3657992] using wordTrace_append hprefix tailTrace_3657992
  have hstable : (prefixWord ++ tailWord_3657992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657992).length < 2 ^ (prefixWord ++ tailWord_3657992).sum := by decide
  have hdescent : baseEnd_3657992 < baseStart_3657992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658030 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3658030 : Nat := 118140960795 + 3658030 * 2 ^ 59
def prefixEnd_3658030 : Nat := 4983230072969 + 3 ^ 40 * 3658030 * 2
def baseEnd_3658030 : Nat := 1878327638566428174502033

theorem tailTrace_3658030 : CollatzResearch.WordTrace tailWord_3658030 prefixEnd_3658030 1878327638566428174502033 := by
  unfold tailWord_3658030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16677414367198690828859443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88946209958393017753917029 16677414367198690828859443)
  ·
    refine ⟨25016121550798036243289165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16677414367198690828859443 25016121550798036243289165)
    ·
      refine ⟨9381045581549263591233437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25016121550798036243289165 9381045581549263591233437)
      ·
        refine ⟨3517892093080973846712539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9381045581549263591233437 3517892093080973846712539)
        ·
          refine ⟨5276838139621460770068809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3517892093080973846712539 5276838139621460770068809)
          ·
            refine ⟨3957628604716095577551607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5276838139621460770068809 3957628604716095577551607)
            ·
              refine ⟨5936442907074143366327411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957628604716095577551607 5936442907074143366327411)
              ·
                refine ⟨8904664360611215049491117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936442907074143366327411 8904664360611215049491117)
                ·
                  refine ⟨3339249135229205643559169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8904664360611215049491117 3339249135229205643559169)
                  ·
                    refine ⟨2504436851421904232669377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3339249135229205643559169 2504436851421904232669377)
                    ·
                      refine ⟨1878327638566428174502033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504436851421904232669377 1878327638566428174502033)
                      ·
                        rfl

theorem cell23_3658030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3658030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658030 prefixEnd_3658030 := by exact prefixLift 3658030
  have htrace : WordTrace (prefixWord ++ tailWord_3658030) baseStart_3658030 baseEnd_3658030 := by
    simpa [prefixWord, tailWord_3658030, baseEnd_3658030] using wordTrace_append hprefix tailTrace_3658030
  have hstable : (prefixWord ++ tailWord_3658030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658030).length < 2 ^ (prefixWord ++ tailWord_3658030).sum := by decide
  have hdescent : baseEnd_3658030 < baseStart_3658030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658035 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 4]
def baseStart_3658035 : Nat := 118140960795 + 3658035 * 2 ^ 59
def prefixEnd_3658035 : Nat := 4983230072969 + 3 ^ 40 * 3658035 * 2
def baseEnd_3658035 : Nat := 1878330205969700654939509

theorem tailTrace_3658035 : CollatzResearch.WordTrace tailWord_3658035 prefixEnd_3658035 1878330205969700654939509 := by
  unfold tailWord_3658035
  simp only [CollatzResearch.WordTrace]
  refine ⟨133419497302571412484807559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88946331535047608323205039 133419497302571412484807559)
  ·
    refine ⟨200129245953857118727211339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133419497302571412484807559 200129245953857118727211339)
    ·
      refine ⟨300193868930785678090817009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200129245953857118727211339 300193868930785678090817009)
      ·
        refine ⟨225145401698089258568112757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300193868930785678090817009 225145401698089258568112757)
        ·
          refine ⟨21107381409195867990760571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225145401698089258568112757 21107381409195867990760571)
          ·
            refine ⟨31661072113793801986140857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21107381409195867990760571 31661072113793801986140857)
            ·
              refine ⟨23745804085345351489605643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31661072113793801986140857 23745804085345351489605643)
              ·
                refine ⟨35618706128018027234408465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23745804085345351489605643 35618706128018027234408465)
                ·
                  refine ⟨26714029596013520425806349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35618706128018027234408465 26714029596013520425806349)
                  ·
                    refine ⟨10017761098505070159677381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26714029596013520425806349 10017761098505070159677381)
                    ·
                      refine ⟨1878330205969700654939509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10017761098505070159677381 1878330205969700654939509)
                      ·
                        rfl

theorem cell23_3658035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_3658035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658035 prefixEnd_3658035 := by exact prefixLift 3658035
  have htrace : WordTrace (prefixWord ++ tailWord_3658035) baseStart_3658035 baseEnd_3658035 := by
    simpa [prefixWord, tailWord_3658035, baseEnd_3658035] using wordTrace_append hprefix tailTrace_3658035
  have hstable : (prefixWord ++ tailWord_3658035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658035).length < 2 ^ (prefixWord ++ tailWord_3658035).sum := by decide
  have hdescent : baseEnd_3658035 < baseStart_3658035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658046 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_3658046 : Nat := 118140960795 + 3658046 * 2 ^ 59
def prefixEnd_3658046 : Nat := 4983230072969 + 3 ^ 40 * 3658046 * 2
def baseEnd_3658046 : Nat := 1878335854256900111901959

theorem tailTrace_3658046 : CollatzResearch.WordTrace tailWord_3658046 prefixEnd_3658046 1878335854256900111901959 := by
  unfold tailWord_3658046
  simp only [CollatzResearch.WordTrace]
  refine ⟨16677487313191445170432249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88946599003687707575638661 16677487313191445170432249)
  ·
    refine ⟨12508115484893583877824187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16677487313191445170432249 12508115484893583877824187)
    ·
      refine ⟨18762173227340375816736281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12508115484893583877824187 18762173227340375816736281)
      ·
        refine ⟨14071629920505281862552211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18762173227340375816736281 14071629920505281862552211)
        ·
          refine ⟨21107444880757922793828317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14071629920505281862552211 21107444880757922793828317)
          ·
            refine ⟨7915291830284221047685619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21107444880757922793828317 7915291830284221047685619)
            ·
              refine ⟨11872937745426331571528429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915291830284221047685619 11872937745426331571528429)
              ·
                refine ⟨4452351654534874339323161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11872937745426331571528429 4452351654534874339323161)
                ·
                  refine ⟨3339263740901155754492371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4452351654534874339323161 3339263740901155754492371)
                  ·
                    refine ⟨5008895611351733631738557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3339263740901155754492371 5008895611351733631738557)
                    ·
                      refine ⟨1878335854256900111901959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5008895611351733631738557 1878335854256900111901959)
                      ·
                        rfl

theorem cell23_3658046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_3658046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658046 prefixEnd_3658046 := by exact prefixLift 3658046
  have htrace : WordTrace (prefixWord ++ tailWord_3658046) baseStart_3658046 baseEnd_3658046 := by
    simpa [prefixWord, tailWord_3658046, baseEnd_3658046] using wordTrace_append hprefix tailTrace_3658046
  have hstable : (prefixWord ++ tailWord_3658046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658046).length < 2 ^ (prefixWord ++ tailWord_3658046).sum := by decide
  have hdescent : baseEnd_3658046 < baseStart_3658046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658055 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_3658055 : Nat := 118140960795 + 3658055 * 2 ^ 59
def prefixEnd_3658055 : Nat := 4983230072969 + 3 ^ 40 * 3658055 * 2
def baseEnd_3658055 : Nat := 1878340475582790576689417

theorem tailTrace_3658055 : CollatzResearch.WordTrace tailWord_3658055 prefixEnd_3658055 1878340475582790576689417 := by
  unfold tailWord_3658055
  simp only [CollatzResearch.WordTrace]
  refine ⟨133420226762498955900535619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88946817841665970600357079 133420226762498955900535619)
  ·
    refine ⟨200130340143748433850803429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133420226762498955900535619 200130340143748433850803429)
    ·
      refine ⟨37524438776952831347025643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200130340143748433850803429 37524438776952831347025643)
      ·
        refine ⟨56286658165429247020538465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37524438776952831347025643 56286658165429247020538465)
        ·
          refine ⟨42214993624071935265403849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56286658165429247020538465 42214993624071935265403849)
          ·
            refine ⟨31661245218053951449052887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42214993624071935265403849 31661245218053951449052887)
            ·
              refine ⟨47491867827080927173579331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31661245218053951449052887 47491867827080927173579331)
              ·
                refine ⟨71237801740621390760368997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47491867827080927173579331 71237801740621390760368997)
                ·
                  refine ⟨13357087826366510767569187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71237801740621390760368997 13357087826366510767569187)
                  ·
                    refine ⟨20035631739549766151353781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13357087826366510767569187 20035631739549766151353781)
                    ·
                      refine ⟨1878340475582790576689417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20035631739549766151353781 1878340475582790576689417)
                      ·
                        rfl

theorem cell23_3658055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_3658055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658055 prefixEnd_3658055 := by exact prefixLift 3658055
  have htrace : WordTrace (prefixWord ++ tailWord_3658055) baseStart_3658055 baseEnd_3658055 := by
    simpa [prefixWord, tailWord_3658055, baseEnd_3658055] using wordTrace_append hprefix tailTrace_3658055
  have hstable : (prefixWord ++ tailWord_3658055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658055).length < 2 ^ (prefixWord ++ tailWord_3658055).sum := by decide
  have hdescent : baseEnd_3658055 < baseStart_3658055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658105 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 1, 7]
def baseStart_3658105 : Nat := 118140960795 + 3658105 * 2 ^ 59
def prefixEnd_3658105 : Nat := 4983230072969 + 3 ^ 40 * 3658105 * 2
def baseEnd_3658105 : Nat := 626122049871838460354729

theorem tailTrace_3658105 : CollatzResearch.WordTrace tailWord_3658105 prefixEnd_3658105 626122049871838460354729 := by
  unfold tailWord_3658105
  simp only [CollatzResearch.WordTrace]
  refine ⟨133422050412317814439855769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88948033608211876293237179 133422050412317814439855769)
  ·
    refine ⟨100066537809238360829891827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133422050412317814439855769 100066537809238360829891827)
    ·
      refine ⟨150099806713857541244837741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100066537809238360829891827 150099806713857541244837741)
      ·
        refine ⟨56287427517696577966814153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150099806713857541244837741 56287427517696577966814153)
        ·
          refine ⟨42215570638272433475110615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56287427517696577966814153 42215570638272433475110615)
          ·
            refine ⟨63323355957408650212665923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42215570638272433475110615 63323355957408650212665923)
            ·
              refine ⟨94985033936112975318998885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63323355957408650212665923 94985033936112975318998885)
              ·
                refine ⟨17809693863021182872312291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94985033936112975318998885 17809693863021182872312291)
                ·
                  refine ⟨26714540794531774308468437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17809693863021182872312291 26714540794531774308468437)
                  ·
                    refine ⟨626122049871838460354729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26714540794531774308468437 626122049871838460354729)
                    ·
                      rfl

theorem cell23_3658105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_3658105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658105 prefixEnd_3658105 := by exact prefixLift 3658105
  have htrace : WordTrace (prefixWord ++ tailWord_3658105) baseStart_3658105 baseEnd_3658105 := by
    simpa [prefixWord, tailWord_3658105, baseEnd_3658105] using wordTrace_append hprefix tailTrace_3658105
  have hstable : (prefixWord ++ tailWord_3658105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658105).length < 2 ^ (prefixWord ++ tailWord_3658105).sum := by decide
  have hdescent : baseEnd_3658105 < baseStart_3658105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658126 : List Nat := [4, 1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_3658126 : Nat := 118140960795 + 3658126 * 2 ^ 59
def prefixEnd_3658126 : Nat := 4983230072969 + 3 ^ 40 * 3658126 * 2
def baseEnd_3658126 : Nat := 208708548078806644322399

theorem tailTrace_3658126 : CollatzResearch.WordTrace tailWord_3658126 prefixEnd_3658126 208708548078806644322399 := by
  unfold tailWord_3658126
  simp only [CollatzResearch.WordTrace]
  refine ⟨16677852043155216878296279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88948544230161156684246821 16677852043155216878296279)
  ·
    refine ⟨25016778064732825317444419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16677852043155216878296279 25016778064732825317444419)
    ·
      refine ⟨37525167097099237976166629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25016778064732825317444419 37525167097099237976166629)
      ·
        refine ⟨7035968830706107120531243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37525167097099237976166629 7035968830706107120531243)
        ·
          refine ⟨10553953246059160680796865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7035968830706107120531243 10553953246059160680796865)
          ·
            refine ⟨7915464934544370510597649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10553953246059160680796865 7915464934544370510597649)
            ·
              refine ⟨5936598700908277882948237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7915464934544370510597649 5936598700908277882948237)
              ·
                refine ⟨2226224512840604206105589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5936598700908277882948237 2226224512840604206105589)
                ·
                  refine ⟨208708548078806644322399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2226224512840604206105589 208708548078806644322399)
                  ·
                    rfl

theorem cell23_3658126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_3658126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658126 prefixEnd_3658126 := by exact prefixLift 3658126
  have htrace : WordTrace (prefixWord ++ tailWord_3658126) baseStart_3658126 baseEnd_3658126 := by
    simpa [prefixWord, tailWord_3658126, baseEnd_3658126] using wordTrace_append hprefix tailTrace_3658126
  have hstable : (prefixWord ++ tailWord_3658126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658126).length < 2 ^ (prefixWord ++ tailWord_3658126).sum := by decide
  have hdescent : baseEnd_3658126 < baseStart_3658126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658154 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3658154 : Nat := 118140960795 + 3658154 * 2 ^ 59
def prefixEnd_3658154 : Nat := 4983230072969 + 3 ^ 40 * 3658154 * 2
def baseEnd_3658154 : Nat := 1878391310167585689351463

theorem tailTrace_3658154 : CollatzResearch.WordTrace tailWord_3658154 prefixEnd_3658154 1878391310167585689351463 := by
  unfold tailWord_3658154
  simp only [CollatzResearch.WordTrace]
  refine ⟨33355959397285073952097379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88949225059426863872259677 33355959397285073952097379)
  ·
    refine ⟨50033939095927610928146069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33355959397285073952097379 50033939095927610928146069)
    ·
      refine ⟨2345340895121606762256847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50033939095927610928146069 2345340895121606762256847)
      ·
        refine ⟨3518011342682410143385271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345340895121606762256847 3518011342682410143385271)
        ·
          refine ⟨5277017014023615215077907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518011342682410143385271 5277017014023615215077907)
          ·
            refine ⟨7915525521035422822616861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277017014023615215077907 7915525521035422822616861)
            ·
              refine ⟨2968322070388283558481323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7915525521035422822616861 2968322070388283558481323)
              ·
                refine ⟨4452483105582425337721985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968322070388283558481323 4452483105582425337721985)
                ·
                  refine ⟨3339362329186819003291489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4452483105582425337721985 3339362329186819003291489)
                  ·
                    refine ⟨2504521746890114252468617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3339362329186819003291489 2504521746890114252468617)
                    ·
                      refine ⟨1878391310167585689351463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504521746890114252468617 1878391310167585689351463)
                      ·
                        rfl

theorem cell23_3658154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3658154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658154 prefixEnd_3658154 := by exact prefixLift 3658154
  have htrace : WordTrace (prefixWord ++ tailWord_3658154) baseStart_3658154 baseEnd_3658154 := by
    simpa [prefixWord, tailWord_3658154, baseEnd_3658154] using wordTrace_append hprefix tailTrace_3658154
  have hstable : (prefixWord ++ tailWord_3658154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658154).length < 2 ^ (prefixWord ++ tailWord_3658154).sum := by decide
  have hdescent : baseEnd_3658154 < baseStart_3658154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658162 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_3658162 : Nat := 118140960795 + 3658162 * 2 ^ 59
def prefixEnd_3658162 : Nat := 4983230072969 + 3 ^ 40 * 3658162 * 2
def baseEnd_3658162 : Nat := 1878395418012821658051425

theorem tailTrace_3658162 : CollatzResearch.WordTrace tailWord_3658162 prefixEnd_3658162 1878395418012821658051425 := by
  unfold tailWord_3658162
  simp only [CollatzResearch.WordTrace]
  refine ⟨33356032343277828293670185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88949419582074208783120493 33356032343277828293670185)
  ·
    refine ⟨25017024257458371220252639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33356032343277828293670185 25017024257458371220252639)
    ·
      refine ⟨37525536386187556830378959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25017024257458371220252639 37525536386187556830378959)
      ·
        refine ⟨56288304579281335245568439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37525536386187556830378959 56288304579281335245568439)
        ·
          refine ⟨84432456868922002868352659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56288304579281335245568439 84432456868922002868352659)
          ·
            refine ⟨126648685303383004302528989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84432456868922002868352659 126648685303383004302528989)
            ·
              refine ⟨47493256988768626613448371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126648685303383004302528989 47493256988768626613448371)
              ·
                refine ⟨71239885483152939920172557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47493256988768626613448371 71239885483152939920172557)
                ·
                  refine ⟨26714957056182352470064709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71239885483152939920172557 26714957056182352470064709)
                  ·
                    refine ⟨5009054448034191088137133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26714957056182352470064709 5009054448034191088137133)
                    ·
                      refine ⟨1878395418012821658051425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5009054448034191088137133 1878395418012821658051425)
                      ·
                        rfl

theorem cell23_3658162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_3658162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658162 prefixEnd_3658162 := by exact prefixLift 3658162
  have htrace : WordTrace (prefixWord ++ tailWord_3658162) baseStart_3658162 baseEnd_3658162 := by
    simpa [prefixWord, tailWord_3658162, baseEnd_3658162] using wordTrace_append hprefix tailTrace_3658162
  have hstable : (prefixWord ++ tailWord_3658162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658162).length < 2 ^ (prefixWord ++ tailWord_3658162).sum := by decide
  have hdescent : baseEnd_3658162 < baseStart_3658162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658169 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 3, 4]
def baseStart_3658169 : Nat := 118140960795 + 3658169 * 2 ^ 59
def prefixEnd_3658169 : Nat := 4983230072969 + 3 ^ 40 * 3658169 * 2
def baseEnd_3658169 : Nat := 626133004125801043554631

theorem tailTrace_3658169 : CollatzResearch.WordTrace tailWord_3658169 prefixEnd_3658169 626133004125801043554631 := by
  unfold tailWord_3658169
  simp only [CollatzResearch.WordTrace]
  refine ⟨133424384684085953370185561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88949589789390635580123707 133424384684085953370185561)
  ·
    refine ⟨100068288513064465027639171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133424384684085953370185561 100068288513064465027639171)
    ·
      refine ⟨150102432769596697541458757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100068288513064465027639171 150102432769596697541458757)
      ·
        refine ⟨28144206144299380789023517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150102432769596697541458757 28144206144299380789023517)
        ·
          refine ⟨10554077304112267795883819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28144206144299380789023517 10554077304112267795883819)
          ·
            refine ⟨15831115956168401693825729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10554077304112267795883819 15831115956168401693825729)
            ·
              refine ⟨11873336967126301270369297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15831115956168401693825729 11873336967126301270369297)
              ·
                refine ⟨8905002725344725952776973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11873336967126301270369297 8905002725344725952776973)
                ·
                  refine ⟨3339376022004272232291365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8905002725344725952776973 3339376022004272232291365)
                  ·
                    refine ⟨626133004125801043554631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3339376022004272232291365 626133004125801043554631)
                    ·
                      rfl

theorem cell23_3658169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 3, 4].length) (baseStart_3658169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658169 prefixEnd_3658169 := by exact prefixLift 3658169
  have htrace : WordTrace (prefixWord ++ tailWord_3658169) baseStart_3658169 baseEnd_3658169 := by
    simpa [prefixWord, tailWord_3658169, baseEnd_3658169] using wordTrace_append hprefix tailTrace_3658169
  have hstable : (prefixWord ++ tailWord_3658169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658169).length < 2 ^ (prefixWord ++ tailWord_3658169).sum := by decide
  have hdescent : baseEnd_3658169 < baseStart_3658169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658175 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_3658175 : Nat := 118140960795 + 3658175 * 2 ^ 59
def prefixEnd_3658175 : Nat := 4983230072969 + 3 ^ 40 * 3658175 * 2
def baseEnd_3658175 : Nat := 1878402093261330107188865

theorem tailTrace_3658175 : CollatzResearch.WordTrace tailWord_3658175 prefixEnd_3658175 1878402093261330107188865 := by
  unfold tailWord_3658175
  simp only [CollatzResearch.WordTrace]
  refine ⟨133424603522064216394903979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88949735681376144263269319 133424603522064216394903979)
  ·
    refine ⟨200136905283096324592355969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133424603522064216394903979 200136905283096324592355969)
    ·
      refine ⟨150102678962322243444266977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200136905283096324592355969 150102678962322243444266977)
      ·
        refine ⟨112577009221741682583200233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150102678962322243444266977 112577009221741682583200233)
        ·
          refine ⟨84432756916306261937400175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112577009221741682583200233 84432756916306261937400175)
          ·
            refine ⟨126649135374459392906100263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84432756916306261937400175 126649135374459392906100263)
            ·
              refine ⟨189973703061689089359150395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126649135374459392906100263 189973703061689089359150395)
              ·
                refine ⟨284960554592533634038725593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189973703061689089359150395 284960554592533634038725593)
                ·
                  refine ⟨213720415944400225529044195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 284960554592533634038725593 213720415944400225529044195)
                  ·
                    refine ⟨320580623916600338293566293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 213720415944400225529044195 320580623916600338293566293)
                    ·
                      refine ⟨1878402093261330107188865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 320580623916600338293566293 1878402093261330107188865)
                      ·
                        rfl

theorem cell23_3658175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_3658175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658175 prefixEnd_3658175 := by exact prefixLift 3658175
  have htrace : WordTrace (prefixWord ++ tailWord_3658175) baseStart_3658175 baseEnd_3658175 := by
    simpa [prefixWord, tailWord_3658175, baseEnd_3658175] using wordTrace_append hprefix tailTrace_3658175
  have hstable : (prefixWord ++ tailWord_3658175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658175).length < 2 ^ (prefixWord ++ tailWord_3658175).sum := by decide
  have hdescent : baseEnd_3658175 < baseStart_3658175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658177 : List Nat := [1, 2, 7, 1, 2, 1, 1, 3, 5]
def baseStart_3658177 : Nat := 118140960795 + 3658177 * 2 ^ 59
def prefixEnd_3658177 : Nat := 4983230072969 + 3 ^ 40 * 3658177 * 2
def baseEnd_3658177 : Nat := 208711457802515455484873

theorem tailTrace_3658177 : CollatzResearch.WordTrace tailWord_3658177 prefixEnd_3658177 208711457802515455484873 := by
  unfold tailWord_3658177
  simp only [CollatzResearch.WordTrace]
  refine ⟨133424676468056970736476785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88949784312037980490984523 133424676468056970736476785)
  ·
    refine ⟨100068507351042728052357589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133424676468056970736476785 100068507351042728052357589)
    ·
      refine ⟨2345355641040063938727131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 100068507351042728052357589 2345355641040063938727131)
      ·
        refine ⟨3518033461560095908090697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345355641040063938727131 3518033461560095908090697)
        ·
          refine ⟨2638525096170071931068023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3518033461560095908090697 2638525096170071931068023)
          ·
            refine ⟨3957787644255107896602035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638525096170071931068023 3957787644255107896602035)
            ·
              refine ⟨5936681466382661844903053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957787644255107896602035 5936681466382661844903053)
              ·
                refine ⟨2226255549893498191838645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5936681466382661844903053 2226255549893498191838645)
                ·
                  refine ⟨208711457802515455484873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2226255549893498191838645 208711457802515455484873)
                  ·
                    rfl

theorem cell23_3658177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 3, 5].length) (baseStart_3658177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658177 prefixEnd_3658177 := by exact prefixLift 3658177
  have htrace : WordTrace (prefixWord ++ tailWord_3658177) baseStart_3658177 baseEnd_3658177 := by
    simpa [prefixWord, tailWord_3658177, baseEnd_3658177] using wordTrace_append hprefix tailTrace_3658177
  have hstable : (prefixWord ++ tailWord_3658177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658177).length < 2 ^ (prefixWord ++ tailWord_3658177).sum := by decide
  have hdescent : baseEnd_3658177 < baseStart_3658177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658195 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 3, 11]
def baseStart_3658195 : Nat := 118140960795 + 3658195 * 2 ^ 59
def prefixEnd_3658195 : Nat := 4983230072969 + 3 ^ 40 * 3658195 * 2
def baseEnd_3658195 : Nat := 626137454291473342979591

theorem tailTrace_3658195 : CollatzResearch.WordTrace tailWord_3658195 prefixEnd_3658195 626137454291473342979591 := by
  unfold tailWord_3658195
  simp only [CollatzResearch.WordTrace]
  refine ⟨133425332981991759810632039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88950221987994506540421359 133425332981991759810632039)
  ·
    refine ⟨200137999472987639715948059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133425332981991759810632039 200137999472987639715948059)
    ·
      refine ⟨300206999209481459573922089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200137999472987639715948059 300206999209481459573922089)
      ·
        refine ⟨225155249407111094680441567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300206999209481459573922089 225155249407111094680441567)
        ·
          refine ⟨337732874110666642020662351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225155249407111094680441567 337732874110666642020662351)
          ·
            refine ⟨506599311165999963030993527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337732874110666642020662351 506599311165999963030993527)
            ·
              refine ⟨759898966748999944546490291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506599311165999963030993527 759898966748999944546490291)
              ·
                refine ⟨1139848450123499916819735437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 759898966748999944546490291 1139848450123499916819735437)
                ·
                  refine ⟨427443168796312468807400789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139848450123499916819735437 427443168796312468807400789)
                  ·
                    refine ⟨626137454291473342979591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 427443168796312468807400789 626137454291473342979591)
                    ·
                      rfl

theorem cell23_3658195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 11].length) (baseStart_3658195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658195 prefixEnd_3658195 := by exact prefixLift 3658195
  have htrace : WordTrace (prefixWord ++ tailWord_3658195) baseStart_3658195 baseEnd_3658195 := by
    simpa [prefixWord, tailWord_3658195, baseEnd_3658195] using wordTrace_append hprefix tailTrace_3658195
  have hstable : (prefixWord ++ tailWord_3658195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658195).length < 2 ^ (prefixWord ++ tailWord_3658195).sum := by decide
  have hdescent : baseEnd_3658195 < baseStart_3658195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658196 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_3658196 : Nat := 118140960795 + 3658196 * 2 ^ 59
def prefixEnd_3658196 : Nat := 4983230072969 + 3 ^ 40 * 3658196 * 2
def baseEnd_3658196 : Nat := 1878412876355074525026269

theorem tailTrace_3658196 : CollatzResearch.WordTrace tailWord_3658196 prefixEnd_3658196 1878412876355074525026269 := by
  unfold tailWord_3658196
  simp only [CollatzResearch.WordTrace]
  refine ⟨66712684727494068490709221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88950246303325424654278961 66712684727494068490709221)
  ·
    refine ⟨12508628386405137842007979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66712684727494068490709221 12508628386405137842007979)
    ·
      refine ⟨18762942579607706763011969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12508628386405137842007979 18762942579607706763011969)
      ·
        refine ⟨14072206934705780072258977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18762942579607706763011969 14072206934705780072258977)
        ·
          refine ⟨10554155201029335054194233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14072206934705780072258977 10554155201029335054194233)
          ·
            refine ⟨7915616400772001290645675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10554155201029335054194233 7915616400772001290645675)
            ·
              refine ⟨11873424601158001935968513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915616400772001290645675 11873424601158001935968513)
              ·
                refine ⟨8905068450868501451976385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11873424601158001935968513 8905068450868501451976385)
                ·
                  refine ⟨6678801338151376088982289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8905068450868501451976385 6678801338151376088982289)
                  ·
                    refine ⟨5009101003613532066736717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6678801338151376088982289 5009101003613532066736717)
                    ·
                      refine ⟨1878412876355074525026269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5009101003613532066736717 1878412876355074525026269)
                      ·
                        rfl

theorem cell23_3658196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_3658196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658196 prefixEnd_3658196 := by exact prefixLift 3658196
  have htrace : WordTrace (prefixWord ++ tailWord_3658196) baseStart_3658196 baseEnd_3658196 := by
    simpa [prefixWord, tailWord_3658196, baseEnd_3658196] using wordTrace_append hprefix tailTrace_3658196
  have hstable : (prefixWord ++ tailWord_3658196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658196).length < 2 ^ (prefixWord ++ tailWord_3658196).sum := by decide
  have hdescent : baseEnd_3658196 < baseStart_3658196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658216 : List Nat := [2, 1, 4, 1, 1, 5, 2, 1, 6]
def baseStart_3658216 : Nat := 118140960795 + 3658216 * 2 ^ 59
def prefixEnd_3658216 : Nat := 4983230072969 + 3 ^ 40 * 3658216 * 2
def baseEnd_3658216 : Nat := 208713682885351605197353

theorem tailTrace_3658216 : CollatzResearch.WordTrace tailWord_3658216 prefixEnd_3658216 208713682885351605197353 := by
  unfold tailWord_3658216
  simp only [CollatzResearch.WordTrace]
  refine ⟨66713049457457840198573251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88950732609943786931431001 66713049457457840198573251)
  ·
    refine ⟨100069574186186760297859877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66713049457457840198573251 100069574186186760297859877)
    ·
      refine ⟨18763045159910017555848727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100069574186186760297859877 18763045159910017555848727)
      ·
        refine ⟨28144567739865026333773091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18763045159910017555848727 28144567739865026333773091)
        ·
          refine ⟨42216851609797539500659637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28144567739865026333773091 42216851609797539500659637)
          ·
            refine ⟨3957829838418519328186841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42216851609797539500659637 3957829838418519328186841)
            ·
              refine ⟨2968372378813889496140131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3957829838418519328186841 2968372378813889496140131)
              ·
                refine ⟨4452558568220834244210197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968372378813889496140131 4452558568220834244210197)
                ·
                  refine ⟨208713682885351605197353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4452558568220834244210197 208713682885351605197353)
                  ·
                    rfl

theorem cell23_3658216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 6].length) (baseStart_3658216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658216 prefixEnd_3658216 := by exact prefixLift 3658216
  have htrace : WordTrace (prefixWord ++ tailWord_3658216) baseStart_3658216 baseEnd_3658216 := by
    simpa [prefixWord, tailWord_3658216, baseEnd_3658216] using wordTrace_append hprefix tailTrace_3658216
  have hstable : (prefixWord ++ tailWord_3658216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658216).length < 2 ^ (prefixWord ++ tailWord_3658216).sum := by decide
  have hdescent : baseEnd_3658216 < baseStart_3658216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658219 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 4, 3, 2]
def baseStart_3658219 : Nat := 118140960795 + 3658219 * 2 ^ 59
def prefixEnd_3658219 : Nat := 4983230072969 + 3 ^ 40 * 3658219 * 2
def baseEnd_3658219 : Nat := 1878424686410127935038663

theorem tailTrace_3658219 : CollatzResearch.WordTrace tailWord_3658219 prefixEnd_3658219 1878424686410127935038663 := by
  unfold tailWord_3658219
  simp only [CollatzResearch.WordTrace]
  refine ⟨133426208333904811909505711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88950805555936541273003807 133426208333904811909505711)
  ·
    refine ⟨200139312500857217864258567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133426208333904811909505711 200139312500857217864258567)
    ·
      refine ⟨300208968751285826796387851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200139312500857217864258567 300208968751285826796387851)
      ·
        refine ⟨450313453126928740194581777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300208968751285826796387851 450313453126928740194581777)
        ·
          refine ⟨337735089845196555145936333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450313453126928740194581777 337735089845196555145936333)
          ·
            refine ⟨126650658691948708179726125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337735089845196555145936333 126650658691948708179726125)
            ·
              refine ⟨47493997009480765567397297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126650658691948708179726125 47493997009480765567397297)
              ·
                refine ⟨35620497757110574175547973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47493997009480765567397297 35620497757110574175547973)
                ·
                  refine ⟨6678843329458232657915245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35620497757110574175547973 6678843329458232657915245)
                  ·
                    refine ⟨2504566248546837246718217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6678843329458232657915245 2504566248546837246718217)
                    ·
                      refine ⟨1878424686410127935038663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504566248546837246718217 1878424686410127935038663)
                      ·
                        rfl

theorem cell23_3658219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 3, 2].length) (baseStart_3658219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658219 prefixEnd_3658219 := by exact prefixLift 3658219
  have htrace : WordTrace (prefixWord ++ tailWord_3658219) baseStart_3658219 baseEnd_3658219 := by
    simpa [prefixWord, tailWord_3658219, baseEnd_3658219] using wordTrace_append hprefix tailTrace_3658219
  have hstable : (prefixWord ++ tailWord_3658219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658219).length < 2 ^ (prefixWord ++ tailWord_3658219).sum := by decide
  have hdescent : baseEnd_3658219 < baseStart_3658219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658300 : List Nat := [2, 2, 2, 2, 3, 1, 1, 5, 1, 2, 2]
def baseStart_3658300 : Nat := 118140960795 + 3658300 * 2 ^ 59
def prefixEnd_3658300 : Nat := 4983230072969 + 3 ^ 40 * 3658300 * 2
def baseEnd_3658300 : Nat := 1878466278343142118125791

theorem tailTrace_3658300 : CollatzResearch.WordTrace tailWord_3658300 prefixEnd_3658300 1878466278343142118125791 := by
  unfold tailWord_3658300
  simp only [CollatzResearch.WordTrace]
  refine ⟨66714581323305681371602177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88952775097740908495469569 66714581323305681371602177)
  ·
    refine ⟨50035935992479261028701633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66714581323305681371602177 50035935992479261028701633)
    ·
      refine ⟨37526951994359445771526225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50035935992479261028701633 37526951994359445771526225)
      ·
        refine ⟨28145213995769584328644669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37526951994359445771526225 28145213995769584328644669)
        ·
          refine ⟨10554455248413594123241751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28145213995769584328644669 10554455248413594123241751)
          ·
            refine ⟨15831682872620391184862627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10554455248413594123241751 15831682872620391184862627)
            ·
              refine ⟨23747524308930586777293941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15831682872620391184862627 23747524308930586777293941)
              ·
                refine ⟨2226330403962242510371307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23747524308930586777293941 2226330403962242510371307)
                ·
                  refine ⟨3339495605943363765556961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226330403962242510371307 3339495605943363765556961)
                  ·
                    refine ⟨2504621704457522824167721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3339495605943363765556961 2504621704457522824167721)
                    ·
                      refine ⟨1878466278343142118125791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504621704457522824167721 1878466278343142118125791)
                      ·
                        rfl

theorem cell23_3658300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_3658300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658300 prefixEnd_3658300 := by exact prefixLift 3658300
  have htrace : WordTrace (prefixWord ++ tailWord_3658300) baseStart_3658300 baseEnd_3658300 := by
    simpa [prefixWord, tailWord_3658300, baseEnd_3658300] using wordTrace_append hprefix tailTrace_3658300
  have hstable : (prefixWord ++ tailWord_3658300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658300).length < 2 ^ (prefixWord ++ tailWord_3658300).sum := by decide
  have hdescent : baseEnd_3658300 < baseStart_3658300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658310 : List Nat := [6, 1, 1, 1, 2, 1, 3, 2, 2, 4]
def baseStart_3658310 : Nat := 118140960795 + 3658310 * 2 ^ 59
def prefixEnd_3658310 : Nat := 4983230072969 + 3 ^ 40 * 3658310 * 2
def baseEnd_3658310 : Nat := 626157137716562359666915

theorem tailTrace_3658310 : CollatzResearch.WordTrace tailWord_3658310 prefixEnd_3658310 626157137716562359666915 := by
  unfold tailWord_3658310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4169672730517972951595887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88953018251050089634045589 4169672730517972951595887)
  ·
    refine ⟨6254509095776959427393831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4169672730517972951595887 6254509095776959427393831)
    ·
      refine ⟨9381763643665439141090747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6254509095776959427393831 9381763643665439141090747)
      ·
        refine ⟨14072645465498158711636121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9381763643665439141090747 14072645465498158711636121)
        ·
          refine ⟨10554484099123619033727091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14072645465498158711636121 10554484099123619033727091)
          ·
            refine ⟨15831726148685428550590637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10554484099123619033727091 15831726148685428550590637)
            ·
              refine ⟨5936897305757035706471489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15831726148685428550590637 5936897305757035706471489)
              ·
                refine ⟨4452672979317776779853617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5936897305757035706471489 4452672979317776779853617)
                ·
                  refine ⟨3339504734488332584890213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4452672979317776779853617 3339504734488332584890213)
                  ·
                    refine ⟨626157137716562359666915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3339504734488332584890213 626157137716562359666915)
                    ·
                      rfl

theorem cell23_3658310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_3658310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658310 prefixEnd_3658310 := by exact prefixLift 3658310
  have htrace : WordTrace (prefixWord ++ tailWord_3658310) baseStart_3658310 baseEnd_3658310 := by
    simpa [prefixWord, tailWord_3658310, baseEnd_3658310] using wordTrace_append hprefix tailTrace_3658310
  have hstable : (prefixWord ++ tailWord_3658310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658310).length < 2 ^ (prefixWord ++ tailWord_3658310).sum := by decide
  have hdescent : baseEnd_3658310 < baseStart_3658310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658316 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 4, 1, 3]
def baseStart_3658316 : Nat := 118140960795 + 3658316 * 2 ^ 59
def prefixEnd_3658316 : Nat := 4983230072969 + 3 ^ 40 * 3658316 * 2
def baseEnd_3658316 : Nat := 1878474494033614055525717

theorem tailTrace_3658316 : CollatzResearch.WordTrace tailWord_3658316 prefixEnd_3658316 1878474494033614055525717 := by
  unfold tailWord_3658316
  simp only [CollatzResearch.WordTrace]
  refine ⟨66714873107276698737893401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88953164143035598317191201 66714873107276698737893401)
  ·
    refine ⟨50036154830457524053420051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66714873107276698737893401 50036154830457524053420051)
    ·
      refine ⟨75054232245686286080130077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50036154830457524053420051 75054232245686286080130077)
      ·
        refine ⟨28145337092132357280048779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75054232245686286080130077 28145337092132357280048779)
        ·
          refine ⟨42218005638198535920073169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28145337092132357280048779 42218005638198535920073169)
          ·
            refine ⟨31663504228648901940054877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42218005638198535920073169 31663504228648901940054877)
            ·
              refine ⟨11873814085743338227520579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31663504228648901940054877 11873814085743338227520579)
              ·
                refine ⟨17810721128615007341280869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11873814085743338227520579 17810721128615007341280869)
                ·
                  refine ⟨3339510211615313876490163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17810721128615007341280869 3339510211615313876490163)
                  ·
                    refine ⟨5009265317422970814735245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3339510211615313876490163 5009265317422970814735245)
                    ·
                      refine ⟨1878474494033614055525717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5009265317422970814735245 1878474494033614055525717)
                      ·
                        rfl

theorem cell23_3658316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_3658316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658316 prefixEnd_3658316 := by exact prefixLift 3658316
  have htrace : WordTrace (prefixWord ++ tailWord_3658316) baseStart_3658316 baseEnd_3658316 := by
    simpa [prefixWord, tailWord_3658316, baseEnd_3658316] using wordTrace_append hprefix tailTrace_3658316
  have hstable : (prefixWord ++ tailWord_3658316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658316).length < 2 ^ (prefixWord ++ tailWord_3658316).sum := by decide
  have hdescent : baseEnd_3658316 < baseStart_3658316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658317 : List Nat := [1, 6, 1, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_3658317 : Nat := 118140960795 + 3658317 * 2 ^ 59
def prefixEnd_3658317 : Nat := 4983230072969 + 3 ^ 40 * 3658317 * 2
def baseEnd_3658317 : Nat := 1878475007514268551613213

theorem tailTrace_3658317 : CollatzResearch.WordTrace tailWord_3658317 prefixEnd_3658317 1878475007514268551613213 := by
  unfold tailWord_3658317
  simp only [CollatzResearch.WordTrace]
  refine ⟨133429782687549774646573205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88953188458366516431048803 133429782687549774646573205)
  ·
    refine ⟨6254521063478895686558119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133429782687549774646573205 6254521063478895686558119)
    ·
      refine ⟨9381781595218343529837179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6254521063478895686558119 9381781595218343529837179)
      ·
        refine ⟨14072672392827515294755769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9381781595218343529837179 14072672392827515294755769)
        ·
          refine ⟨10554504294620636471066827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14072672392827515294755769 10554504294620636471066827)
          ·
            refine ⟨15831756441930954706600241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10554504294620636471066827 15831756441930954706600241)
            ·
              refine ⟨11873817331448216029950181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15831756441930954706600241 11873817331448216029950181)
              ·
                refine ⟨2226340749646540505615659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11873817331448216029950181 2226340749646540505615659)
                ·
                  refine ⟨3339511124469810758423489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226340749646540505615659 3339511124469810758423489)
                  ·
                    refine ⟨2504633343352358068817617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3339511124469810758423489 2504633343352358068817617)
                    ·
                      refine ⟨1878475007514268551613213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504633343352358068817617 1878475007514268551613213)
                      ·
                        rfl

theorem cell23_3658317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_3658317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658317 prefixEnd_3658317 := by exact prefixLift 3658317
  have htrace : WordTrace (prefixWord ++ tailWord_3658317) baseStart_3658317 baseEnd_3658317 := by
    simpa [prefixWord, tailWord_3658317, baseEnd_3658317] using wordTrace_append hprefix tailTrace_3658317
  have hstable : (prefixWord ++ tailWord_3658317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658317).length < 2 ^ (prefixWord ++ tailWord_3658317).sum := by decide
  have hdescent : baseEnd_3658317 < baseStart_3658317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658373 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 4, 2, 2]
def baseStart_3658373 : Nat := 118140960795 + 3658373 * 2 ^ 59
def prefixEnd_3658373 : Nat := 4983230072969 + 3 ^ 40 * 3658373 * 2
def baseEnd_3658373 : Nat := 1878503762430920332512955

theorem tailTrace_3658373 : CollatzResearch.WordTrace tailWord_3658373 prefixEnd_3658373 1878503762430920332512955 := by
  unfold tailWord_3658373
  simp only [CollatzResearch.WordTrace]
  refine ⟨133431825175346896210611773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88954550116897930807074515 133431825175346896210611773)
  ·
    refine ⟨50036934440755086078979415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133431825175346896210611773 50036934440755086078979415)
    ·
      refine ⟨75055401661132629118469123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50036934440755086078979415 75055401661132629118469123)
      ·
        refine ⟨112583102491698943677703685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75055401661132629118469123 112583102491698943677703685)
        ·
          refine ⟨21109331717193551939569441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112583102491698943677703685 21109331717193551939569441)
          ·
            refine ⟨15831998787895163954677081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21109331717193551939569441 15831998787895163954677081)
            ·
              refine ⟨11873999090921372966007811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15831998787895163954677081 11873999090921372966007811)
              ·
                refine ⟨17810998636382059449011717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11873999090921372966007811 17810998636382059449011717)
                ·
                  refine ⟨3339562244321636146689697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17810998636382059449011717 3339562244321636146689697)
                  ·
                    refine ⟨2504671683241227110017273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3339562244321636146689697 2504671683241227110017273)
                    ·
                      refine ⟨1878503762430920332512955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504671683241227110017273 1878503762430920332512955)
                      ·
                        rfl

theorem cell23_3658373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 4, 2, 2].length) (baseStart_3658373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658373 prefixEnd_3658373 := by exact prefixLift 3658373
  have htrace : WordTrace (prefixWord ++ tailWord_3658373) baseStart_3658373 baseEnd_3658373 := by
    simpa [prefixWord, tailWord_3658373, baseEnd_3658373] using wordTrace_append hprefix tailTrace_3658373
  have hstable : (prefixWord ++ tailWord_3658373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658373).length < 2 ^ (prefixWord ++ tailWord_3658373).sum := by decide
  have hdescent : baseEnd_3658373 < baseStart_3658373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658394 : List Nat := [3, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3658394 : Nat := 118140960795 + 3658394 * 2 ^ 59
def prefixEnd_3658394 : Nat := 4983230072969 + 3 ^ 40 * 3658394 * 2
def baseEnd_3658394 : Nat := 1878514545524664750350359

theorem tailTrace_3658394 : CollatzResearch.WordTrace tailWord_3658394 prefixEnd_3658394 1878514545524664750350359 := by
  unfold tailWord_3658394
  simp only [CollatzResearch.WordTrace]
  refine ⟨33358147777067704199281559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88955060738847211198084157 33358147777067704199281559)
  ·
    refine ⟨50037221665601556298922339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33358147777067704199281559 50037221665601556298922339)
    ·
      refine ⟨75055832498402334448383509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50037221665601556298922339 75055832498402334448383509)
      ·
        refine ⟨3518242148362609427267977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75055832498402334448383509 3518242148362609427267977)
        ·
          refine ⟨2638681611271957070450983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3518242148362609427267977 2638681611271957070450983)
          ·
            refine ⟨3958022416907935605676475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638681611271957070450983 3958022416907935605676475)
            ·
              refine ⟨5937033625361903408514713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958022416907935605676475 5937033625361903408514713)
              ·
                refine ⟨4452775219021427556386035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5937033625361903408514713 4452775219021427556386035)
                ·
                  refine ⟨6679162828532141334579053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4452775219021427556386035 6679162828532141334579053)
                  ·
                    refine ⟨2504686060699553000467145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6679162828532141334579053 2504686060699553000467145)
                    ·
                      refine ⟨1878514545524664750350359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504686060699553000467145 1878514545524664750350359)
                      ·
                        rfl

theorem cell23_3658394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3658394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658394 prefixEnd_3658394 := by exact prefixLift 3658394
  have htrace : WordTrace (prefixWord ++ tailWord_3658394) baseStart_3658394 baseEnd_3658394 := by
    simpa [prefixWord, tailWord_3658394, baseEnd_3658394] using wordTrace_append hprefix tailTrace_3658394
  have hstable : (prefixWord ++ tailWord_3658394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658394).length < 2 ^ (prefixWord ++ tailWord_3658394).sum := by decide
  have hdescent : baseEnd_3658394 < baseStart_3658394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658409 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 2, 5]
def baseStart_3658409 : Nat := 118140960795 + 3658409 * 2 ^ 59
def prefixEnd_3658409 : Nat := 4983230072969 + 3 ^ 40 * 3658409 * 2
def baseEnd_3658409 : Nat := 626174082578160730554263

theorem tailTrace_3658409 : CollatzResearch.WordTrace tailWord_3658409 prefixEnd_3658409 626174082578160730554263 := by
  unfold tailWord_3658409
  simp only [CollatzResearch.WordTrace]
  refine ⟨133433138203216474358922281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88955425468810982905948187 133433138203216474358922281)
  ·
    refine ⟨100074853652412355769191711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133433138203216474358922281 100074853652412355769191711)
    ·
      refine ⟨150112280478618533653787567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100074853652412355769191711 150112280478618533653787567)
      ·
        refine ⟨225168420717927800480681351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150112280478618533653787567 225168420717927800480681351)
        ·
          refine ⟨337752631076891700721022027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225168420717927800480681351 337752631076891700721022027)
          ·
            refine ⟨506628946615337551081533041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337752631076891700721022027 506628946615337551081533041)
            ·
              refine ⟨379971709961503163311149781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506628946615337551081533041 379971709961503163311149781)
              ·
                refine ⟨8905586952222730390105073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 379971709961503163311149781 8905586952222730390105073)
                ·
                  refine ⟨6679190214167047792578805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8905586952222730390105073 6679190214167047792578805)
                  ·
                    refine ⟨626174082578160730554263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6679190214167047792578805 626174082578160730554263)
                    ·
                      rfl

theorem cell23_3658409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_3658409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658409 prefixEnd_3658409 := by exact prefixLift 3658409
  have htrace : WordTrace (prefixWord ++ tailWord_3658409) baseStart_3658409 baseEnd_3658409 := by
    simpa [prefixWord, tailWord_3658409, baseEnd_3658409] using wordTrace_append hprefix tailTrace_3658409
  have hstable : (prefixWord ++ tailWord_3658409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658409).length < 2 ^ (prefixWord ++ tailWord_3658409).sum := by decide
  have hdescent : baseEnd_3658409 < baseStart_3658409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658419 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 5]
def baseStart_3658419 : Nat := 118140960795 + 3658419 * 2 ^ 59
def prefixEnd_3658419 : Nat := 4983230072969 + 3 ^ 40 * 3658419 * 2
def baseEnd_3658419 : Nat := 1878527382541027152537743

theorem tailTrace_3658419 : CollatzResearch.WordTrace tailWord_3658419 prefixEnd_3658419 1878527382541027152537743 := by
  unfold tailWord_3658419
  simp only [CollatzResearch.WordTrace]
  refine ⟨133433502933180246066786311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88955668622120164044524207 133433502933180246066786311)
  ·
    refine ⟨200150254399770369100179467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133433502933180246066786311 200150254399770369100179467)
    ·
      refine ⟨300225381599655553650269201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200150254399770369100179467 300225381599655553650269201)
      ·
        refine ⟨225169036199741665237701901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300225381599655553650269201 225169036199741665237701901)
        ·
          refine ⟨84438388574903124464138213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225169036199741665237701901 84438388574903124464138213)
          ·
            refine ⟨15832197857794335837025915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84438388574903124464138213 15832197857794335837025915)
            ·
              refine ⟨23748296786691503755538873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15832197857794335837025915 23748296786691503755538873)
              ·
                refine ⟨17811222590018627816654155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23748296786691503755538873 17811222590018627816654155)
                ·
                  refine ⟨26716833885027941724981233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17811222590018627816654155 26716833885027941724981233)
                  ·
                    refine ⟨20037625413770956293735925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26716833885027941724981233 20037625413770956293735925)
                    ·
                      refine ⟨1878527382541027152537743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20037625413770956293735925 1878527382541027152537743)
                      ·
                        rfl

theorem cell23_3658419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_3658419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658419 prefixEnd_3658419 := by exact prefixLift 3658419
  have htrace : WordTrace (prefixWord ++ tailWord_3658419) baseStart_3658419 baseEnd_3658419 := by
    simpa [prefixWord, tailWord_3658419, baseEnd_3658419] using wordTrace_append hprefix tailTrace_3658419
  have hstable : (prefixWord ++ tailWord_3658419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658419).length < 2 ^ (prefixWord ++ tailWord_3658419).sum := by decide
  have hdescent : baseEnd_3658419 < baseStart_3658419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658436 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3658436 : Nat := 118140960795 + 3658436 * 2 ^ 59
def prefixEnd_3658436 : Nat := 4983230072969 + 3 ^ 40 * 3658436 * 2
def baseEnd_3658436 : Nat := 1878536111712153586025165

theorem tailTrace_3658436 : CollatzResearch.WordTrace tailWord_3658436 prefixEnd_3658436 1878536111712153586025165 := by
  unfold tailWord_3658436
  simp only [CollatzResearch.WordTrace]
  refine ⟨66717061487059328985077581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88956081982745771980103441 66717061487059328985077581)
  ·
    refine ⟨25018898057647248369404093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66717061487059328985077581 25018898057647248369404093)
    ·
      refine ⟨9382086771617718138526535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25018898057647248369404093 9382086771617718138526535)
      ·
        refine ⟨14073130157426577207789803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9382086771617718138526535 14073130157426577207789803)
        ·
          refine ⟨21109695236139865811684705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14073130157426577207789803 21109695236139865811684705)
          ·
            refine ⟨15832271427104899358763529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21109695236139865811684705 15832271427104899358763529)
            ·
              refine ⟨11874203570328674519072647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15832271427104899358763529 11874203570328674519072647)
              ·
                refine ⟨17811305355493011778608971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11874203570328674519072647 17811305355493011778608971)
                ·
                  refine ⟨26716958033239517667913457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17811305355493011778608971 26716958033239517667913457)
                  ·
                    refine ⟨20037718524929638250935093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26716958033239517667913457 20037718524929638250935093)
                    ·
                      refine ⟨1878536111712153586025165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20037718524929638250935093 1878536111712153586025165)
                      ·
                        rfl

theorem cell23_3658436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3658436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658436 prefixEnd_3658436 := by exact prefixLift 3658436
  have htrace : WordTrace (prefixWord ++ tailWord_3658436) baseStart_3658436 baseEnd_3658436 := by
    simpa [prefixWord, tailWord_3658436, baseEnd_3658436] using wordTrace_append hprefix tailTrace_3658436
  have hstable : (prefixWord ++ tailWord_3658436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658436).length < 2 ^ (prefixWord ++ tailWord_3658436).sum := by decide
  have hdescent : baseEnd_3658436 < baseStart_3658436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658456 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 5, 4]
def baseStart_3658456 : Nat := 118140960795 + 3658456 * 2 ^ 59
def prefixEnd_3658456 : Nat := 4983230072969 + 3 ^ 40 * 3658456 * 2
def baseEnd_3658456 : Nat := 626182127108414502591691

theorem tailTrace_3658456 : CollatzResearch.WordTrace tailWord_3658456 prefixEnd_3658456 626182127108414502591691 := by
  unfold tailWord_3658456
  simp only [CollatzResearch.WordTrace]
  refine ⟨66717426217023100692941611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88956568289364134257255481 66717426217023100692941611)
  ·
    refine ⟨100076139325534651039412417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66717426217023100692941611 100076139325534651039412417)
    ·
      refine ⟨75057104494150988279559313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100076139325534651039412417 75057104494150988279559313)
      ·
        refine ⟨56292828370613241209669485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75057104494150988279559313 56292828370613241209669485)
        ·
          refine ⟨21109810638979965453626057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56292828370613241209669485 21109810638979965453626057)
          ·
            refine ⟨15832357979234974090219543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21109810638979965453626057 15832357979234974090219543)
            ·
              refine ⟨23748536968852461135329315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15832357979234974090219543 23748536968852461135329315)
              ·
                refine ⟨35622805453278691702993973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23748536968852461135329315 35622805453278691702993973)
                ·
                  refine ⟨3339638011244877347155685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35622805453278691702993973 3339638011244877347155685)
                  ·
                    refine ⟨626182127108414502591691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3339638011244877347155685 626182127108414502591691)
                    ·
                      rfl

theorem cell23_3658456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_3658456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658456 prefixEnd_3658456 := by exact prefixLift 3658456
  have htrace : WordTrace (prefixWord ++ tailWord_3658456) baseStart_3658456 baseEnd_3658456 := by
    simpa [prefixWord, tailWord_3658456, baseEnd_3658456] using wordTrace_append hprefix tailTrace_3658456
  have hstable : (prefixWord ++ tailWord_3658456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658456).length < 2 ^ (prefixWord ++ tailWord_3658456).sum := by decide
  have hdescent : baseEnd_3658456 < baseStart_3658456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658460 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3658460 : Nat := 118140960795 + 3658460 * 2 ^ 59
def prefixEnd_3658460 : Nat := 4983230072969 + 3 ^ 40 * 3658460 * 2
def baseEnd_3658460 : Nat := 626182811749287164041685

theorem tailTrace_3658460 : CollatzResearch.WordTrace tailWord_3658460 prefixEnd_3658460 626182811749287164041685 := by
  unfold tailWord_3658460
  simp only [CollatzResearch.WordTrace]
  refine ⟨66717499163015855034514417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88956665550687806712685889 66717499163015855034514417)
  ·
    refine ⟨50038124372261891275885813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66717499163015855034514417 50038124372261891275885813)
    ·
      refine ⟨4691074159899552307114295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50038124372261891275885813 4691074159899552307114295)
      ·
        refine ⟨7036611239849328460671443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4691074159899552307114295 7036611239849328460671443)
        ·
          refine ⟨10554916859773992691007165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7036611239849328460671443 10554916859773992691007165)
          ·
            refine ⟨3958093822415247259127687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10554916859773992691007165 3958093822415247259127687)
            ·
              refine ⟨5937140733622870888691531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958093822415247259127687 5937140733622870888691531)
              ·
                refine ⟨8905711100434306333037297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5937140733622870888691531 8905711100434306333037297)
                ·
                  refine ⟨6679283325325729749777973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8905711100434306333037297 6679283325325729749777973)
                  ·
                    refine ⟨626182811749287164041685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6679283325325729749777973 626182811749287164041685)
                    ·
                      rfl

theorem cell23_3658460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3658460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658460 prefixEnd_3658460 := by exact prefixLift 3658460
  have htrace : WordTrace (prefixWord ++ tailWord_3658460) baseStart_3658460 baseEnd_3658460 := by
    simpa [prefixWord, tailWord_3658460, baseEnd_3658460] using wordTrace_append hprefix tailTrace_3658460
  have hstable : (prefixWord ++ tailWord_3658460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658460).length < 2 ^ (prefixWord ++ tailWord_3658460).sum := by decide
  have hdescent : baseEnd_3658460 < baseStart_3658460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658463 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 4]
def baseStart_3658463 : Nat := 118140960795 + 3658463 * 2 ^ 59
def prefixEnd_3658463 : Nat := 4983230072969 + 3 ^ 40 * 3658463 * 2
def baseEnd_3658463 : Nat := 1878549975689824980387541

theorem tailTrace_3658463 : CollatzResearch.WordTrace tailWord_3658463 prefixEnd_3658463 1878549975689824980387541 := by
  unfold tailWord_3658463
  simp only [CollatzResearch.WordTrace]
  refine ⟨133435107745020841581388043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88956738496680561054258695 133435107745020841581388043)
  ·
    refine ⟨200152661617531262372082065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133435107745020841581388043 200152661617531262372082065)
    ·
      refine ⟨150114496213148446779061549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200152661617531262372082065 150114496213148446779061549)
      ·
        refine ⟨56292936079930667542148081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150114496213148446779061549 56292936079930667542148081)
        ·
          refine ⟨42219702059948000656611061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56292936079930667542148081 42219702059948000656611061)
          ·
            refine ⟨3958097068120125061557287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42219702059948000656611061 3958097068120125061557287)
            ·
              refine ⟨5937145602180187592335931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958097068120125061557287 5937145602180187592335931)
              ·
                refine ⟨8905718403270281388503897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5937145602180187592335931 8905718403270281388503897)
                ·
                  refine ⟨6679288802452711041377923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8905718403270281388503897 6679288802452711041377923)
                  ·
                    refine ⟨10018933203679066562066885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6679288802452711041377923 10018933203679066562066885)
                    ·
                      refine ⟨1878549975689824980387541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10018933203679066562066885 1878549975689824980387541)
                      ·
                        rfl

theorem cell23_3658463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_3658463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658463 prefixEnd_3658463 := by exact prefixLift 3658463
  have htrace : WordTrace (prefixWord ++ tailWord_3658463) baseStart_3658463 baseEnd_3658463 := by
    simpa [prefixWord, tailWord_3658463, baseEnd_3658463] using wordTrace_append hprefix tailTrace_3658463
  have hstable : (prefixWord ++ tailWord_3658463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658463).length < 2 ^ (prefixWord ++ tailWord_3658463).sum := by decide
  have hdescent : baseEnd_3658463 < baseStart_3658463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658473 : List Nat := [1, 2, 1, 1, 1, 2, 5, 5, 1, 4]
def baseStart_3658473 : Nat := 118140960795 + 3658473 * 2 ^ 59
def prefixEnd_3658473 : Nat := 4983230072969 + 3 ^ 40 * 3658473 * 2
def baseEnd_3658473 : Nat := 626185036832123313754165

theorem tailTrace_3658473 : CollatzResearch.WordTrace tailWord_3658473 prefixEnd_3658473 626185036832123313754165 := by
  unfold tailWord_3658473
  simp only [CollatzResearch.WordTrace]
  refine ⟨133435472474984613289252073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88956981649989742192834715 133435472474984613289252073)
  ·
    refine ⟨100076604356238459966939055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133435472474984613289252073 100076604356238459966939055)
    ·
      refine ⟨150114906534357689950408583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100076604356238459966939055 150114906534357689950408583)
      ·
        refine ⟨225172359801536534925612875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150114906534357689950408583 225172359801536534925612875)
        ·
          refine ⟨337758539702304802388419313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225172359801536534925612875 337758539702304802388419313)
          ·
            refine ⟨253318904776728601791314485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337758539702304802388419313 253318904776728601791314485)
            ·
              refine ⟨23748647322818306417935733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253318904776728601791314485 23748647322818306417935733)
              ·
                refine ⟨2226435686514216226681475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23748647322818306417935733 2226435686514216226681475)
                ·
                  refine ⟨3339653529771324340022213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226435686514216226681475 3339653529771324340022213)
                  ·
                    refine ⟨626185036832123313754165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3339653529771324340022213 626185036832123313754165)
                    ·
                      rfl

theorem cell23_3658473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5, 1, 4].length) (baseStart_3658473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658473 prefixEnd_3658473 := by exact prefixLift 3658473
  have htrace : WordTrace (prefixWord ++ tailWord_3658473) baseStart_3658473 baseEnd_3658473 := by
    simpa [prefixWord, tailWord_3658473, baseEnd_3658473] using wordTrace_append hprefix tailTrace_3658473
  have hstable : (prefixWord ++ tailWord_3658473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658473).length < 2 ^ (prefixWord ++ tailWord_3658473).sum := by decide
  have hdescent : baseEnd_3658473 < baseStart_3658473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658486 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_3658486 : Nat := 118140960795 + 3658486 * 2 ^ 59
def prefixEnd_3658486 : Nat := 4983230072969 + 3 ^ 40 * 3658486 * 2
def baseEnd_3658486 : Nat := 208729087304986487822215

theorem tailTrace_3658486 : CollatzResearch.WordTrace tailWord_3658486 prefixEnd_3658486 208729087304986487822215 := by
  unfold tailWord_3658486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8339746663996094781842207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88957297749291677672983541 8339746663996094781842207)
  ·
    refine ⟨12509619995994142172763311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8339746663996094781842207 12509619995994142172763311)
    ·
      refine ⟨18764429993991213259144967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12509619995994142172763311 18764429993991213259144967)
      ·
        refine ⟨28146644990986819888717451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18764429993991213259144967 28146644990986819888717451)
        ·
          refine ⟨42219967486480229833076177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28146644990986819888717451 42219967486480229833076177)
          ·
            refine ⟨31664975614860172374807133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42219967486480229833076177 31664975614860172374807133)
            ·
              refine ⟨11874365855572564640552675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31664975614860172374807133 11874365855572564640552675)
              ·
                refine ⟨17811548783358846960829013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11874365855572564640552675 17811548783358846960829013)
                ·
                  refine ⟨208729087304986487822215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17811548783358846960829013 208729087304986487822215)
                  ·
                    rfl

theorem cell23_3658486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_3658486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658486 prefixEnd_3658486 := by exact prefixLift 3658486
  have htrace : WordTrace (prefixWord ++ tailWord_3658486) baseStart_3658486 baseEnd_3658486 := by
    simpa [prefixWord, tailWord_3658486, baseEnd_3658486] using wordTrace_append hprefix tailTrace_3658486
  have hstable : (prefixWord ++ tailWord_3658486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658486).length < 2 ^ (prefixWord ++ tailWord_3658486).sum := by decide
  have hdescent : baseEnd_3658486 < baseStart_3658486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658513 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 3, 1, 3]
def baseStart_3658513 : Nat := 118140960795 + 3658513 * 2 ^ 59
def prefixEnd_3658513 : Nat := 4983230072969 + 3 ^ 40 * 3658513 * 2
def baseEnd_3658513 : Nat := 1878575649722549784762311

theorem tailTrace_3658513 : CollatzResearch.WordTrace tailWord_3658513 prefixEnd_3658513 1878575649722549784762311 := by
  unfold tailWord_3658513
  simp only [CollatzResearch.WordTrace]
  refine ⟨133436931394839700120708193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88957954263226466747138795 133436931394839700120708193)
  ·
    refine ⟨100077698546129775090531145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133436931394839700120708193 100077698546129775090531145)
    ·
      refine ⟨75058273909597331317898359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100077698546129775090531145 75058273909597331317898359)
      ·
        refine ⟨112587410864395996976847539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75058273909597331317898359 112587410864395996976847539)
        ·
          refine ⟨168881116296593995465271309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112587410864395996976847539 168881116296593995465271309)
          ·
            refine ⟨63330418611222748299476741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168881116296593995465271309 63330418611222748299476741)
            ·
              refine ⟨11874453489604265306151889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63330418611222748299476741 11874453489604265306151889)
              ·
                refine ⟨8905840117203198979613917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11874453489604265306151889 8905840117203198979613917)
                ·
                  refine ⟨3339690043951199617355219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8905840117203198979613917 3339690043951199617355219)
                  ·
                    refine ⟨5009535065926799426032829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3339690043951199617355219 5009535065926799426032829)
                    ·
                      refine ⟨1878575649722549784762311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5009535065926799426032829 1878575649722549784762311)
                      ·
                        rfl

theorem cell23_3658513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_3658513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658513 prefixEnd_3658513 := by exact prefixLift 3658513
  have htrace : WordTrace (prefixWord ++ tailWord_3658513) baseStart_3658513 baseEnd_3658513 := by
    simpa [prefixWord, tailWord_3658513, baseEnd_3658513] using wordTrace_append hprefix tailTrace_3658513
  have hstable : (prefixWord ++ tailWord_3658513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658513).length < 2 ^ (prefixWord ++ tailWord_3658513).sum := by decide
  have hdescent : baseEnd_3658513 < baseStart_3658513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658541 : List Nat := [1, 5, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_3658541 : Nat := 118140960795 + 3658541 * 2 ^ 59
def prefixEnd_3658541 : Nat := 4983230072969 + 3 ^ 40 * 3658541 * 2
def baseEnd_3658541 : Nat := 626196675726958558404061

theorem tailTrace_3658541 : CollatzResearch.WordTrace tailWord_3658541 prefixEnd_3658541 626196675726958558404061 := by
  unfold tailWord_3658541
  simp only [CollatzResearch.WordTrace]
  refine ⟨133437952638738260902727477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88958635092492173935151651 133437952638738260902727477)
  ·
    refine ⟨12509808059881711959630701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133437952638738260902727477 12509808059881711959630701)
    ·
      refine ⟨4691178022455641984861513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12509808059881711959630701 4691178022455641984861513)
      ·
        refine ⟨3518383516841731488646135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4691178022455641984861513 3518383516841731488646135)
        ·
          refine ⟨5277575275262597232969203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518383516841731488646135 5277575275262597232969203)
          ·
            refine ⟨7916362912893895849453805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277575275262597232969203 7916362912893895849453805)
            ·
              refine ⟨2968636092335210943545177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7916362912893895849453805 2968636092335210943545177)
              ·
                refine ⟨2226477069251408207658883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2968636092335210943545177 2226477069251408207658883)
                ·
                  refine ⟨3339715603877112311488325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226477069251408207658883 3339715603877112311488325)
                  ·
                    refine ⟨626196675726958558404061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3339715603877112311488325 626196675726958558404061)
                    ·
                      rfl

theorem cell23_3658541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_3658541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658541 prefixEnd_3658541 := by exact prefixLift 3658541
  have htrace : WordTrace (prefixWord ++ tailWord_3658541) baseStart_3658541 baseEnd_3658541 := by
    simpa [prefixWord, tailWord_3658541, baseEnd_3658541] using wordTrace_append hprefix tailTrace_3658541
  have hstable : (prefixWord ++ tailWord_3658541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658541).length < 2 ^ (prefixWord ++ tailWord_3658541).sum := by decide
  have hdescent : baseEnd_3658541 < baseStart_3658541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658556 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_3658556 : Nat := 118140960795 + 3658556 * 2 ^ 59
def prefixEnd_3658556 : Nat := 4983230072969 + 3 ^ 40 * 3658556 * 2
def baseEnd_3658556 : Nat := 1878597729390693116524613

theorem tailTrace_3658556 : CollatzResearch.WordTrace tailWord_3658556 prefixEnd_3658556 1878597729390693116524613 := by
  unfold tailWord_3658556
  simp only [CollatzResearch.WordTrace]
  refine ⟨66719249866841959232261761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88958999822455945643015681 66719249866841959232261761)
  ·
    refine ⟨50039437400131469424196321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66719249866841959232261761 50039437400131469424196321)
    ·
      refine ⟨37529578050098602068147241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50039437400131469424196321 37529578050098602068147241)
      ·
        refine ⟨28147183537573951551110431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37529578050098602068147241 28147183537573951551110431)
        ·
          refine ⟨42220775306360927326665647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28147183537573951551110431 42220775306360927326665647)
          ·
            refine ⟨63331162959541390989998471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42220775306360927326665647 63331162959541390989998471)
            ·
              refine ⟨94996744439312086484997707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63331162959541390989998471 94996744439312086484997707)
              ·
                refine ⟨142495116658968129727496561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94996744439312086484997707 142495116658968129727496561)
                ·
                  refine ⟨106871337494226097295622421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142495116658968129727496561 106871337494226097295622421)
                  ·
                    refine ⟨5009593945041848310732301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106871337494226097295622421 5009593945041848310732301)
                    ·
                      refine ⟨1878597729390693116524613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5009593945041848310732301 1878597729390693116524613)
                      ·
                        rfl

theorem cell23_3658556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_3658556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658556 prefixEnd_3658556 := by exact prefixLift 3658556
  have htrace : WordTrace (prefixWord ++ tailWord_3658556) baseStart_3658556 baseEnd_3658556 := by
    simpa [prefixWord, tailWord_3658556, baseEnd_3658556] using wordTrace_append hprefix tailTrace_3658556
  have hstable : (prefixWord ++ tailWord_3658556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658556).length < 2 ^ (prefixWord ++ tailWord_3658556).sum := by decide
  have hdescent : baseEnd_3658556 < baseStart_3658556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658563 : List Nat := [1, 1, 1, 3, 1, 4, 3, 3, 2, 4]
def baseStart_3658563 : Nat := 118140960795 + 3658563 * 2 ^ 59
def prefixEnd_3658563 : Nat := 4983230072969 + 3 ^ 40 * 3658563 * 2
def baseEnd_3658563 : Nat := 626200441251758196379027

theorem tailTrace_3658563 : CollatzResearch.WordTrace tailWord_3658563 prefixEnd_3658563 626200441251758196379027 := by
  unfold tailWord_3658563
  simp only [CollatzResearch.WordTrace]
  refine ⟨133438755044658558660028343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88959170029772372440018895 133438755044658558660028343)
  ·
    refine ⟨200158132566987837990042515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133438755044658558660028343 200158132566987837990042515)
    ·
      refine ⟨300237198850481756985063773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200158132566987837990042515 300237198850481756985063773)
      ·
        refine ⟨112588949568930658869398915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300237198850481756985063773 112588949568930658869398915)
        ·
          refine ⟨168883424353395988304098373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112588949568930658869398915 168883424353395988304098373)
          ·
            refine ⟨31665642066261747807018445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168883424353395988304098373 31665642066261747807018445)
            ·
              refine ⟨11874615774848155427631917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31665642066261747807018445 11874615774848155427631917)
              ·
                refine ⟨4452980915568058285361969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11874615774848155427631917 4452980915568058285361969)
                ·
                  refine ⟨3339735686676043714021477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4452980915568058285361969 3339735686676043714021477)
                  ·
                    refine ⟨626200441251758196379027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3339735686676043714021477 626200441251758196379027)
                    ·
                      rfl

theorem cell23_3658563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3, 2, 4].length) (baseStart_3658563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658563 prefixEnd_3658563 := by exact prefixLift 3658563
  have htrace : WordTrace (prefixWord ++ tailWord_3658563) baseStart_3658563 baseEnd_3658563 := by
    simpa [prefixWord, tailWord_3658563, baseEnd_3658563] using wordTrace_append hprefix tailTrace_3658563
  have hstable : (prefixWord ++ tailWord_3658563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658563).length < 2 ^ (prefixWord ++ tailWord_3658563).sum := by decide
  have hdescent : baseEnd_3658563 < baseStart_3658563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658583 : List Nat := [1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_3658583 : Nat := 118140960795 + 3658583 * 2 ^ 59
def prefixEnd_3658583 : Nat := 4983230072969 + 3 ^ 40 * 3658583 * 2
def baseEnd_3658583 : Nat := 1878611593368364510886989

theorem tailTrace_3658583 : CollatzResearch.WordTrace tailWord_3658583 prefixEnd_3658583 1878611593368364510886989 := by
  unfold tailWord_3658583
  simp only [CollatzResearch.WordTrace]
  refine ⟨133439484504586102075756403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88959656336390734717170935 133439484504586102075756403)
  ·
    refine ⟨200159226756879153113634605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133439484504586102075756403 200159226756879153113634605)
    ·
      refine ⟨75059710033829682417612977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200159226756879153113634605 75059710033829682417612977)
      ·
        refine ⟨56294782525372261813209733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75059710033829682417612977 56294782525372261813209733)
        ·
          refine ⟨10555271723507299089976825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56294782525372261813209733 10555271723507299089976825)
          ·
            refine ⟨7916453792630474317482619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10555271723507299089976825 7916453792630474317482619)
            ·
              refine ⟨11874680688945711476223929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7916453792630474317482619 11874680688945711476223929)
              ·
                refine ⟨8906010516709283607167947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11874680688945711476223929 8906010516709283607167947)
                ·
                  refine ⟨13359015775063925410751921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8906010516709283607167947 13359015775063925410751921)
                  ·
                    refine ⟨10019261831297944058063941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13359015775063925410751921 10019261831297944058063941)
                    ·
                      refine ⟨1878611593368364510886989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10019261831297944058063941 1878611593368364510886989)
                      ·
                        rfl

theorem cell23_3658583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_3658583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658583 prefixEnd_3658583 := by exact prefixLift 3658583
  have htrace : WordTrace (prefixWord ++ tailWord_3658583) baseStart_3658583 baseEnd_3658583 := by
    simpa [prefixWord, tailWord_3658583, baseEnd_3658583] using wordTrace_append hprefix tailTrace_3658583
  have hstable : (prefixWord ++ tailWord_3658583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658583).length < 2 ^ (prefixWord ++ tailWord_3658583).sum := by decide
  have hdescent : baseEnd_3658583 < baseStart_3658583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658603 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 4, 1, 3]
def baseStart_3658603 : Nat := 118140960795 + 3658603 * 2 ^ 59
def prefixEnd_3658603 : Nat := 4983230072969 + 3 ^ 40 * 3658603 * 2
def baseEnd_3658603 : Nat := 1878621862981454432636897

theorem tailTrace_3658603 : CollatzResearch.WordTrace tailWord_3658603 prefixEnd_3658603 1878621862981454432636897 := by
  unfold tailWord_3658603
  simp only [CollatzResearch.WordTrace]
  refine ⟨133440213964513645491484463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88960142643009096994322975 133440213964513645491484463)
  ·
    refine ⟨200160320946770468237226695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133440213964513645491484463 200160320946770468237226695)
    ·
      refine ⟨300240481420155702355840043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200160320946770468237226695 300240481420155702355840043)
      ·
        refine ⟨450360722130233553533760065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300240481420155702355840043 450360722130233553533760065)
        ·
          refine ⟨337770541597675165150320049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450360722130233553533760065 337770541597675165150320049)
          ·
            refine ⟨253327906198256373862740037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337770541597675165150320049 253327906198256373862740037)
            ·
              refine ⟨47498982412173070099263757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253327906198256373862740037 47498982412173070099263757)
              ·
                refine ⟨17812118404564901287223909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47498982412173070099263757 17812118404564901287223909)
                ·
                  refine ⟨3339772200855918991354483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17812118404564901287223909 3339772200855918991354483)
                  ·
                    refine ⟨5009658301283878487031725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3339772200855918991354483 5009658301283878487031725)
                    ·
                      refine ⟨1878621862981454432636897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5009658301283878487031725 1878621862981454432636897)
                      ·
                        rfl

theorem cell23_3658603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 4, 1, 3].length) (baseStart_3658603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658603 prefixEnd_3658603 := by exact prefixLift 3658603
  have htrace : WordTrace (prefixWord ++ tailWord_3658603) baseStart_3658603 baseEnd_3658603 := by
    simpa [prefixWord, tailWord_3658603, baseEnd_3658603] using wordTrace_append hprefix tailTrace_3658603
  have hstable : (prefixWord ++ tailWord_3658603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658603).length < 2 ^ (prefixWord ++ tailWord_3658603).sum := by decide
  have hdescent : baseEnd_3658603 < baseStart_3658603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658643 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 3, 4, 2]
def baseStart_3658643 : Nat := 118140960795 + 3658643 * 2 ^ 59
def prefixEnd_3658643 : Nat := 4983230072969 + 3 ^ 40 * 3658643 * 2
def baseEnd_3658643 : Nat := 1878642402207634276136713

theorem tailTrace_3658643 : CollatzResearch.WordTrace tailWord_3658643 prefixEnd_3658643 1878642402207634276136713 := by
  unfold tailWord_3658643
  simp only [CollatzResearch.WordTrace]
  refine ⟨133441672884368732322940583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88961115256245821548627055 133441672884368732322940583)
  ·
    refine ⟨200162509326553098484410875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133441672884368732322940583 200162509326553098484410875)
    ·
      refine ⟨300243763989829647726616313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200162509326553098484410875 300243763989829647726616313)
      ·
        refine ⟨225182822992372235794962235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300243763989829647726616313 225182822992372235794962235)
        ·
          refine ⟨337774234488558353692443353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225182822992372235794962235 337774234488558353692443353)
          ·
            refine ⟨253330675866418765269332515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337774234488558353692443353 253330675866418765269332515)
            ·
              refine ⟨379996013799628147903998773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253330675866418765269332515 379996013799628147903998773)
              ·
                refine ⟨35624626293715138865999885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 379996013799628147903998773 35624626293715138865999885)
                ·
                  refine ⟨13359234860143177074749957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35624626293715138865999885 13359234860143177074749957)
                  ·
                    refine ⟨2504856536276845701515617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13359234860143177074749957 2504856536276845701515617)
                    ·
                      refine ⟨1878642402207634276136713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504856536276845701515617 1878642402207634276136713)
                      ·
                        rfl

theorem cell23_3658643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 4, 2].length) (baseStart_3658643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658643 prefixEnd_3658643 := by exact prefixLift 3658643
  have htrace : WordTrace (prefixWord ++ tailWord_3658643) baseStart_3658643 baseEnd_3658643 := by
    simpa [prefixWord, tailWord_3658643, baseEnd_3658643] using wordTrace_append hprefix tailTrace_3658643
  have hstable : (prefixWord ++ tailWord_3658643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658643).length < 2 ^ (prefixWord ++ tailWord_3658643).sum := by decide
  have hdescent : baseEnd_3658643 < baseStart_3658643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658713 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 4, 5]
def baseStart_3658713 : Nat := 118140960795 + 3658713 * 2 ^ 59
def prefixEnd_3658713 : Nat := 4983230072969 + 3 ^ 40 * 3658713 * 2
def baseEnd_3658713 : Nat := 626226115284483000753797

theorem tailTrace_3658713 : CollatzResearch.WordTrace tailWord_3658713 prefixEnd_3658713 626226115284483000753797 := by
  unfold tailWord_3658713
  simp only [CollatzResearch.WordTrace]
  refine ⟨133444225994115134277988793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88962817329410089518659195 133444225994115134277988793)
  ·
    refine ⟨100083169495586350708491595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133444225994115134277988793 100083169495586350708491595)
    ·
      refine ⟨150124754243379526062737393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100083169495586350708491595 150124754243379526062737393)
      ·
        refine ⟨112593565682534644547053045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150124754243379526062737393 112593565682534644547053045)
        ·
          refine ⟨10555646782737622926286223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112593565682534644547053045 10555646782737622926286223)
          ·
            refine ⟨15833470174106434389429335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10555646782737622926286223 15833470174106434389429335)
            ·
              refine ⟨23750205261159651584144003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15833470174106434389429335 23750205261159651584144003)
              ·
                refine ⟨35625307891739477376216005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23750205261159651584144003 35625307891739477376216005)
                ·
                  refine ⟨6679745229701152008040501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35625307891739477376216005 6679745229701152008040501)
                  ·
                    refine ⟨626226115284483000753797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6679745229701152008040501 626226115284483000753797)
                    ·
                      rfl

theorem cell23_3658713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_3658713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658713 prefixEnd_3658713 := by exact prefixLift 3658713
  have htrace : WordTrace (prefixWord ++ tailWord_3658713) baseStart_3658713 baseEnd_3658713 := by
    simpa [prefixWord, tailWord_3658713, baseEnd_3658713] using wordTrace_append hprefix tailTrace_3658713
  have hstable : (prefixWord ++ tailWord_3658713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658713).length < 2 ^ (prefixWord ++ tailWord_3658713).sum := by decide
  have hdescent : baseEnd_3658713 < baseStart_3658713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658723 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3658723 : Nat := 118140960795 + 3658723 * 2 ^ 59
def prefixEnd_3658723 : Nat := 4983230072969 + 3 ^ 40 * 3658723 * 2
def baseEnd_3658723 : Nat := 1878683480659993963136345

theorem tailTrace_3658723 : CollatzResearch.WordTrace tailWord_3658723 prefixEnd_3658723 1878683480659993963136345 := by
  unfold tailWord_3658723
  simp only [CollatzResearch.WordTrace]
  refine ⟨133444590724078905985852823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88963060482719270657235215 133444590724078905985852823)
  ·
    refine ⟨200166886086118358978779235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133444590724078905985852823 200166886086118358978779235)
    ·
      refine ⟨300250329129177538468168853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200166886086118358978779235 300250329129177538468168853)
      ·
        refine ⟨14074234177930197115695415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 300250329129177538468168853 14074234177930197115695415)
        ·
          refine ⟨21111351266895295673543123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14074234177930197115695415 21111351266895295673543123)
          ·
            refine ⟨31667026900342943510314685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21111351266895295673543123 31667026900342943510314685)
            ·
              refine ⟨11875135087628603816368007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31667026900342943510314685 11875135087628603816368007)
              ·
                refine ⟨17812702631442905724552011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11875135087628603816368007 17812702631442905724552011)
                ·
                  refine ⟨26719053947164358586828017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17812702631442905724552011 26719053947164358586828017)
                  ·
                    refine ⟨20039290460373268940121013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26719053947164358586828017 20039290460373268940121013)
                    ·
                      refine ⟨1878683480659993963136345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20039290460373268940121013 1878683480659993963136345)
                      ·
                        rfl

theorem cell23_3658723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3658723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658723 prefixEnd_3658723 := by exact prefixLift 3658723
  have htrace : WordTrace (prefixWord ++ tailWord_3658723) baseStart_3658723 baseEnd_3658723 := by
    simpa [prefixWord, tailWord_3658723, baseEnd_3658723] using wordTrace_append hprefix tailTrace_3658723
  have hstable : (prefixWord ++ tailWord_3658723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658723).length < 2 ^ (prefixWord ++ tailWord_3658723).sum := by decide
  have hdescent : baseEnd_3658723 < baseStart_3658723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658784 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3658784 : Nat := 118140960795 + 3658784 * 2 ^ 59
def prefixEnd_3658784 : Nat := 4983230072969 + 3 ^ 40 * 3658784 * 2
def baseEnd_3658784 : Nat := 1878714802979918224473565

theorem tailTrace_3658784 : CollatzResearch.WordTrace tailWord_3658784 prefixEnd_3658784 1878714802979918224473565 := by
  unfold tailWord_3658784
  simp only [CollatzResearch.WordTrace]
  refine ⟨66723407788428956701911703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88964543717905275602548937 66723407788428956701911703)
  ·
    refine ⟨100085111682643435052867555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66723407788428956701911703 100085111682643435052867555)
    ·
      refine ⟨150127667523965152579301333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100085111682643435052867555 150127667523965152579301333)
      ·
        refine ⟨3518617207592933263577375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 150127667523965152579301333 3518617207592933263577375)
        ·
          refine ⟨5277925811389399895366063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518617207592933263577375 5277925811389399895366063)
          ·
            refine ⟨7916888717084099843049095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277925811389399895366063 7916888717084099843049095)
            ·
              refine ⟨11875333075626149764573643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7916888717084099843049095 11875333075626149764573643)
              ·
                refine ⟨17812999613439224646860465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11875333075626149764573643 17812999613439224646860465)
                ·
                  refine ⟨13359749710079418485145349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17812999613439224646860465 13359749710079418485145349)
                  ·
                    refine ⟨2504953070639890965964753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13359749710079418485145349 2504953070639890965964753)
                    ·
                      refine ⟨1878714802979918224473565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2504953070639890965964753 1878714802979918224473565)
                      ·
                        rfl

theorem cell23_3658784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3658784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658784 prefixEnd_3658784 := by exact prefixLift 3658784
  have htrace : WordTrace (prefixWord ++ tailWord_3658784) baseStart_3658784 baseEnd_3658784 := by
    simpa [prefixWord, tailWord_3658784, baseEnd_3658784] using wordTrace_append hprefix tailTrace_3658784
  have hstable : (prefixWord ++ tailWord_3658784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658784).length < 2 ^ (prefixWord ++ tailWord_3658784).sum := by decide
  have hdescent : baseEnd_3658784 < baseStart_3658784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658804 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3658804 : Nat := 118140960795 + 3658804 * 2 ^ 59
def prefixEnd_3658804 : Nat := 4983230072969 + 3 ^ 40 * 3658804 * 2
def baseEnd_3658804 : Nat := 1878725072593008146223473

theorem tailTrace_3658804 : CollatzResearch.WordTrace tailWord_3658804 prefixEnd_3658804 1878725072593008146223473 := by
  unfold tailWord_3658804
  simp only [CollatzResearch.WordTrace]
  refine ⟨66723772518392728409775733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88965030024523637879700977 66723772518392728409775733)
  ·
    refine ⟨6255353673599318288416475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66723772518392728409775733 6255353673599318288416475)
    ·
      refine ⟨9383030510398977432624713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6255353673599318288416475 9383030510398977432624713)
      ·
        refine ⟨7037272882799233074468535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9383030510398977432624713 7037272882799233074468535)
        ·
          refine ⟨10555909324198849611702803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7037272882799233074468535 10555909324198849611702803)
          ·
            refine ⟨15833863986298274417554205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10555909324198849611702803 15833863986298274417554205)
            ·
              refine ⟨5937698994861852906582827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15833863986298274417554205 5937698994861852906582827)
              ·
                refine ⟨8906548492292779359874241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5937698994861852906582827 8906548492292779359874241)
                ·
                  refine ⟨6679911369219584519905681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8906548492292779359874241 6679911369219584519905681)
                  ·
                    refine ⟨5009933526914688389929261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6679911369219584519905681 5009933526914688389929261)
                    ·
                      refine ⟨1878725072593008146223473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5009933526914688389929261 1878725072593008146223473)
                      ·
                        rfl

theorem cell23_3658804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3658804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658804 prefixEnd_3658804 := by exact prefixLift 3658804
  have htrace : WordTrace (prefixWord ++ tailWord_3658804) baseStart_3658804 baseEnd_3658804 := by
    simpa [prefixWord, tailWord_3658804, baseEnd_3658804] using wordTrace_append hprefix tailTrace_3658804
  have hstable : (prefixWord ++ tailWord_3658804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658804).length < 2 ^ (prefixWord ++ tailWord_3658804).sum := by decide
  have hdescent : baseEnd_3658804 < baseStart_3658804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658833 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 3, 6]
def baseStart_3658833 : Nat := 118140960795 + 3658833 * 2 ^ 59
def prefixEnd_3658833 : Nat := 4983230072969 + 3 ^ 40 * 3658833 * 2
def baseEnd_3658833 : Nat := 626246654510662844253613

theorem tailTrace_3658833 : CollatzResearch.WordTrace tailWord_3658833 prefixEnd_3658833 626246654510662844253613 := by
  unfold tailWord_3658833
  simp only [CollatzResearch.WordTrace]
  refine ⟨133448602753680394772357153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88965735169120263181571435 133448602753680394772357153)
  ·
    refine ⟨100086452065260296079267865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133448602753680394772357153 100086452065260296079267865)
    ·
      refine ⟨75064839048945222059450899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100086452065260296079267865 75064839048945222059450899)
      ·
        refine ⟨112597258573417833089176349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75064839048945222059450899 112597258573417833089176349)
        ·
          refine ⟨42223971965031687408441131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112597258573417833089176349 42223971965031687408441131)
          ·
            refine ⟨63335957947547531112661697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42223971965031687408441131 63335957947547531112661697)
            ·
              refine ⟨47501968460660648334496273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63335957947547531112661697 47501968460660648334496273)
              ·
                refine ⟨35626476345495486250872205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47501968460660648334496273 35626476345495486250872205)
                ·
                  refine ⟨13359928629560807344077077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35626476345495486250872205 13359928629560807344077077)
                  ·
                    refine ⟨626246654510662844253613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13359928629560807344077077 626246654510662844253613)
                    ·
                      rfl

theorem cell23_3658833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_3658833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658833 prefixEnd_3658833 := by exact prefixLift 3658833
  have htrace : WordTrace (prefixWord ++ tailWord_3658833) baseStart_3658833 baseEnd_3658833 := by
    simpa [prefixWord, tailWord_3658833, baseEnd_3658833] using wordTrace_append hprefix tailTrace_3658833
  have hstable : (prefixWord ++ tailWord_3658833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658833).length < 2 ^ (prefixWord ++ tailWord_3658833).sum := by decide
  have hdescent : baseEnd_3658833 < baseStart_3658833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658834 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 3, 1, 3]
def baseStart_3658834 : Nat := 118140960795 + 3658834 * 2 ^ 59
def prefixEnd_3658834 : Nat := 4983230072969 + 3 ^ 40 * 3658834 * 2
def baseEnd_3658834 : Nat := 1878740477012643028848335

theorem tailTrace_3658834 : CollatzResearch.WordTrace tailWord_3658834 prefixEnd_3658834 1878740477012643028848335 := by
  unfold tailWord_3658834
  simp only [CollatzResearch.WordTrace]
  refine ⟨33362159806669192985785889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88965759484451181295429037 33362159806669192985785889)
  ·
    refine ⟨25021619855001894739339417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33362159806669192985785889 25021619855001894739339417)
    ·
      refine ⟨18766214891251421054504563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25021619855001894739339417 18766214891251421054504563)
      ·
        refine ⟨28149322336877131581756845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18766214891251421054504563 28149322336877131581756845)
        ·
          refine ⟨10555995876328924343158817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28149322336877131581756845 10555995876328924343158817)
          ·
            refine ⟨7916996907246693257369113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10555995876328924343158817 7916996907246693257369113)
            ·
              refine ⟨5937747680435019943026835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7916996907246693257369113 5937747680435019943026835)
              ·
                refine ⟨8906621520652529914540253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5937747680435019943026835 8906621520652529914540253)
                ·
                  refine ⟨3339983070244698717952595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8906621520652529914540253 3339983070244698717952595)
                  ·
                    refine ⟨5009974605367048076928893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3339983070244698717952595 5009974605367048076928893)
                    ·
                      refine ⟨1878740477012643028848335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5009974605367048076928893 1878740477012643028848335)
                      ·
                        rfl

theorem cell23_3658834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_3658834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658834 prefixEnd_3658834 := by exact prefixLift 3658834
  have htrace : WordTrace (prefixWord ++ tailWord_3658834) baseStart_3658834 baseEnd_3658834 := by
    simpa [prefixWord, tailWord_3658834, baseEnd_3658834] using wordTrace_append hprefix tailTrace_3658834
  have hstable : (prefixWord ++ tailWord_3658834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658834).length < 2 ^ (prefixWord ++ tailWord_3658834).sum := by decide
  have hdescent : baseEnd_3658834 < baseStart_3658834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658857 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 4]
def baseStart_3658857 : Nat := 118140960795 + 3658857 * 2 ^ 59
def prefixEnd_3658857 : Nat := 4983230072969 + 3 ^ 40 * 3658857 * 2
def baseEnd_3658857 : Nat := 1878752287067696438860729

theorem tailTrace_3658857 : CollatzResearch.WordTrace tailWord_3658857 prefixEnd_3658857 1878752287067696438860729 := by
  unfold tailWord_3658857
  simp only [CollatzResearch.WordTrace]
  refine ⟨133449478105593446871230825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88966318737062297914153883 133449478105593446871230825)
  ·
    refine ⟨100087108579195085153423119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133449478105593446871230825 100087108579195085153423119)
    ·
      refine ⟨150130662868792627730134679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100087108579195085153423119 150130662868792627730134679)
      ·
        refine ⟨225195994303188941595202019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150130662868792627730134679 225195994303188941595202019)
        ·
          refine ⟨337793991454783412392803029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225195994303188941595202019 337793991454783412392803029)
          ·
            refine ⟨7917046674721486227956321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 337793991454783412392803029 7917046674721486227956321)
            ·
              refine ⟨5937785006041114670967241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7917046674721486227956321 5937785006041114670967241)
              ·
                refine ⟨4453338754530836003225431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5937785006041114670967241 4453338754530836003225431)
                ·
                  refine ⟨6680008131796254004838147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4453338754530836003225431 6680008131796254004838147)
                  ·
                    refine ⟨10020012197694381007257221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6680008131796254004838147 10020012197694381007257221)
                    ·
                      refine ⟨1878752287067696438860729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10020012197694381007257221 1878752287067696438860729)
                      ·
                        rfl

theorem cell23_3658857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 1, 4].length) (baseStart_3658857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658857 prefixEnd_3658857 := by exact prefixLift 3658857
  have htrace : WordTrace (prefixWord ++ tailWord_3658857) baseStart_3658857 baseEnd_3658857 := by
    simpa [prefixWord, tailWord_3658857, baseEnd_3658857] using wordTrace_append hprefix tailTrace_3658857
  have hstable : (prefixWord ++ tailWord_3658857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658857).length < 2 ^ (prefixWord ++ tailWord_3658857).sum := by decide
  have hdescent : baseEnd_3658857 < baseStart_3658857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658863 : List Nat := [1, 1, 2, 1, 3, 3, 3, 9]
def baseStart_3658863 : Nat := 118140960795 + 3658863 * 2 ^ 59
def prefixEnd_3658863 : Nat := 4983230072969 + 3 ^ 40 * 3658863 * 2
def baseEnd_3658863 : Nat := 69583532146356422792063

theorem tailTrace_3658863 : CollatzResearch.WordTrace tailWord_3658863 prefixEnd_3658863 69583532146356422792063 := by
  unfold tailWord_3658863
  simp only [CollatzResearch.WordTrace]
  refine ⟨133449696943571709895949243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88966464629047806597299495 133449696943571709895949243)
  ·
    refine ⟨200174545415357564843923865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133449696943571709895949243 200174545415357564843923865)
    ·
      refine ⟨150130909061518173632942899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200174545415357564843923865 150130909061518173632942899)
      ·
        refine ⟨225196363592277260449414349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150130909061518173632942899 225196363592277260449414349)
        ·
          refine ⟨84448636347103972668530381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225196363592277260449414349 84448636347103972668530381)
          ·
            refine ⟨31668238630163989750698893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84448636347103972668530381 31668238630163989750698893)
            ·
              refine ⟨11875589486311496156512085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31668238630163989750698893 11875589486311496156512085)
              ·
                refine ⟨69583532146356422792063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11875589486311496156512085 69583532146356422792063)
                ·
                  rfl

theorem cell23_3658863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 9].length) (baseStart_3658863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658863 prefixEnd_3658863 := by exact prefixLift 3658863
  have htrace : WordTrace (prefixWord ++ tailWord_3658863) baseStart_3658863 baseEnd_3658863 := by
    simpa [prefixWord, tailWord_3658863, baseEnd_3658863] using wordTrace_append hprefix tailTrace_3658863
  have hstable : (prefixWord ++ tailWord_3658863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658863).length < 2 ^ (prefixWord ++ tailWord_3658863).sum := by decide
  have hdescent : baseEnd_3658863 < baseStart_3658863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658877 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 1, 2, 3]
def baseStart_3658877 : Nat := 118140960795 + 3658877 * 2 ^ 59
def prefixEnd_3658877 : Nat := 4983230072969 + 3 ^ 40 * 3658877 * 2
def baseEnd_3658877 : Nat := 1878762556680786360610637

theorem tailTrace_3658877 : CollatzResearch.WordTrace tailWord_3658877 prefixEnd_3658877 1878762556680786360610637 := by
  unfold tailWord_3658877
  simp only [CollatzResearch.WordTrace]
  refine ⟨133450207565520990286958885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88966805043680660191305923 133450207565520990286958885)
  ·
    refine ⟨25021913918535185678804791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133450207565520990286958885 25021913918535185678804791)
    ·
      refine ⟨37532870877802778518207187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25021913918535185678804791 37532870877802778518207187)
      ·
        refine ⟨56299306316704167777310781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37532870877802778518207187 56299306316704167777310781)
        ·
          refine ⟨21112239868764062916491543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56299306316704167777310781 21112239868764062916491543)
          ·
            refine ⟨31668359803146094374737315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21112239868764062916491543 31668359803146094374737315)
            ·
              refine ⟨47502539704719141562105973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31668359803146094374737315 47502539704719141562105973)
              ·
                refine ⟨4453363097317419521447435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47502539704719141562105973 4453363097317419521447435)
                ·
                  refine ⟨6680044645976129282171153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4453363097317419521447435 6680044645976129282171153)
                  ·
                    refine ⟨5010033484482096961628365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6680044645976129282171153 5010033484482096961628365)
                    ·
                      refine ⟨1878762556680786360610637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5010033484482096961628365 1878762556680786360610637)
                      ·
                        rfl

theorem cell23_3658877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_3658877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658877 prefixEnd_3658877 := by exact prefixLift 3658877
  have htrace : WordTrace (prefixWord ++ tailWord_3658877) baseStart_3658877 baseEnd_3658877 := by
    simpa [prefixWord, tailWord_3658877, baseEnd_3658877] using wordTrace_append hprefix tailTrace_3658877
  have hstable : (prefixWord ++ tailWord_3658877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658877).length < 2 ^ (prefixWord ++ tailWord_3658877).sum := by decide
  have hdescent : baseEnd_3658877 < baseStart_3658877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658911 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3658911 : Nat := 118140960795 + 3658911 * 2 ^ 59
def prefixEnd_3658911 : Nat := 4983230072969 + 3 ^ 40 * 3658911 * 2
def baseEnd_3658911 : Nat := 1878780015023039227585481

theorem tailTrace_3658911 : CollatzResearch.WordTrace tailWord_3658911 prefixEnd_3658911 1878780015023039227585481 := by
  unfold tailWord_3658911
  simp only [CollatzResearch.WordTrace]
  refine ⟨133451447647397814093696587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88967631764931876062464391 133451447647397814093696587)
  ·
    refine ⟨200177171471096721140544881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133451447647397814093696587 200177171471096721140544881)
    ·
      refine ⟨150132878603322540855408661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200177171471096721140544881 150132878603322540855408661)
      ·
        refine ⟨7037478684530744102597281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150132878603322540855408661 7037478684530744102597281)
        ·
          refine ⟨5278109013398058076947961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7037478684530744102597281 5278109013398058076947961)
          ·
            refine ⟨3958581760048543557710971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278109013398058076947961 3958581760048543557710971)
            ·
              refine ⟨5937872640072815336566457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958581760048543557710971 5937872640072815336566457)
              ·
                refine ⟨4453404480054611502424843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5937872640072815336566457 4453404480054611502424843)
                ·
                  refine ⟨6680106720081917253637265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4453404480054611502424843 6680106720081917253637265)
                  ·
                    refine ⟨5010080040061437940227949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6680106720081917253637265 5010080040061437940227949)
                    ·
                      refine ⟨1878780015023039227585481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5010080040061437940227949 1878780015023039227585481)
                      ·
                        rfl

theorem cell23_3658911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3658911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658911 prefixEnd_3658911 := by exact prefixLift 3658911
  have htrace : WordTrace (prefixWord ++ tailWord_3658911) baseStart_3658911 baseEnd_3658911 := by
    simpa [prefixWord, tailWord_3658911, baseEnd_3658911] using wordTrace_append hprefix tailTrace_3658911
  have hstable : (prefixWord ++ tailWord_3658911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658911).length < 2 ^ (prefixWord ++ tailWord_3658911).sum := by decide
  have hdescent : baseEnd_3658911 < baseStart_3658911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658987 : List Nat := [1, 1, 1, 1, 2, 6, 1, 5, 5]
def baseStart_3658987 : Nat := 118140960795 + 3658987 * 2 ^ 59
def prefixEnd_3658987 : Nat := 4983230072969 + 3 ^ 40 * 3658987 * 2
def baseEnd_3658987 : Nat := 208757671061420103359459

theorem tailTrace_3658987 : CollatzResearch.WordTrace tailWord_3658987 prefixEnd_3658987 208757671061420103359459 := by
  unfold tailWord_3658987
  simp only [CollatzResearch.WordTrace]
  refine ⟨133454219595122479073463215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88969479730081652715642143 133454219595122479073463215)
  ·
    refine ⟨200181329392683718610194823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133454219595122479073463215 200181329392683718610194823)
    ·
      refine ⟨300271994089025577915292235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200181329392683718610194823 300271994089025577915292235)
      ·
        refine ⟨450407991133538366872938353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300271994089025577915292235 450407991133538366872938353)
        ·
          refine ⟨337805993350153775154703765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450407991133538366872938353 337805993350153775154703765)
          ·
            refine ⟨15834655938288458210376739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 337805993350153775154703765 15834655938288458210376739)
            ·
              refine ⟨23751983907432687315565109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15834655938288458210376739 23751983907432687315565109)
              ·
                refine ⟨2226748491321814435834229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23751983907432687315565109 2226748491321814435834229)
                ·
                  refine ⟨208757671061420103359459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2226748491321814435834229 208757671061420103359459)
                  ·
                    rfl

theorem cell23_3658987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 5, 5].length) (baseStart_3658987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3658987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3658987 prefixEnd_3658987 := by exact prefixLift 3658987
  have htrace : WordTrace (prefixWord ++ tailWord_3658987) baseStart_3658987 baseEnd_3658987 := by
    simpa [prefixWord, tailWord_3658987, baseEnd_3658987] using wordTrace_append hprefix tailTrace_3658987
  have hstable : (prefixWord ++ tailWord_3658987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658987).length < 2 ^ (prefixWord ++ tailWord_3658987).sum := by decide
  have hdescent : baseEnd_3658987 < baseStart_3658987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659127 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_3659127 : Nat := 118140960795 + 3659127 * 2 ^ 59
def prefixEnd_3659127 : Nat := 4983230072969 + 3 ^ 40 * 3659127 * 2
def baseEnd_3659127 : Nat := 1878890926844410382484487

theorem tailTrace_3659127 : CollatzResearch.WordTrace tailWord_3659127 prefixEnd_3659127 1878890926844410382484487 := by
  unfold tailWord_3659127
  simp only [CollatzResearch.WordTrace]
  refine ⟨133459325814615282983559635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88972883876410188655706423 133459325814615282983559635)
  ·
    refine ⟨200188988721922924475339453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133459325814615282983559635 200188988721922924475339453)
    ·
      refine ⟨75070870770721096678252295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200188988721922924475339453 75070870770721096678252295)
      ·
        refine ⟨112606306156081645017378443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75070870770721096678252295 112606306156081645017378443)
        ·
          refine ⟨168909459234122467526067665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112606306156081645017378443 168909459234122467526067665)
          ·
            refine ⟨126682094425591850644550749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168909459234122467526067665 126682094425591850644550749)
            ·
              refine ⟨47505785409596943991706531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126682094425591850644550749 47505785409596943991706531)
              ·
                refine ⟨71258678114395415987559797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47505785409596943991706531 71258678114395415987559797)
                ·
                  refine ⟨6680501073224570248833731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71258678114395415987559797 6680501073224570248833731)
                  ·
                    refine ⟨10020751609836855373250597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6680501073224570248833731 10020751609836855373250597)
                    ·
                      refine ⟨1878890926844410382484487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10020751609836855373250597 1878890926844410382484487)
                      ·
                        rfl

theorem cell23_3659127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_3659127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659127 prefixEnd_3659127 := by exact prefixLift 3659127
  have htrace : WordTrace (prefixWord ++ tailWord_3659127) baseStart_3659127 baseEnd_3659127 := by
    simpa [prefixWord, tailWord_3659127, baseEnd_3659127] using wordTrace_append hprefix tailTrace_3659127
  have hstable : (prefixWord ++ tailWord_3659127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659127).length < 2 ^ (prefixWord ++ tailWord_3659127).sum := by decide
  have hdescent : baseEnd_3659127 < baseStart_3659127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659138 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3659138 : Nat := 118140960795 + 3659138 * 2 ^ 59
def prefixEnd_3659138 : Nat := 4983230072969 + 3 ^ 40 * 3659138 * 2
def baseEnd_3659138 : Nat := 1878896575131609839446937

theorem tailTrace_3659138 : CollatzResearch.WordTrace tailWord_3659138 prefixEnd_3659138 1878896575131609839446937 := by
  unfold tailWord_3659138
  simp only [CollatzResearch.WordTrace]
  refine ⟨33364931754393857965552517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88973151345050287908140045 33364931754393857965552517)
  ·
    refine ⟨6255924703948848368541097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33364931754393857965552517 6255924703948848368541097)
    ·
      refine ⟨4691943527961636276405823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6255924703948848368541097 4691943527961636276405823)
      ·
        refine ⟨7037915291942454414608735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4691943527961636276405823 7037915291942454414608735)
        ·
          refine ⟨10556872937913681621913103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7037915291942454414608735 10556872937913681621913103)
          ·
            refine ⟨15835309406870522432869655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10556872937913681621913103 15835309406870522432869655)
            ·
              refine ⟨23752964110305783649304483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15835309406870522432869655 23752964110305783649304483)
              ·
                refine ⟨35629446165458675473956725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23752964110305783649304483 35629446165458675473956725)
                ·
                  refine ⟨3340260578011750825683443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35629446165458675473956725 3340260578011750825683443)
                  ·
                    refine ⟨5010390867017626238525165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3340260578011750825683443 5010390867017626238525165)
                    ·
                      refine ⟨1878896575131609839446937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5010390867017626238525165 1878896575131609839446937)
                      ·
                        rfl

theorem cell23_3659138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3659138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659138 prefixEnd_3659138 := by exact prefixLift 3659138
  have htrace : WordTrace (prefixWord ++ tailWord_3659138) baseStart_3659138 baseEnd_3659138 := by
    simpa [prefixWord, tailWord_3659138, baseEnd_3659138] using wordTrace_append hprefix tailTrace_3659138
  have hstable : (prefixWord ++ tailWord_3659138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659138).length < 2 ^ (prefixWord ++ tailWord_3659138).sum := by decide
  have hdescent : baseEnd_3659138 < baseStart_3659138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659144 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3659144 : Nat := 118140960795 + 3659144 * 2 ^ 59
def prefixEnd_3659144 : Nat := 4983230072969 + 3 ^ 40 * 3659144 * 2
def baseEnd_3659144 : Nat := 1878899656015536815971909

theorem tailTrace_3659144 : CollatzResearch.WordTrace tailWord_3659144 prefixEnd_3659144 1878899656015536815971909 := by
  unfold tailWord_3659144
  simp only [CollatzResearch.WordTrace]
  refine ⟨66729972927776847443464243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88973297237035796591285657 66729972927776847443464243)
  ·
    refine ⟨100094959391665271165196365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66729972927776847443464243 100094959391665271165196365)
    ·
      refine ⟨37535609771874476686948637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100094959391665271165196365 37535609771874476686948637)
      ·
        refine ⟨14075853664452928757605739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37535609771874476686948637 14075853664452928757605739)
        ·
          refine ⟨21113780496679393136408609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14075853664452928757605739 21113780496679393136408609)
          ·
            refine ⟨15835335372509544852306457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21113780496679393136408609 15835335372509544852306457)
            ·
              refine ⟨11876501529382158639229843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15835335372509544852306457 11876501529382158639229843)
              ·
                refine ⟨17814752294073237958844765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11876501529382158639229843 17814752294073237958844765)
                ·
                  refine ⟨6680532110277464234566787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17814752294073237958844765 6680532110277464234566787)
                  ·
                    refine ⟨10020798165416196351850181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6680532110277464234566787 10020798165416196351850181)
                    ·
                      refine ⟨1878899656015536815971909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10020798165416196351850181 1878899656015536815971909)
                      ·
                        rfl

theorem cell23_3659144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3659144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659144 prefixEnd_3659144 := by exact prefixLift 3659144
  have htrace : WordTrace (prefixWord ++ tailWord_3659144) baseStart_3659144 baseEnd_3659144 := by
    simpa [prefixWord, tailWord_3659144, baseEnd_3659144] using wordTrace_append hprefix tailTrace_3659144
  have hstable : (prefixWord ++ tailWord_3659144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659144).length < 2 ^ (prefixWord ++ tailWord_3659144).sum := by decide
  have hdescent : baseEnd_3659144 < baseStart_3659144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659161 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 1, 1, 4]
def baseStart_3659161 : Nat := 118140960795 + 3659161 * 2 ^ 59
def prefixEnd_3659161 : Nat := 4983230072969 + 3 ^ 40 * 3659161 * 2
def baseEnd_3659161 : Nat := 1878908385186663249459331

theorem tailTrace_3659161 : CollatzResearch.WordTrace tailWord_3659161 prefixEnd_3659161 1878908385186663249459331 := by
  unfold tailWord_3659161
  simp only [CollatzResearch.WordTrace]
  refine ⟨133460565896492106790297337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88973710597661404526864891 133460565896492106790297337)
  ·
    refine ⟨100095424422369080092723003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133460565896492106790297337 100095424422369080092723003)
    ·
      refine ⟨150143136633553620139084505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100095424422369080092723003 150143136633553620139084505)
      ·
        refine ⟨112607352475165215104313379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150143136633553620139084505 112607352475165215104313379)
        ·
          refine ⟨168911028712747822656470069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112607352475165215104313379 168911028712747822656470069)
          ·
            refine ⟨15835408941820108374044069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168911028712747822656470069 15835408941820108374044069)
            ·
              refine ⟨2969139176591270320133263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15835408941820108374044069 2969139176591270320133263)
              ·
                refine ⟨4453708764886905480199895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969139176591270320133263 4453708764886905480199895)
                ·
                  refine ⟨6680563147330358220299843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4453708764886905480199895 6680563147330358220299843)
                  ·
                    refine ⟨10020844720995537330449765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6680563147330358220299843 10020844720995537330449765)
                    ·
                      refine ⟨1878908385186663249459331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10020844720995537330449765 1878908385186663249459331)
                      ·
                        rfl

theorem cell23_3659161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 1, 1, 4].length) (baseStart_3659161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659161 prefixEnd_3659161 := by exact prefixLift 3659161
  have htrace : WordTrace (prefixWord ++ tailWord_3659161) baseStart_3659161 baseEnd_3659161 := by
    simpa [prefixWord, tailWord_3659161, baseEnd_3659161] using wordTrace_append hprefix tailTrace_3659161
  have hstable : (prefixWord ++ tailWord_3659161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659161).length < 2 ^ (prefixWord ++ tailWord_3659161).sum := by decide
  have hdescent : baseEnd_3659161 < baseStart_3659161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659167 : List Nat := [1, 1, 2, 5, 1, 3, 10]
def baseStart_3659167 : Nat := 118140960795 + 3659167 * 2 ^ 59
def prefixEnd_3659167 : Nat := 4983230072969 + 3 ^ 40 * 3659167 * 2
def baseEnd_3659167 : Nat := 23196437852723336123263

theorem tailTrace_3659167 : CollatzResearch.WordTrace tailWord_3659167 prefixEnd_3659167 23196437852723336123263 := by
  unfold tailWord_3659167
  simp only [CollatzResearch.WordTrace]
  refine ⟨133460784734470369815015755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88973856489646913210010503 133460784734470369815015755)
  ·
    refine ⟨200191177101705554722523633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133460784734470369815015755 200191177101705554722523633)
    ·
      refine ⟨150143382826279166041892725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200191177101705554722523633 150143382826279166041892725)
      ·
        refine ⟨14075942139963671816427443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150143382826279166041892725 14075942139963671816427443)
        ·
          refine ⟨21113913209945507724641165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14075942139963671816427443 21113913209945507724641165)
          ·
            refine ⟨7917717453729565396740437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21113913209945507724641165 7917717453729565396740437)
            ·
              refine ⟨23196437852723336123263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7917717453729565396740437 23196437852723336123263)
              ·
                rfl

theorem cell23_3659167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 10].length) (baseStart_3659167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659167 prefixEnd_3659167 := by exact prefixLift 3659167
  have htrace : WordTrace (prefixWord ++ tailWord_3659167) baseStart_3659167 baseEnd_3659167 := by
    simpa [prefixWord, tailWord_3659167, baseEnd_3659167] using wordTrace_append hprefix tailTrace_3659167
  have hstable : (prefixWord ++ tailWord_3659167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659167).length < 2 ^ (prefixWord ++ tailWord_3659167).sum := by decide
  have hdescent : baseEnd_3659167 < baseStart_3659167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659177 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 2, 7, 3]
def baseStart_3659177 : Nat := 118140960795 + 3659177 * 2 ^ 59
def prefixEnd_3659177 : Nat := 4983230072969 + 3 ^ 40 * 3659177 * 2
def baseEnd_3659177 : Nat := 1878916600877135186859257

theorem tailTrace_3659177 : CollatzResearch.WordTrace tailWord_3659177 prefixEnd_3659177 1878916600877135186859257 := by
  unfold tailWord_3659177
  simp only [CollatzResearch.WordTrace]
  refine ⟨133461149464434141522879785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88974099642956094348586523 133461149464434141522879785)
  ·
    refine ⟨100095862098325606142159839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133461149464434141522879785 100095862098325606142159839)
    ·
      refine ⟨150143793147488409213239759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100095862098325606142159839 150143793147488409213239759)
      ·
        refine ⟨225215689721232613819859639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150143793147488409213239759 225215689721232613819859639)
        ·
          refine ⟨337823534581848920729789459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225215689721232613819859639 337823534581848920729789459)
          ·
            refine ⟨506735301872773381094684189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337823534581848920729789459 506735301872773381094684189)
            ·
              refine ⟨190025738202290017910506571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506735301872773381094684189 190025738202290017910506571)
              ·
                refine ⟨285038607303435026865759857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190025738202290017910506571 285038607303435026865759857)
                ·
                  refine ⟨213778955477576270149319893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285038607303435026865759857 213778955477576270149319893)
                  ·
                    refine ⟨5010444269005693831624685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 213778955477576270149319893 5010444269005693831624685)
                    ·
                      refine ⟨1878916600877135186859257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5010444269005693831624685 1878916600877135186859257)
                      ·
                        rfl

theorem cell23_3659177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 7, 3].length) (baseStart_3659177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659177 prefixEnd_3659177 := by exact prefixLift 3659177
  have htrace : WordTrace (prefixWord ++ tailWord_3659177) baseStart_3659177 baseEnd_3659177 := by
    simpa [prefixWord, tailWord_3659177, baseEnd_3659177] using wordTrace_append hprefix tailTrace_3659177
  have hstable : (prefixWord ++ tailWord_3659177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659177).length < 2 ^ (prefixWord ++ tailWord_3659177).sum := by decide
  have hdescent : baseEnd_3659177 < baseStart_3659177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659181 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3659181 : Nat := 118140960795 + 3659181 * 2 ^ 59
def prefixEnd_3659181 : Nat := 4983230072969 + 3 ^ 40 * 3659181 * 2
def baseEnd_3659181 : Nat := 1878918654799753171209239

theorem tailTrace_3659181 : CollatzResearch.WordTrace tailWord_3659181 prefixEnd_3659181 1878918654799753171209239 := by
  unfold tailWord_3659181
  simp only [CollatzResearch.WordTrace]
  refine ⟨133461295356419650206025397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88974196904279766804016931 133461295356419650206025397)
  ·
    refine ⟨12511996439664342206814881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133461295356419650206025397 12511996439664342206814881)
    ·
      refine ⟨9383997329748256655111161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12511996439664342206814881 9383997329748256655111161)
      ·
        refine ⟨7037997997311192491333371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9383997329748256655111161 7037997997311192491333371)
        ·
          refine ⟨10556996995966788737000057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7037997997311192491333371 10556996995966788737000057)
          ·
            refine ⟨7917747746975091552750043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10556996995966788737000057 7917747746975091552750043)
            ·
              refine ⟨11876621620462637329125065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7917747746975091552750043 11876621620462637329125065)
              ·
                refine ⟨8907466215346977996843799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11876621620462637329125065 8907466215346977996843799)
                ·
                  refine ⟨13361199323020466995265699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8907466215346977996843799 13361199323020466995265699)
                  ·
                    refine ⟨20041798984530700492898549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13361199323020466995265699 20041798984530700492898549)
                    ·
                      refine ⟨1878918654799753171209239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20041798984530700492898549 1878918654799753171209239)
                      ·
                        rfl

theorem cell23_3659181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3659181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659181 prefixEnd_3659181 := by exact prefixLift 3659181
  have htrace : WordTrace (prefixWord ++ tailWord_3659181) baseStart_3659181 baseEnd_3659181 := by
    simpa [prefixWord, tailWord_3659181, baseEnd_3659181] using wordTrace_append hprefix tailTrace_3659181
  have hstable : (prefixWord ++ tailWord_3659181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659181).length < 2 ^ (prefixWord ++ tailWord_3659181).sum := by decide
  have hdescent : baseEnd_3659181 < baseStart_3659181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659207 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_3659207 : Nat := 118140960795 + 3659207 * 2 ^ 59
def prefixEnd_3659207 : Nat := 4983230072969 + 3 ^ 40 * 3659207 * 2
def baseEnd_3659207 : Nat := 1878932005296770069484119

theorem tailTrace_3659207 : CollatzResearch.WordTrace tailWord_3659207 prefixEnd_3659207 1878932005296770069484119 := by
  unfold tailWord_3659207
  simp only [CollatzResearch.WordTrace]
  refine ⟨133462243654325456646471875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88974829102883637764314583 133462243654325456646471875)
  ·
    refine ⟨200193365481488184969707813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133462243654325456646471875 200193365481488184969707813)
    ·
      refine ⟨37536256027779034681820215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200193365481488184969707813 37536256027779034681820215)
      ·
        refine ⟨56304384041668552022730323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37536256027779034681820215 56304384041668552022730323)
        ·
          refine ⟨84456576062502828034095485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56304384041668552022730323 84456576062502828034095485)
          ·
            refine ⟨31671216023438560512785807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84456576062502828034095485 31671216023438560512785807)
            ·
              refine ⟨47506824035157840769178711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31671216023438560512785807 47506824035157840769178711)
              ·
                refine ⟨71260236052736761153768067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47506824035157840769178711 71260236052736761153768067)
                ·
                  refine ⟨106890354079105141730652101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71260236052736761153768067 106890354079105141730652101)
                  ·
                    refine ⟨20041941389832214074497269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106890354079105141730652101 20041941389832214074497269)
                    ·
                      refine ⟨1878932005296770069484119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20041941389832214074497269 1878932005296770069484119)
                      ·
                        rfl

theorem cell23_3659207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_3659207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659207 prefixEnd_3659207 := by exact prefixLift 3659207
  have htrace : WordTrace (prefixWord ++ tailWord_3659207) baseStart_3659207 baseEnd_3659207 := by
    simpa [prefixWord, tailWord_3659207, baseEnd_3659207] using wordTrace_append hprefix tailTrace_3659207
  have hstable : (prefixWord ++ tailWord_3659207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659207).length < 2 ^ (prefixWord ++ tailWord_3659207).sum := by decide
  have hdescent : baseEnd_3659207 < baseStart_3659207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659212 : List Nat := [2, 2, 1, 4, 2, 3, 1, 3, 1, 2, 2]
def baseStart_3659212 : Nat := 118140960795 + 3659212 * 2 ^ 59
def prefixEnd_3659212 : Nat := 4983230072969 + 3 ^ 40 * 3659212 * 2
def baseEnd_3659212 : Nat := 1878934572700042549921597

theorem tailTrace_3659212 : CollatzResearch.WordTrace tailWord_3659212 prefixEnd_3659212 1878934572700042549921597 := by
  unfold tailWord_3659212
  simp only [CollatzResearch.WordTrace]
  refine ⟨66731213009653671250201945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88974950679538228333602593 66731213009653671250201945)
  ·
    refine ⟨50048409757240253437651459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66731213009653671250201945 50048409757240253437651459)
    ·
      refine ⟨75072614635860380156477189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50048409757240253437651459 75072614635860380156477189)
      ·
        refine ⟨14076115244223821279339473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75072614635860380156477189 14076115244223821279339473)
        ·
          refine ⟨10557086433167865959504605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14076115244223821279339473 10557086433167865959504605)
          ·
            refine ⟨3958907412437949734814227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10557086433167865959504605 3958907412437949734814227)
            ·
              refine ⟨5938361118656924602221341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958907412437949734814227 5938361118656924602221341)
              ·
                refine ⟨2226885419496346725833003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5938361118656924602221341 2226885419496346725833003)
                ·
                  refine ⟨3340328129244520088749505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226885419496346725833003 3340328129244520088749505)
                  ·
                    refine ⟨2505246096933390066562129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3340328129244520088749505 2505246096933390066562129)
                    ·
                      refine ⟨1878934572700042549921597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2505246096933390066562129 1878934572700042549921597)
                      ·
                        rfl

theorem cell23_3659212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_3659212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659212 prefixEnd_3659212 := by exact prefixLift 3659212
  have htrace : WordTrace (prefixWord ++ tailWord_3659212) baseStart_3659212 baseEnd_3659212 := by
    simpa [prefixWord, tailWord_3659212, baseEnd_3659212] using wordTrace_append hprefix tailTrace_3659212
  have hstable : (prefixWord ++ tailWord_3659212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659212).length < 2 ^ (prefixWord ++ tailWord_3659212).sum := by decide
  have hdescent : baseEnd_3659212 < baseStart_3659212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659217 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_3659217 : Nat := 118140960795 + 3659217 * 2 ^ 59
def prefixEnd_3659217 : Nat := 4983230072969 + 3 ^ 40 * 3659217 * 2
def baseEnd_3659217 : Nat := 1878937140103315030359073

theorem tailTrace_3659217 : CollatzResearch.WordTrace tailWord_3659217 prefixEnd_3659217 1878937140103315030359073 := by
  unfold tailWord_3659217
  simp only [CollatzResearch.WordTrace]
  refine ⟨133462608384289228354335905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88975072256192818902890603 133462608384289228354335905)
  ·
    refine ⟨100096956288216921265751929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133462608384289228354335905 100096956288216921265751929)
    ·
      refine ⟨75072717216162690949313947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100096956288216921265751929 75072717216162690949313947)
      ·
        refine ⟨112609075824244036423970921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75072717216162690949313947 112609075824244036423970921)
        ·
          refine ⟨84456806868183027317978191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112609075824244036423970921 84456806868183027317978191)
          ·
            refine ⟨126685210302274540976967287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84456806868183027317978191 126685210302274540976967287)
            ·
              refine ⟨190027815453411811465450931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126685210302274540976967287 190027815453411811465450931)
              ·
                refine ⟨285041723180117717198176397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190027815453411811465450931 285041723180117717198176397)
                ·
                  refine ⟨106890646192544143949316149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285041723180117717198176397 106890646192544143949316149)
                  ·
                    refine ⟨10020998080551013495248389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106890646192544143949316149 10020998080551013495248389)
                    ·
                      refine ⟨1878937140103315030359073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10020998080551013495248389 1878937140103315030359073)
                      ·
                        rfl

theorem cell23_3659217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_3659217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659217 prefixEnd_3659217 := by exact prefixLift 3659217
  have htrace : WordTrace (prefixWord ++ tailWord_3659217) baseStart_3659217 baseEnd_3659217 := by
    simpa [prefixWord, tailWord_3659217, baseEnd_3659217] using wordTrace_append hprefix tailTrace_3659217
  have hstable : (prefixWord ++ tailWord_3659217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659217).length < 2 ^ (prefixWord ++ tailWord_3659217).sum := by decide
  have hdescent : baseEnd_3659217 < baseStart_3659217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659245 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3659245 : Nat := 118140960795 + 3659245 * 2 ^ 59
def prefixEnd_3659245 : Nat := 4983230072969 + 3 ^ 40 * 3659245 * 2
def baseEnd_3659245 : Nat := 1878951517561640920808945

theorem tailTrace_3659245 : CollatzResearch.WordTrace tailWord_3659245 prefixEnd_3659245 1878951517561640920808945 := by
  unfold tailWord_3659245
  simp only [CollatzResearch.WordTrace]
  refine ⟨133463629628187789136355189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88975753085458526090903459 133463629628187789136355189)
  ·
    refine ⟨12512215277642605231533299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133463629628187789136355189 12512215277642605231533299)
    ·
      refine ⟨18768322916463907847299949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12512215277642605231533299 18768322916463907847299949)
      ·
        refine ⟨7038121093673965442737481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18768322916463907847299949 7038121093673965442737481)
        ·
          refine ⟨5278590820255474082053111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7038121093673965442737481 5278590820255474082053111)
          ·
            refine ⟨7917886230383211123079667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278590820255474082053111 7917886230383211123079667)
            ·
              refine ⟨11876829345574816684619501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7917886230383211123079667 11876829345574816684619501)
              ·
                refine ⟨4453811004590556256732313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11876829345574816684619501 4453811004590556256732313)
                ·
                  refine ⟨3340358253442917192549235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4453811004590556256732313 3340358253442917192549235)
                  ·
                    refine ⟨5010537380164375788823853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3340358253442917192549235 5010537380164375788823853)
                    ·
                      refine ⟨1878951517561640920808945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5010537380164375788823853 1878951517561640920808945)
                      ·
                        rfl

theorem cell23_3659245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3659245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659245 prefixEnd_3659245 := by exact prefixLift 3659245
  have htrace : WordTrace (prefixWord ++ tailWord_3659245) baseStart_3659245 baseEnd_3659245 := by
    simpa [prefixWord, tailWord_3659245, baseEnd_3659245] using wordTrace_append hprefix tailTrace_3659245
  have hstable : (prefixWord ++ tailWord_3659245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659245).length < 2 ^ (prefixWord ++ tailWord_3659245).sum := by decide
  have hdescent : baseEnd_3659245 < baseStart_3659245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659251 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 6, 2, 2]
def baseStart_3659251 : Nat := 118140960795 + 3659251 * 2 ^ 59
def prefixEnd_3659251 : Nat := 4983230072969 + 3 ^ 40 * 3659251 * 2
def baseEnd_3659251 : Nat := 1878954598445567897333917

theorem tailTrace_3659251 : CollatzResearch.WordTrace tailWord_3659251 prefixEnd_3659251 1878954598445567897333917 := by
  unfold tailWord_3659251
  simp only [CollatzResearch.WordTrace]
  refine ⟨133463848466166052161073607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88975898977444034774049071 133463848466166052161073607)
  ·
    refine ⟨200195772699249078241610411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133463848466166052161073607 200195772699249078241610411)
    ·
      refine ⟨300293659048873617362415617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200195772699249078241610411 300293659048873617362415617)
      ·
        refine ⟨225220244286655213021811713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300293659048873617362415617 225220244286655213021811713)
        ·
          refine ⟨168915183214991409766358785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225220244286655213021811713 168915183214991409766358785)
          ·
            refine ⟨126686387411243557324769089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168915183214991409766358785 126686387411243557324769089)
            ·
              refine ⟨95014790558432667993576817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126686387411243557324769089 95014790558432667993576817)
              ·
                refine ⟨71261092918824500995182613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95014790558432667993576817 71261092918824500995182613)
                ·
                  refine ⟨3340363730569898484149185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71261092918824500995182613 3340363730569898484149185)
                  ·
                    refine ⟨2505272797927423863111889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3340363730569898484149185 2505272797927423863111889)
                    ·
                      refine ⟨1878954598445567897333917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2505272797927423863111889 1878954598445567897333917)
                      ·
                        rfl

theorem cell23_3659251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 6, 2, 2].length) (baseStart_3659251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659251 prefixEnd_3659251 := by exact prefixLift 3659251
  have htrace : WordTrace (prefixWord ++ tailWord_3659251) baseStart_3659251 baseEnd_3659251 := by
    simpa [prefixWord, tailWord_3659251, baseEnd_3659251] using wordTrace_append hprefix tailTrace_3659251
  have hstable : (prefixWord ++ tailWord_3659251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659251).length < 2 ^ (prefixWord ++ tailWord_3659251).sum := by decide
  have hdescent : baseEnd_3659251 < baseStart_3659251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659257 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 9]
def baseStart_3659257 : Nat := 118140960795 + 3659257 * 2 ^ 59
def prefixEnd_3659257 : Nat := 4983230072969 + 3 ^ 40 * 3659257 * 2
def baseEnd_3659257 : Nat := 208773075481054985984321

theorem tailTrace_3659257 : CollatzResearch.WordTrace tailWord_3659257 prefixEnd_3659257 208773075481054985984321 := by
  unfold tailWord_3659257
  simp only [CollatzResearch.WordTrace]
  refine ⟨133464067304144315185792025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88976044869429543457194683 133464067304144315185792025)
  ·
    refine ⟨100098050478108236389344019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133464067304144315185792025 100098050478108236389344019)
    ·
      refine ⟨150147075717162354584016029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100098050478108236389344019 150147075717162354584016029)
      ·
        refine ⟨56305153393935882969006011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150147075717162354584016029 56305153393935882969006011)
        ·
          refine ⟨84457730090903824453509017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56305153393935882969006011 84457730090903824453509017)
          ·
            refine ⟨63343297568177868340131763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84457730090903824453509017 63343297568177868340131763)
            ·
              refine ⟨95014946352266802510197645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63343297568177868340131763 95014946352266802510197645)
              ·
                refine ⟨35630604882100050941324117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95014946352266802510197645 35630604882100050941324117)
                ·
                  refine ⟨208773075481054985984321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35630604882100050941324117 208773075481054985984321)
                  ·
                    rfl

theorem cell23_3659257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 9].length) (baseStart_3659257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659257 prefixEnd_3659257 := by exact prefixLift 3659257
  have htrace : WordTrace (prefixWord ++ tailWord_3659257) baseStart_3659257 baseEnd_3659257 := by
    simpa [prefixWord, tailWord_3659257, baseEnd_3659257] using wordTrace_append hprefix tailTrace_3659257
  have hstable : (prefixWord ++ tailWord_3659257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659257).length < 2 ^ (prefixWord ++ tailWord_3659257).sum := by decide
  have hdescent : baseEnd_3659257 < baseStart_3659257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659267 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 7]
def baseStart_3659267 : Nat := 118140960795 + 3659267 * 2 ^ 59
def prefixEnd_3659267 : Nat := 4983230072969 + 3 ^ 40 * 3659267 * 2
def baseEnd_3659267 : Nat := 1878962814136039834733843

theorem tailTrace_3659267 : CollatzResearch.WordTrace tailWord_3659267 prefixEnd_3659267 1878962814136039834733843 := by
  unfold tailWord_3659267
  simp only [CollatzResearch.WordTrace]
  refine ⟨133464432034108086893656055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88976288022738724595770703 133464432034108086893656055)
  ·
    refine ⟨200196648051162130340484083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133464432034108086893656055 200196648051162130340484083)
    ·
      refine ⟨300294972076743195510726125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200196648051162130340484083 300294972076743195510726125)
      ·
        refine ⟨112610614528778698316522297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300294972076743195510726125 112610614528778698316522297)
        ·
          refine ⟨84457960896584023737391723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112610614528778698316522297 84457960896584023737391723)
          ·
            refine ⟨126686941344876035606087585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84457960896584023737391723 126686941344876035606087585)
            ·
              refine ⟨95015206008657026704565689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126686941344876035606087585 95015206008657026704565689)
              ·
                refine ⟨71261404506492770028424267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95015206008657026704565689 71261404506492770028424267)
                ·
                  refine ⟨106892106759739155042636401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71261404506492770028424267 106892106759739155042636401)
                  ·
                    refine ⟨80169080069804366281977301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106892106759739155042636401 80169080069804366281977301)
                    ·
                      refine ⟨1878962814136039834733843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80169080069804366281977301 1878962814136039834733843)
                      ·
                        rfl

theorem cell23_3659267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_3659267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659267 prefixEnd_3659267 := by exact prefixLift 3659267
  have htrace : WordTrace (prefixWord ++ tailWord_3659267) baseStart_3659267 baseEnd_3659267 := by
    simpa [prefixWord, tailWord_3659267, baseEnd_3659267] using wordTrace_append hprefix tailTrace_3659267
  have hstable : (prefixWord ++ tailWord_3659267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659267).length < 2 ^ (prefixWord ++ tailWord_3659267).sum := by decide
  have hdescent : baseEnd_3659267 < baseStart_3659267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659285 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 2, 2, 2]
def baseStart_3659285 : Nat := 118140960795 + 3659285 * 2 ^ 59
def prefixEnd_3659285 : Nat := 4983230072969 + 3 ^ 40 * 3659285 * 2
def baseEnd_3659285 : Nat := 1878972056787820764308761

theorem tailTrace_3659285 : CollatzResearch.WordTrace tailWord_3659285 prefixEnd_3659285 1878972056787820764308761 := by
  unfold tailWord_3659285
  simp only [CollatzResearch.WordTrace]
  refine ⟨133465088548042875967811309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88976725698695250645207539 133465088548042875967811309)
  ·
    refine ⟨50049408205516078487929241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133465088548042875967811309 50049408205516078487929241)
    ·
      refine ⟨37537056154137058865946931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50049408205516078487929241 37537056154137058865946931)
      ·
        refine ⟨56305584231205588298920397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37537056154137058865946931 56305584231205588298920397)
        ·
          refine ⟨21114594086702095612095149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56305584231205588298920397 21114594086702095612095149)
          ·
            refine ⟨7917972782513285854535681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21114594086702095612095149 7917972782513285854535681)
            ·
              refine ⟨5938479586884964390901761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7917972782513285854535681 5938479586884964390901761)
              ·
                refine ⟨4453859690163723293176321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5938479586884964390901761 4453859690163723293176321)
                ·
                  refine ⟨3340394767622792469882241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4453859690163723293176321 3340394767622792469882241)
                  ·
                    refine ⟨2505296075717094352411681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3340394767622792469882241 2505296075717094352411681)
                    ·
                      refine ⟨1878972056787820764308761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2505296075717094352411681 1878972056787820764308761)
                      ·
                        rfl

theorem cell23_3659285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_3659285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659285 prefixEnd_3659285 := by exact prefixLift 3659285
  have htrace : WordTrace (prefixWord ++ tailWord_3659285) baseStart_3659285 baseEnd_3659285 := by
    simpa [prefixWord, tailWord_3659285, baseEnd_3659285] using wordTrace_append hprefix tailTrace_3659285
  have hstable : (prefixWord ++ tailWord_3659285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659285).length < 2 ^ (prefixWord ++ tailWord_3659285).sum := by decide
  have hdescent : baseEnd_3659285 < baseStart_3659285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659321 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 2, 5]
def baseStart_3659321 : Nat := 118140960795 + 3659321 * 2 ^ 59
def prefixEnd_3659321 : Nat := 4983230072969 + 3 ^ 40 * 3659321 * 2
def baseEnd_3659321 : Nat := 626330180697127541152865

theorem tailTrace_3659321 : CollatzResearch.WordTrace tailWord_3659321 prefixEnd_3659321 626330180697127541152865 := by
  unfold tailWord_3659321
  simp only [CollatzResearch.WordTrace]
  refine ⟨133466401575912454116121817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88977601050608302744081211 133466401575912454116121817)
  ·
    refine ⟨100099801181934340587091363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133466401575912454116121817 100099801181934340587091363)
    ·
      refine ⟨150149701772901510880637045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100099801181934340587091363 150149701772901510880637045)
      ·
        refine ⟨14076534541209516645059723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150149701772901510880637045 14076534541209516645059723)
        ·
          refine ⟨21114801811814274967589585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14076534541209516645059723 21114801811814274967589585)
          ·
            refine ⟨15836101358860706225692189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21114801811814274967589585 15836101358860706225692189)
            ·
              refine ⟨5938538009572764834634571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15836101358860706225692189 5938538009572764834634571)
              ·
                refine ⟨8907807014359147251951857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5938538009572764834634571 8907807014359147251951857)
                ·
                  refine ⟨6680855260769360438963893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8907807014359147251951857 6680855260769360438963893)
                  ·
                    refine ⟨626330180697127541152865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6680855260769360438963893 626330180697127541152865)
                    ·
                      rfl

theorem cell23_3659321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 2, 5].length) (baseStart_3659321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659321 prefixEnd_3659321 := by exact prefixLift 3659321
  have htrace : WordTrace (prefixWord ++ tailWord_3659321) baseStart_3659321 baseEnd_3659321 := by
    simpa [prefixWord, tailWord_3659321, baseEnd_3659321] using wordTrace_append hprefix tailTrace_3659321
  have hstable : (prefixWord ++ tailWord_3659321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659321).length < 2 ^ (prefixWord ++ tailWord_3659321).sum := by decide
  have hdescent : baseEnd_3659321 < baseStart_3659321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659351 : List Nat := [1, 1, 3, 2, 2, 3, 1, 3, 3, 4]
def baseStart_3659351 : Nat := 118140960795 + 3659351 * 2 ^ 59
def prefixEnd_3659351 : Nat := 4983230072969 + 3 ^ 40 * 3659351 * 2
def baseEnd_3659351 : Nat := 626335315503672502027819

theorem tailTrace_3659351 : CollatzResearch.WordTrace tailWord_3659351 prefixEnd_3659351 626335315503672502027819 := by
  unfold tailWord_3659351
  simp only [CollatzResearch.WordTrace]
  refine ⟨133467495765803769239713907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88978330510535846159809271 133467495765803769239713907)
  ·
    refine ⟨200201243648705653859570861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133467495765803769239713907 200201243648705653859570861)
    ·
      refine ⟨75075466368264620197339073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200201243648705653859570861 75075466368264620197339073)
      ·
        refine ⟨56306599776198465148004305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75075466368264620197339073 56306599776198465148004305)
        ·
          refine ⟨42229949832148848861003229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56306599776198465148004305 42229949832148848861003229)
          ·
            refine ⟨15836231187055818322876211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42229949832148848861003229 15836231187055818322876211)
            ·
              refine ⟨23754346780583727484314317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15836231187055818322876211 23754346780583727484314317)
              ·
                refine ⟨8907880042718897806617869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23754346780583727484314317 8907880042718897806617869)
                ·
                  refine ⟨3340455016019586677481701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8907880042718897806617869 3340455016019586677481701)
                  ·
                    refine ⟨626335315503672502027819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3340455016019586677481701 626335315503672502027819)
                    ·
                      rfl

theorem cell23_3659351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_3659351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659351 prefixEnd_3659351 := by exact prefixLift 3659351
  have htrace : WordTrace (prefixWord ++ tailWord_3659351) baseStart_3659351 baseEnd_3659351 := by
    simpa [prefixWord, tailWord_3659351, baseEnd_3659351] using wordTrace_append hprefix tailTrace_3659351
  have hstable : (prefixWord ++ tailWord_3659351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659351).length < 2 ^ (prefixWord ++ tailWord_3659351).sum := by decide
  have hdescent : baseEnd_3659351 < baseStart_3659351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659368 : List Nat := [2, 1, 4, 3, 1, 1, 2, 2, 3, 4]
def baseStart_3659368 : Nat := 118140960795 + 3659368 * 2 ^ 59
def prefixEnd_3659368 : Nat := 4983230072969 + 3 ^ 40 * 3659368 * 2
def baseEnd_3659368 : Nat := 626338225227381313190293

theorem tailTrace_3659368 : CollatzResearch.WordTrace tailWord_3659368 prefixEnd_3659368 626338225227381313190293 := by
  unfold tailWord_3659368
  simp only [CollatzResearch.WordTrace]
  refine ⟨66734057903371090571541379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88978743871161454095388505 66734057903371090571541379)
  ·
    refine ⟨100101086855056635857312069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66734057903371090571541379 100101086855056635857312069)
    ·
      refine ⟨18768953785323119223246013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100101086855056635857312069 18768953785323119223246013)
      ·
        refine ⟨7038357669496169708717255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18768953785323119223246013 7038357669496169708717255)
        ·
          refine ⟨10557536504244254563075883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7038357669496169708717255 10557536504244254563075883)
          ·
            refine ⟨15836304756366381844613825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10557536504244254563075883 15836304756366381844613825)
            ·
              refine ⟨11877228567274786383460369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15836304756366381844613825 11877228567274786383460369)
              ·
                refine ⟨8907921425456089787595277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11877228567274786383460369 8907921425456089787595277)
                ·
                  refine ⟨3340470534546033670348229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8907921425456089787595277 3340470534546033670348229)
                  ·
                    refine ⟨626338225227381313190293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3340470534546033670348229 626338225227381313190293)
                    ·
                      rfl

theorem cell23_3659368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_3659368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659368 prefixEnd_3659368 := by exact prefixLift 3659368
  have htrace : WordTrace (prefixWord ++ tailWord_3659368) baseStart_3659368 baseEnd_3659368 := by
    simpa [prefixWord, tailWord_3659368, baseEnd_3659368] using wordTrace_append hprefix tailTrace_3659368
  have hstable : (prefixWord ++ tailWord_3659368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659368).length < 2 ^ (prefixWord ++ tailWord_3659368).sum := by decide
  have hdescent : baseEnd_3659368 < baseStart_3659368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659381 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 8]
def baseStart_3659381 : Nat := 118140960795 + 3659381 * 2 ^ 59
def prefixEnd_3659381 : Nat := 4983230072969 + 3 ^ 40 * 3659381 * 2
def baseEnd_3659381 : Nat := 208780150103405820967591

theorem tailTrace_3659381 : CollatzResearch.WordTrace tailWord_3659381 prefixEnd_3659381 208780150103405820967591 := by
  unfold tailWord_3659381
  simp only [CollatzResearch.WordTrace]
  refine ⟨133468589955695084363305997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88979059970463389575537331 133468589955695084363305997)
  ·
    refine ⟨50050721233385656636239749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133468589955695084363305997 50050721233385656636239749)
    ·
      refine ⟨9384510231259810619294953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50050721233385656636239749 9384510231259810619294953)
      ·
        refine ⟨7038382673444857964471215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9384510231259810619294953 7038382673444857964471215)
        ·
          refine ⟨10557574010167286946706823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7038382673444857964471215 10557574010167286946706823)
          ·
            refine ⟨15836361015250930420060235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10557574010167286946706823 15836361015250930420060235)
            ·
              refine ⟨23754541522876395630090353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15836361015250930420060235 23754541522876395630090353)
              ·
                refine ⟨17815906142157296722567765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23754541522876395630090353 17815906142157296722567765)
                ·
                  refine ⟨208780150103405820967591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17815906142157296722567765 208780150103405820967591)
                  ·
                    rfl

theorem cell23_3659381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_3659381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659381 prefixEnd_3659381 := by exact prefixLift 3659381
  have htrace : WordTrace (prefixWord ++ tailWord_3659381) baseStart_3659381 baseEnd_3659381 := by
    simpa [prefixWord, tailWord_3659381, baseEnd_3659381] using wordTrace_append hprefix tailTrace_3659381
  have hstable : (prefixWord ++ tailWord_3659381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659381).length < 2 ^ (prefixWord ++ tailWord_3659381).sum := by decide
  have hdescent : baseEnd_3659381 < baseStart_3659381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659402 : List Nat := [3, 1, 2, 3, 2, 2, 3, 2, 1, 4]
def baseStart_3659402 : Nat := 118140960795 + 3659402 * 2 ^ 59
def prefixEnd_3659402 : Nat := 4983230072969 + 3 ^ 40 * 3659402 * 2
def baseEnd_3659402 : Nat := 626344044674798935515241

theorem tailTrace_3659402 : CollatzResearch.WordTrace tailWord_3659402 prefixEnd_3659402 626344044674798935515241 := by
  unfold tailWord_3659402
  simp only [CollatzResearch.WordTrace]
  refine ⟨33367338972154751237455115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88979570592412669966546973 33367338972154751237455115)
  ·
    refine ⟨50051008458232126856182673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33367338972154751237455115 50051008458232126856182673)
    ·
      refine ⟨37538256343674095142137005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50051008458232126856182673 37538256343674095142137005)
      ·
        refine ⟨14076846128877785678301377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37538256343674095142137005 14076846128877785678301377)
        ·
          refine ⟨10557634596658339258726033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14076846128877785678301377 10557634596658339258726033)
          ·
            refine ⟨7918225947493754444044525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10557634596658339258726033 7918225947493754444044525)
            ·
              refine ⟨2969334730310157916516697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7918225947493754444044525 2969334730310157916516697)
              ·
                refine ⟨2227001047732618437387523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2969334730310157916516697 2227001047732618437387523)
                ·
                  refine ⟨3340501571598927656081285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227001047732618437387523 3340501571598927656081285)
                  ·
                    refine ⟨626344044674798935515241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3340501571598927656081285 626344044674798935515241)
                    ·
                      rfl

theorem cell23_3659402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_3659402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659402 prefixEnd_3659402 := by exact prefixLift 3659402
  have htrace : WordTrace (prefixWord ++ tailWord_3659402) baseStart_3659402 baseEnd_3659402 := by
    simpa [prefixWord, tailWord_3659402, baseEnd_3659402] using wordTrace_append hprefix tailTrace_3659402
  have hstable : (prefixWord ++ tailWord_3659402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659402).length < 2 ^ (prefixWord ++ tailWord_3659402).sum := by decide
  have hdescent : baseEnd_3659402 < baseStart_3659402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659428 : List Nat := [2, 3, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_3659428 : Nat := 118140960795 + 3659428 * 2 ^ 59
def prefixEnd_3659428 : Nat := 4983230072969 + 3 ^ 40 * 3659428 * 2
def baseEnd_3659428 : Nat := 626348494840471234940201

theorem tailTrace_3659428 : CollatzResearch.WordTrace tailWord_3659428 prefixEnd_3659428 626348494840471234940201 := by
  unfold tailWord_3659428
  simp only [CollatzResearch.WordTrace]
  refine ⟨66735152093262405695133469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88980202791016540926844625 66735152093262405695133469)
  ·
    refine ⟨25025682034973402135675051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66735152093262405695133469 25025682034973402135675051)
    ·
      refine ⟨37538523052460103203512577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25025682034973402135675051 37538523052460103203512577)
      ·
        refine ⟨28153892289345077402634433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37538523052460103203512577 28153892289345077402634433)
        ·
          refine ⟨21115419217008808051975825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28153892289345077402634433 21115419217008808051975825)
          ·
            refine ⟨15836564412756606038981869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21115419217008808051975825 15836564412756606038981869)
            ·
              refine ⟨5938711654783727264618201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15836564412756606038981869 5938711654783727264618201)
              ·
                refine ⟨4454033741087795448463651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5938711654783727264618201 4454033741087795448463651)
                ·
                  refine ⟨6681050611631693172695477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454033741087795448463651 6681050611631693172695477)
                  ·
                    refine ⟨626348494840471234940201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6681050611631693172695477 626348494840471234940201)
                    ·
                      rfl

theorem cell23_3659428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_3659428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659428 prefixEnd_3659428 := by exact prefixLift 3659428
  have htrace : WordTrace (prefixWord ++ tailWord_3659428) baseStart_3659428 baseEnd_3659428 := by
    simpa [prefixWord, tailWord_3659428, baseEnd_3659428] using wordTrace_append hprefix tailTrace_3659428
  have hstable : (prefixWord ++ tailWord_3659428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659428).length < 2 ^ (prefixWord ++ tailWord_3659428).sum := by decide
  have hdescent : baseEnd_3659428 < baseStart_3659428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659498 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_3659498 : Nat := 118140960795 + 3659498 * 2 ^ 59
def prefixEnd_3659498 : Nat := 4983230072969 + 3 ^ 40 * 3659498 * 2
def baseEnd_3659498 : Nat := 1879081428167228430945281

theorem tailTrace_3659498 : CollatzResearch.WordTrace tailWord_3659498 prefixEnd_3659498 1879081428167228430945281 := by
  unfold tailWord_3659498
  simp only [CollatzResearch.WordTrace]
  refine ⟨33368214324067803336328787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88981904864180808896876765 33368214324067803336328787)
  ·
    refine ⟨50052321486101705004493181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33368214324067803336328787 50052321486101705004493181)
    ·
      refine ⟨18769620557288139376684943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50052321486101705004493181 18769620557288139376684943)
      ·
        refine ⟨28154430835932209065027415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18769620557288139376684943 28154430835932209065027415)
        ·
          refine ⟨42231646253898313597541123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28154430835932209065027415 42231646253898313597541123)
          ·
            refine ⟨63347469380847470396311685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42231646253898313597541123 63347469380847470396311685)
            ·
              refine ⟨11877650508908900699308441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63347469380847470396311685 11877650508908900699308441)
              ·
                refine ⟨8908237881681675524481331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11877650508908900699308441 8908237881681675524481331)
                ·
                  refine ⟨13362356822522513286721997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8908237881681675524481331 13362356822522513286721997)
                  ·
                    refine ⟨5010883808445942482520749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13362356822522513286721997 5010883808445942482520749)
                    ·
                      refine ⟨1879081428167228430945281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5010883808445942482520749 1879081428167228430945281)
                      ·
                        rfl

theorem cell23_3659498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_3659498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659498 prefixEnd_3659498 := by exact prefixLift 3659498
  have htrace : WordTrace (prefixWord ++ tailWord_3659498) baseStart_3659498 baseEnd_3659498 := by
    simpa [prefixWord, tailWord_3659498, baseEnd_3659498] using wordTrace_append hprefix tailTrace_3659498
  have hstable : (prefixWord ++ tailWord_3659498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659498).length < 2 ^ (prefixWord ++ tailWord_3659498).sum := by decide
  have hdescent : baseEnd_3659498 < baseStart_3659498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659521 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_3659521 : Nat := 118140960795 + 3659521 * 2 ^ 59
def prefixEnd_3659521 : Nat := 4983230072969 + 3 ^ 40 * 3659521 * 2
def baseEnd_3659521 : Nat := 1879093238222281840957675

theorem tailTrace_3659521 : CollatzResearch.WordTrace tailWord_3659521 prefixEnd_3659521 1879093238222281840957675 := by
  unfold tailWord_3659521
  simp only [CollatzResearch.WordTrace]
  refine ⟨133473696175187888273402417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88982464116791925515601611 133473696175187888273402417)
  ·
    refine ⟨100105272131390916205051813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133473696175187888273402417 100105272131390916205051813)
    ·
      refine ⟨18769738524635796788447215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100105272131390916205051813 18769738524635796788447215)
      ·
        refine ⟨28154607786953695182670823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18769738524635796788447215 28154607786953695182670823)
        ·
          refine ⟨42231911680430542774006235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28154607786953695182670823 42231911680430542774006235)
          ·
            refine ⟨63347867520645814161009353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42231911680430542774006235 63347867520645814161009353)
            ·
              refine ⟨47510900640484360620757015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63347867520645814161009353 47510900640484360620757015)
              ·
                refine ⟨71266350960726540931135523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47510900640484360620757015 71266350960726540931135523)
                ·
                  refine ⟨106899526441089811396703285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71266350960726540931135523 106899526441089811396703285)
                  ·
                    refine ⟨10021830603852169818440933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106899526441089811396703285 10021830603852169818440933)
                    ·
                      refine ⟨1879093238222281840957675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10021830603852169818440933 1879093238222281840957675)
                      ·
                        rfl

theorem cell23_3659521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_3659521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659521 prefixEnd_3659521 := by exact prefixLift 3659521
  have htrace : WordTrace (prefixWord ++ tailWord_3659521) baseStart_3659521 baseEnd_3659521 := by
    simpa [prefixWord, tailWord_3659521, baseEnd_3659521] using wordTrace_append hprefix tailTrace_3659521
  have hstable : (prefixWord ++ tailWord_3659521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659521).length < 2 ^ (prefixWord ++ tailWord_3659521).sum := by decide
  have hdescent : baseEnd_3659521 < baseStart_3659521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659531 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 2, 6]
def baseStart_3659531 : Nat := 118140960795 + 3659531 * 2 ^ 59
def prefixEnd_3659531 : Nat := 4983230072969 + 3 ^ 40 * 3659531 * 2
def baseEnd_3659531 : Nat := 626366124342942267277543

theorem tailTrace_3659531 : CollatzResearch.WordTrace tailWord_3659531 prefixEnd_3659531 626366124342942267277543 := by
  unfold tailWord_3659531
  simp only [CollatzResearch.WordTrace]
  refine ⟨133474060905151659981266447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88982707270101106654177631 133474060905151659981266447)
  ·
    refine ⟨200211091357727489971899671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133474060905151659981266447 200211091357727489971899671)
    ·
      refine ⟨300316637036591234957849507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200211091357727489971899671 300316637036591234957849507)
      ·
        refine ⟨450474955554886852436774261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300316637036591234957849507 450474955554886852436774261)
        ·
          refine ⟨42232027083270642415947587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 450474955554886852436774261 42232027083270642415947587)
          ·
            refine ⟨63348040624905963623921381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42232027083270642415947587 63348040624905963623921381)
            ·
              refine ⟨11877757617169868179485259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63348040624905963623921381 11877757617169868179485259)
              ·
                refine ⟨17816636425754802269227889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11877757617169868179485259 17816636425754802269227889)
                ·
                  refine ⟨13362477319316101701920917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17816636425754802269227889 13362477319316101701920917)
                  ·
                    refine ⟨626366124342942267277543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13362477319316101701920917 626366124342942267277543)
                    ·
                      rfl

theorem cell23_3659531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 6].length) (baseStart_3659531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659531 prefixEnd_3659531 := by exact prefixLift 3659531
  have htrace : WordTrace (prefixWord ++ tailWord_3659531) baseStart_3659531 baseEnd_3659531 := by
    simpa [prefixWord, tailWord_3659531, baseEnd_3659531] using wordTrace_append hprefix tailTrace_3659531
  have hstable : (prefixWord ++ tailWord_3659531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659531).length < 2 ^ (prefixWord ++ tailWord_3659531).sum := by decide
  have hdescent : baseEnd_3659531 < baseStart_3659531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659550 : List Nat := [4, 3, 2, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_3659550 : Nat := 118140960795 + 3659550 * 2 ^ 59
def prefixEnd_3659550 : Nat := 4983230072969 + 3 ^ 40 * 3659550 * 2
def baseEnd_3659550 : Nat := 1879108129161262227495043

theorem tailTrace_3659550 : CollatzResearch.WordTrace tailWord_3659550 prefixEnd_3659550 1879108129161262227495043 := by
  unfold tailWord_3659550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16684344236510353278276013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88983169261388550817472069 16684344236510353278276013)
  ·
    refine ⟨6256629088691382479353505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16684344236510353278276013 6256629088691382479353505)
    ·
      refine ⟨4692471816518536859515129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6256629088691382479353505 4692471816518536859515129)
      ·
        refine ⟨3519353862388902644636347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4692471816518536859515129 3519353862388902644636347)
        ·
          refine ⟨5279030793583353966954521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519353862388902644636347 5279030793583353966954521)
          ·
            refine ⟨3959273095187515475215891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5279030793583353966954521 3959273095187515475215891)
            ·
              refine ⟨5938909642781273212823837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959273095187515475215891 5938909642781273212823837)
              ·
                refine ⟨2227091116042977454808939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5938909642781273212823837 2227091116042977454808939)
                ·
                  refine ⟨3340636674064466182213409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227091116042977454808939 3340636674064466182213409)
                  ·
                    refine ⟨2505477505548349636660057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3340636674064466182213409 2505477505548349636660057)
                    ·
                      refine ⟨1879108129161262227495043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2505477505548349636660057 1879108129161262227495043)
                      ·
                        rfl

theorem cell23_3659550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_3659550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659550 prefixEnd_3659550 := by exact prefixLift 3659550
  have htrace : WordTrace (prefixWord ++ tailWord_3659550) baseStart_3659550 baseEnd_3659550 := by
    simpa [prefixWord, tailWord_3659550, baseEnd_3659550] using wordTrace_append hprefix tailTrace_3659550
  have hstable : (prefixWord ++ tailWord_3659550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659550).length < 2 ^ (prefixWord ++ tailWord_3659550).sum := by decide
  have hdescent : baseEnd_3659550 < baseStart_3659550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659555 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 4, 2, 2]
def baseStart_3659555 : Nat := 118140960795 + 3659555 * 2 ^ 59
def prefixEnd_3659555 : Nat := 4983230072969 + 3 ^ 40 * 3659555 * 2
def baseEnd_3659555 : Nat := 1879110696564534707932519

theorem tailTrace_3659555 : CollatzResearch.WordTrace tailWord_3659555 prefixEnd_3659555 1879110696564534707932519 := by
  unfold tailWord_3659555
  simp only [CollatzResearch.WordTrace]
  refine ⟨133474936257064712080140119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88983290838043141386760079 133474936257064712080140119)
  ·
    refine ⟨200212404385597068120210179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133474936257064712080140119 200212404385597068120210179)
    ·
      refine ⟨300318606578395602180315269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200212404385597068120210179 300318606578395602180315269)
      ·
        refine ⟨56309738733449175408809113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300318606578395602180315269 56309738733449175408809113)
        ·
          refine ⟨42232304050086881556606835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56309738733449175408809113 42232304050086881556606835)
          ·
            refine ⟨63348456075130322334910253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42232304050086881556606835 63348456075130322334910253)
            ·
              refine ⟨23755671028173870875591345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63348456075130322334910253 23755671028173870875591345)
              ·
                refine ⟨17816753271130403156693509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23755671028173870875591345 17816753271130403156693509)
                ·
                  refine ⟨3340641238336950591880033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17816753271130403156693509 3340641238336950591880033)
                  ·
                    refine ⟨2505480928752712943910025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3340641238336950591880033 2505480928752712943910025)
                    ·
                      refine ⟨1879110696564534707932519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2505480928752712943910025 1879110696564534707932519)
                      ·
                        rfl

theorem cell23_3659555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_3659555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659555 prefixEnd_3659555 := by exact prefixLift 3659555
  have htrace : WordTrace (prefixWord ++ tailWord_3659555) baseStart_3659555 baseEnd_3659555 := by
    simpa [prefixWord, tailWord_3659555, baseEnd_3659555] using wordTrace_append hprefix tailTrace_3659555
  have hstable : (prefixWord ++ tailWord_3659555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659555).length < 2 ^ (prefixWord ++ tailWord_3659555).sum := by decide
  have hdescent : baseEnd_3659555 < baseStart_3659555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659578 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 7]
def baseStart_3659578 : Nat := 118140960795 + 3659578 * 2 ^ 59
def prefixEnd_3659578 : Nat := 4983230072969 + 3 ^ 40 * 3659578 * 2
def baseEnd_3659578 : Nat := 208791389624398679771657

theorem tailTrace_3659578 : CollatzResearch.WordTrace tailWord_3659578 prefixEnd_3659578 208791389624398679771657 := by
  unfold tailWord_3659578
  simp only [CollatzResearch.WordTrace]
  refine ⟨33368943783995346752056847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88983850090654258005484925 33368943783995346752056847)
  ·
    refine ⟨50053415675993020128085271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33368943783995346752056847 50053415675993020128085271)
    ·
      refine ⟨75080123513989530192127907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50053415675993020128085271 75080123513989530192127907)
      ·
        refine ⟨112620185270984295288191861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75080123513989530192127907 112620185270984295288191861)
        ·
          refine ⟨10558142369154777683267987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112620185270984295288191861 10558142369154777683267987)
          ·
            refine ⟨15837213553732166524901981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10558142369154777683267987 15837213553732166524901981)
            ·
              refine ⟨5938955082649562446838243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15837213553732166524901981 5938955082649562446838243)
              ·
                refine ⟨8908432623974343670257365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5938955082649562446838243 8908432623974343670257365)
                ·
                  refine ⟨208791389624398679771657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8908432623974343670257365 208791389624398679771657)
                  ·
                    rfl

theorem cell23_3659578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_3659578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659578 prefixEnd_3659578 := by exact prefixLift 3659578
  have htrace : WordTrace (prefixWord ++ tailWord_3659578) baseStart_3659578 baseEnd_3659578 := by
    simpa [prefixWord, tailWord_3659578, baseEnd_3659578] using wordTrace_append hprefix tailTrace_3659578
  have hstable : (prefixWord ++ tailWord_3659578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659578).length < 2 ^ (prefixWord ++ tailWord_3659578).sum := by decide
  have hdescent : baseEnd_3659578 < baseStart_3659578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659591 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 3, 7]
def baseStart_3659591 : Nat := 118140960795 + 3659591 * 2 ^ 59
def prefixEnd_3659591 : Nat := 4983230072969 + 3 ^ 40 * 3659591 * 2
def baseEnd_3659591 : Nat := 626376393956032189027451

theorem tailTrace_3659591 : CollatzResearch.WordTrace tailWord_3659591 prefixEnd_3659591 626376393956032189027451 := by
  unfold tailWord_3659591
  simp only [CollatzResearch.WordTrace]
  refine ⟨133476249284934290228450627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88984166189956193485633751 133476249284934290228450627)
  ·
    refine ⟨200214373927401435342675941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133476249284934290228450627 200214373927401435342675941)
    ·
      refine ⟨37540195111387769126751739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200214373927401435342675941 37540195111387769126751739)
      ·
        refine ⟨56310292667081653690127609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37540195111387769126751739 56310292667081653690127609)
        ·
          refine ⟨42232719500311240267595707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56310292667081653690127609 42232719500311240267595707)
          ·
            refine ⟨63349079250466860401393561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42232719500311240267595707 63349079250466860401393561)
            ·
              refine ⟨47511809437850145301045171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63349079250466860401393561 47511809437850145301045171)
              ·
                refine ⟨71267714156775217951567757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47511809437850145301045171 71267714156775217951567757)
                ·
                  refine ⟨26725392808790706731837909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71267714156775217951567757 26725392808790706731837909)
                  ·
                    refine ⟨626376393956032189027451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26725392808790706731837909 626376393956032189027451)
                    ·
                      rfl

theorem cell23_3659591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_3659591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659591 prefixEnd_3659591 := by exact prefixLift 3659591
  have htrace : WordTrace (prefixWord ++ tailWord_3659591) baseStart_3659591 baseEnd_3659591 := by
    simpa [prefixWord, tailWord_3659591, baseEnd_3659591] using wordTrace_append hprefix tailTrace_3659591
  have hstable : (prefixWord ++ tailWord_3659591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659591).length < 2 ^ (prefixWord ++ tailWord_3659591).sum := by decide
  have hdescent : baseEnd_3659591 < baseStart_3659591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659648 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 3]
def baseStart_3659648 : Nat := 118140960795 + 3659648 * 2 ^ 59
def prefixEnd_3659648 : Nat := 4983230072969 + 3 ^ 40 * 3659648 * 2
def baseEnd_3659648 : Nat := 1879158450265402844069591

theorem tailTrace_3659648 : CollatzResearch.WordTrace tailWord_3659648 prefixEnd_3659648 1879158450265402844069591 := by
  unfold tailWord_3659648
  simp only [CollatzResearch.WordTrace]
  refine ⟨66739164122863894481637799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88985552163818525975517065 66739164122863894481637799)
  ·
    refine ⟨100108746184295841722456699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66739164122863894481637799 100108746184295841722456699)
    ·
      refine ⟨150163119276443762583685049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100108746184295841722456699 150163119276443762583685049)
      ·
        refine ⟨112622339457332821937763787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150163119276443762583685049 112622339457332821937763787)
        ·
          refine ⟨168933509185999232906645681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112622339457332821937763787 168933509185999232906645681)
          ·
            refine ⟨126700131889499424679984261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168933509185999232906645681 126700131889499424679984261)
            ·
              refine ⟨23756274729281142127497049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126700131889499424679984261 23756274729281142127497049)
              ·
                refine ⟨17817206046960856595622787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23756274729281142127497049 17817206046960856595622787)
                ·
                  refine ⟨26725809070441284893434181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17817206046960856595622787 26725809070441284893434181)
                  ·
                    refine ⟨5011089200707740917518909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26725809070441284893434181 5011089200707740917518909)
                    ·
                      refine ⟨1879158450265402844069591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5011089200707740917518909 1879158450265402844069591)
                      ·
                        rfl

theorem cell23_3659648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_3659648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659648 prefixEnd_3659648 := by exact prefixLift 3659648
  have htrace : WordTrace (prefixWord ++ tailWord_3659648) baseStart_3659648 baseEnd_3659648 := by
    simpa [prefixWord, tailWord_3659648, baseEnd_3659648] using wordTrace_append hprefix tailTrace_3659648
  have hstable : (prefixWord ++ tailWord_3659648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659648).length < 2 ^ (prefixWord ++ tailWord_3659648).sum := by decide
  have hdescent : baseEnd_3659648 < baseStart_3659648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659662 : List Nat := [4, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3659662 : Nat := 118140960795 + 3659662 * 2 ^ 59
def prefixEnd_3659662 : Nat := 4983230072969 + 3 ^ 40 * 3659662 * 2
def baseEnd_3659662 : Nat := 1879165638994565789294527

theorem tailTrace_3659662 : CollatzResearch.WordTrace tailWord_3659662 prefixEnd_3659662 1879165638994565789294527 := by
  unfold tailWord_3659662
  simp only [CollatzResearch.WordTrace]
  refine ⟨16684854858459633669285655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88985892578451379569523493 16684854858459633669285655)
  ·
    refine ⟨25027282287689450503928483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16684854858459633669285655 25027282287689450503928483)
    ·
      refine ⟨37540923431534175755892725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25027282287689450503928483 37540923431534175755892725)
      ·
        refine ⟨3519461571706328977114943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37540923431534175755892725 3519461571706328977114943)
        ·
          refine ⟨5279192357559493465672415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519461571706328977114943 5279192357559493465672415)
          ·
            refine ⟨7918788536339240198508623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279192357559493465672415 7918788536339240198508623)
            ·
              refine ⟨11878182804508860297762935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7918788536339240198508623 11878182804508860297762935)
              ·
                refine ⟨17817274206763290446644403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11878182804508860297762935 17817274206763290446644403)
                ·
                  refine ⟨26725911310144935669966605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17817274206763290446644403 26725911310144935669966605)
                  ·
                    refine ⟨10022216741304350876237477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26725911310144935669966605 10022216741304350876237477)
                    ·
                      refine ⟨1879165638994565789294527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10022216741304350876237477 1879165638994565789294527)
                      ·
                        rfl

theorem cell23_3659662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3659662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659662 prefixEnd_3659662 := by exact prefixLift 3659662
  have htrace : WordTrace (prefixWord ++ tailWord_3659662) baseStart_3659662 baseEnd_3659662 := by
    simpa [prefixWord, tailWord_3659662, baseEnd_3659662] using wordTrace_append hprefix tailTrace_3659662
  have hstable : (prefixWord ++ tailWord_3659662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659662).length < 2 ^ (prefixWord ++ tailWord_3659662).sum := by decide
  have hdescent : baseEnd_3659662 < baseStart_3659662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659665 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 3]
def baseStart_3659665 : Nat := 118140960795 + 3659665 * 2 ^ 59
def prefixEnd_3659665 : Nat := 4983230072969 + 3 ^ 40 * 3659665 * 2
def baseEnd_3659665 : Nat := 1879167179436529277557013

theorem tailTrace_3659665 : CollatzResearch.WordTrace tailWord_3659665 prefixEnd_3659665 1879167179436529277557013 := by
  unfold tailWord_3659665
  simp only [CollatzResearch.WordTrace]
  refine ⟨133478948286666200866644449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88985965524444133911096299 133478948286666200866644449)
  ·
    refine ⟨100109211214999650649983337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133478948286666200866644449 100109211214999650649983337)
    ·
      refine ⟨75081908411249737987487503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100109211214999650649983337 75081908411249737987487503)
      ·
        refine ⟨112622862616874606981231255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75081908411249737987487503 112622862616874606981231255)
        ·
          refine ⟨168934293925311910471846883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112622862616874606981231255 168934293925311910471846883)
          ·
            refine ⟨253401440887967865707770325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168934293925311910471846883 253401440887967865707770325)
            ·
              refine ⟨5939096270811746852525867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 253401440887967865707770325 5939096270811746852525867)
              ·
                refine ⟨8908644406217620278788801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939096270811746852525867 8908644406217620278788801)
                ·
                  refine ⟨6681483304663215209091601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8908644406217620278788801 6681483304663215209091601)
                  ·
                    refine ⟨5011112478497411406818701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6681483304663215209091601 5011112478497411406818701)
                    ·
                      refine ⟨1879167179436529277557013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5011112478497411406818701 1879167179436529277557013)
                      ·
                        rfl

theorem cell23_3659665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_3659665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659665 prefixEnd_3659665 := by exact prefixLift 3659665
  have htrace : WordTrace (prefixWord ++ tailWord_3659665) baseStart_3659665 baseEnd_3659665 := by
    simpa [prefixWord, tailWord_3659665, baseEnd_3659665] using wordTrace_append hprefix tailTrace_3659665
  have hstable : (prefixWord ++ tailWord_3659665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659665).length < 2 ^ (prefixWord ++ tailWord_3659665).sum := by decide
  have hdescent : baseEnd_3659665 < baseStart_3659665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659698 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_3659698 : Nat := 118140960795 + 3659698 * 2 ^ 59
def prefixEnd_3659698 : Nat := 4983230072969 + 3 ^ 40 * 3659698 * 2
def baseEnd_3659698 : Nat := 626394708099375882814787

theorem tailTrace_3659698 : CollatzResearch.WordTrace tailWord_3659698 prefixEnd_3659698 626394708099375882814787 := by
  unfold tailWord_3659698
  simp only [CollatzResearch.WordTrace]
  refine ⟨33370037973886661875648937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88986767930364431668397165 33370037973886661875648937)
  ·
    refine ⟨25027528480414996406736703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33370037973886661875648937 25027528480414996406736703)
    ·
      refine ⟨37541292720622494610105055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25027528480414996406736703 37541292720622494610105055)
      ·
        refine ⟨56311939080933741915157583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37541292720622494610105055 56311939080933741915157583)
        ·
          refine ⟨84467908621400612872736375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56311939080933741915157583 84467908621400612872736375)
          ·
            refine ⟨126701862932100919309104563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84467908621400612872736375 126701862932100919309104563)
            ·
              refine ⟨190052794398151378963656845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126701862932100919309104563 190052794398151378963656845)
              ·
                refine ⟨71269797899306767111371317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190052794398151378963656845 71269797899306767111371317)
                ·
                  refine ⟨6681543553060009416691061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71269797899306767111371317 6681543553060009416691061)
                  ·
                    refine ⟨626394708099375882814787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6681543553060009416691061 626394708099375882814787)
                    ·
                      rfl

theorem cell23_3659698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_3659698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659698 prefixEnd_3659698 := by exact prefixLift 3659698
  have htrace : WordTrace (prefixWord ++ tailWord_3659698) baseStart_3659698 baseEnd_3659698 := by
    simpa [prefixWord, tailWord_3659698, baseEnd_3659698] using wordTrace_append hprefix tailTrace_3659698
  have hstable : (prefixWord ++ tailWord_3659698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659698).length < 2 ^ (prefixWord ++ tailWord_3659698).sum := by decide
  have hdescent : baseEnd_3659698 < baseStart_3659698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659705 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 3, 5, 2]
def baseStart_3659705 : Nat := 118140960795 + 3659705 * 2 ^ 59
def prefixEnd_3659705 : Nat := 4983230072969 + 3 ^ 40 * 3659705 * 2
def baseEnd_3659705 : Nat := 1879187718662709121056829

theorem tailTrace_3659705 : CollatzResearch.WordTrace tailWord_3659705 prefixEnd_3659705 1879187718662709121056829 := by
  unfold tailWord_3659705
  simp only [CollatzResearch.WordTrace]
  refine ⟨133480407206521287698100569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88986938137680858465400379 133480407206521287698100569)
  ·
    refine ⟨100110305404890965773575427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133480407206521287698100569 100110305404890965773575427)
    ·
      refine ⟨150165458107336448660363141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100110305404890965773575427 150165458107336448660363141)
      ·
        refine ⟨28156023395125584123818089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150165458107336448660363141 28156023395125584123818089)
        ·
          refine ⟨21117017546344188092863567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28156023395125584123818089 21117017546344188092863567)
          ·
            refine ⟨31675526319516282139295351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21117017546344188092863567 31675526319516282139295351)
            ·
              refine ⟨47513289479274423208943027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31675526319516282139295351 47513289479274423208943027)
              ·
                refine ⟨71269934218911634813414541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47513289479274423208943027 71269934218911634813414541)
                ·
                  refine ⟨26726225332091863055030453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71269934218911634813414541 26726225332091863055030453)
                  ·
                    refine ⟨2505583624883612161409105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26726225332091863055030453 2505583624883612161409105)
                    ·
                      refine ⟨1879187718662709121056829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2505583624883612161409105 1879187718662709121056829)
                      ·
                        rfl

theorem cell23_3659705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_3659705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659705 prefixEnd_3659705 := by exact prefixLift 3659705
  have htrace : WordTrace (prefixWord ++ tailWord_3659705) baseStart_3659705 baseEnd_3659705 := by
    simpa [prefixWord, tailWord_3659705, baseEnd_3659705] using wordTrace_append hprefix tailTrace_3659705
  have hstable : (prefixWord ++ tailWord_3659705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659705).length < 2 ^ (prefixWord ++ tailWord_3659705).sum := by decide
  have hdescent : baseEnd_3659705 < baseStart_3659705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659728 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 1, 6]
def baseStart_3659728 : Nat := 118140960795 + 3659728 * 2 ^ 59
def prefixEnd_3659728 : Nat := 4983230072969 + 3 ^ 40 * 3659728 * 2
def baseEnd_3659728 : Nat := 626399842905920843689741

theorem tailTrace_3659728 : CollatzResearch.WordTrace tailWord_3659728 prefixEnd_3659728 626399842905920843689741 := by
  unfold tailWord_3659728
  simp only [CollatzResearch.WordTrace]
  refine ⟨66740623042718981313093919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88987497390291975084125225 66740623042718981313093919)
  ·
    refine ⟨100110934564078471969640879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66740623042718981313093919 100110934564078471969640879)
    ·
      refine ⟨150166401846117707954461319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100110934564078471969640879 150166401846117707954461319)
      ·
        refine ⟨225249602769176561931691979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150166401846117707954461319 225249602769176561931691979)
        ·
          refine ⟨337874404153764842897537969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225249602769176561931691979 337874404153764842897537969)
          ·
            refine ⟨253405803115323632173153477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337874404153764842897537969 253405803115323632173153477)
            ·
              refine ⟨47513588084123181032466277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253405803115323632173153477 47513588084123181032466277)
              ·
                refine ⟨8908797765773096443587427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47513588084123181032466277 8908797765773096443587427)
                ·
                  refine ⟨13363196648659644665381141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8908797765773096443587427 13363196648659644665381141)
                  ·
                    refine ⟨626399842905920843689741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13363196648659644665381141 626399842905920843689741)
                    ·
                      rfl

theorem cell23_3659728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_3659728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659728 prefixEnd_3659728 := by exact prefixLift 3659728
  have htrace : WordTrace (prefixWord ++ tailWord_3659728) baseStart_3659728 baseEnd_3659728 := by
    simpa [prefixWord, tailWord_3659728, baseEnd_3659728] using wordTrace_append hprefix tailTrace_3659728
  have hstable : (prefixWord ++ tailWord_3659728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659728).length < 2 ^ (prefixWord ++ tailWord_3659728).sum := by decide
  have hdescent : baseEnd_3659728 < baseStart_3659728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659735 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 4]
def baseStart_3659735 : Nat := 118140960795 + 3659735 * 2 ^ 59
def prefixEnd_3659735 : Nat := 4983230072969 + 3 ^ 40 * 3659735 * 2
def baseEnd_3659735 : Nat := 1879203123082344003681691

theorem tailTrace_3659735 : CollatzResearch.WordTrace tailWord_3659735 prefixEnd_3659735 1879203123082344003681691 := by
  unfold tailWord_3659735
  simp only [CollatzResearch.WordTrace]
  refine ⟨133481501396412602821692659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88987667597608401881128439 133481501396412602821692659)
  ·
    refine ⟨200222252094618904232538989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133481501396412602821692659 200222252094618904232538989)
    ·
      refine ⟨75083344535482089087202121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200222252094618904232538989 75083344535482089087202121)
      ·
        refine ⟨56312508401611566815401591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75083344535482089087202121 56312508401611566815401591)
        ·
          refine ⟨84468762602417350223102387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56312508401611566815401591 84468762602417350223102387)
          ·
            refine ⟨126703143903626025334653581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84468762602417350223102387 126703143903626025334653581)
            ·
              refine ⟨47513678963859759500495093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126703143903626025334653581 47513678963859759500495093)
              ·
                refine ⟨4454407402861852453171415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47513678963859759500495093 4454407402861852453171415)
                ·
                  refine ⟨6681611104292778679757123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454407402861852453171415 6681611104292778679757123)
                  ·
                    refine ⟨10022416656439168019635685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6681611104292778679757123 10022416656439168019635685)
                    ·
                      refine ⟨1879203123082344003681691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10022416656439168019635685 1879203123082344003681691)
                      ·
                        rfl

theorem cell23_3659735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_3659735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659735 prefixEnd_3659735 := by exact prefixLift 3659735
  have htrace : WordTrace (prefixWord ++ tailWord_3659735) baseStart_3659735 baseEnd_3659735 := by
    simpa [prefixWord, tailWord_3659735, baseEnd_3659735] using wordTrace_append hprefix tailTrace_3659735
  have hstable : (prefixWord ++ tailWord_3659735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659735).length < 2 ^ (prefixWord ++ tailWord_3659735).sum := by decide
  have hdescent : baseEnd_3659735 < baseStart_3659735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659740 : List Nat := [2, 2, 6, 1, 1, 1, 3, 2, 1, 4]
def baseStart_3659740 : Nat := 118140960795 + 3659740 * 2 ^ 59
def prefixEnd_3659740 : Nat := 4983230072969 + 3 ^ 40 * 3659740 * 2
def baseEnd_3659740 : Nat := 626401896828538828039723

theorem tailTrace_3659740 : CollatzResearch.WordTrace tailWord_3659740 prefixEnd_3659740 626401896828538828039723 := by
  unfold tailWord_3659740
  simp only [CollatzResearch.WordTrace]
  refine ⟨66740841880697244337812337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88987789174262992450416449 66740841880697244337812337)
  ·
    refine ⟨50055631410522933253359253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66740841880697244337812337 50055631410522933253359253)
    ·
      refine ⟨2346357722368262496251215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50055631410522933253359253 2346357722368262496251215)
      ·
        refine ⟨3519536583552393744376823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2346357722368262496251215 3519536583552393744376823)
        ·
          refine ⟨5279304875328590616565235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519536583552393744376823 5279304875328590616565235)
          ·
            refine ⟨7918957312992885924847853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279304875328590616565235 7918957312992885924847853)
            ·
              refine ⟨2969608992372332221817945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7918957312992885924847853 2969608992372332221817945)
              ·
                refine ⟨2227206744279249166363459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2969608992372332221817945 2227206744279249166363459)
                ·
                  refine ⟨3340810116418873749545189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227206744279249166363459 3340810116418873749545189)
                  ·
                    refine ⟨626401896828538828039723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3340810116418873749545189 626401896828538828039723)
                    ·
                      rfl

theorem cell23_3659740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_3659740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659740 prefixEnd_3659740 := by exact prefixLift 3659740
  have htrace : WordTrace (prefixWord ++ tailWord_3659740) baseStart_3659740 baseEnd_3659740 := by
    simpa [prefixWord, tailWord_3659740, baseEnd_3659740] using wordTrace_append hprefix tailTrace_3659740
  have hstable : (prefixWord ++ tailWord_3659740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659740).length < 2 ^ (prefixWord ++ tailWord_3659740).sum := by decide
  have hdescent : baseEnd_3659740 < baseStart_3659740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659745 : List Nat := [1, 2, 3, 1, 2, 1, 4, 1, 4, 4]
def baseStart_3659745 : Nat := 118140960795 + 3659745 * 2 ^ 59
def prefixEnd_3659745 : Nat := 4983230072969 + 3 ^ 40 * 3659745 * 2
def baseEnd_3659745 : Nat := 626402752629629654852215

theorem tailTrace_3659745 : CollatzResearch.WordTrace tailWord_3659745 prefixEnd_3659745 626402752629629654852215 := by
  unfold tailWord_3659745
  simp only [CollatzResearch.WordTrace]
  refine ⟨133481866126376374529556689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88987910750917583019704459 133481866126376374529556689)
  ·
    refine ⟨100111399594782280897167517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133481866126376374529556689 100111399594782280897167517)
    ·
      refine ⟨37541774848043355336437819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100111399594782280897167517 37541774848043355336437819)
      ·
        refine ⟨56312662272065033004656729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37541774848043355336437819 56312662272065033004656729)
        ·
          refine ⟨42234496704048774753492547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56312662272065033004656729 42234496704048774753492547)
          ·
            refine ⟨63351745056073162130238821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42234496704048774753492547 63351745056073162130238821)
            ·
              refine ⟨11878452198013717899419779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63351745056073162130238821 11878452198013717899419779)
              ·
                refine ⟨17817678297020576849129669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11878452198013717899419779 17817678297020576849129669)
                ·
                  refine ⟨3340814680691358159211813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17817678297020576849129669 3340814680691358159211813)
                  ·
                    refine ⟨626402752629629654852215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3340814680691358159211813 626402752629629654852215)
                    ·
                      rfl

theorem cell23_3659745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_3659745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659745 prefixEnd_3659745 := by exact prefixLift 3659745
  have htrace : WordTrace (prefixWord ++ tailWord_3659745) baseStart_3659745 baseEnd_3659745 := by
    simpa [prefixWord, tailWord_3659745, baseEnd_3659745] using wordTrace_append hprefix tailTrace_3659745
  have hstable : (prefixWord ++ tailWord_3659745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659745).length < 2 ^ (prefixWord ++ tailWord_3659745).sum := by decide
  have hdescent : baseEnd_3659745 < baseStart_3659745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659748 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3659748 : Nat := 118140960795 + 3659748 * 2 ^ 59
def prefixEnd_3659748 : Nat := 4983230072969 + 3 ^ 40 * 3659748 * 2
def baseEnd_3659748 : Nat := 1879209798330852452819131

theorem tailTrace_3659748 : CollatzResearch.WordTrace tailWord_3659748 prefixEnd_3659748 1879209798330852452819131 := by
  unfold tailWord_3659748
  simp only [CollatzResearch.WordTrace]
  refine ⟨66740987772682753020957949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88987983696910337361277265 66740987772682753020957949)
  ·
    refine ⟨25027870414756032382859231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66740987772682753020957949 25027870414756032382859231)
    ·
      refine ⟨37541805622134048574288847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25027870414756032382859231 37541805622134048574288847)
      ·
        refine ⟨56312708433201072861433271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37541805622134048574288847 56312708433201072861433271)
        ·
          refine ⟨84469062649801609292149907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56312708433201072861433271 84469062649801609292149907)
          ·
            refine ⟨126703593974702413938224861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84469062649801609292149907 126703593974702413938224861)
            ·
              refine ⟨47513847740513405226834323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126703593974702413938224861 47513847740513405226834323)
              ·
                refine ⟨71270771610770107840251485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47513847740513405226834323 71270771610770107840251485)
                ·
                  refine ⟨26726539354038790440094307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71270771610770107840251485 26726539354038790440094307)
                  ·
                    refine ⟨40089809031058185660141461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26726539354038790440094307 40089809031058185660141461)
                    ·
                      refine ⟨1879209798330852452819131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40089809031058185660141461 1879209798330852452819131)
                      ·
                        rfl

theorem cell23_3659748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3659748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659748 prefixEnd_3659748 := by exact prefixLift 3659748
  have htrace : WordTrace (prefixWord ++ tailWord_3659748) baseStart_3659748 baseEnd_3659748 := by
    simpa [prefixWord, tailWord_3659748, baseEnd_3659748] using wordTrace_append hprefix tailTrace_3659748
  have hstable : (prefixWord ++ tailWord_3659748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659748).length < 2 ^ (prefixWord ++ tailWord_3659748).sum := by decide
  have hdescent : baseEnd_3659748 < baseStart_3659748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659766 : List Nat := [5, 1, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_3659766 : Nat := 118140960795 + 3659766 * 2 ^ 59
def prefixEnd_3659766 : Nat := 4983230072969 + 3 ^ 40 * 3659766 * 2
def baseEnd_3659766 : Nat := 626406346994211127464683

theorem tailTrace_3659766 : CollatzResearch.WordTrace tailWord_3659766 prefixEnd_3659766 626406346994211127464683 := by
  unfold tailWord_3659766
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342664503706268444754447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88988421372866863410714101 8342664503706268444754447)
  ·
    refine ⟨12513996755559402667131671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8342664503706268444754447 12513996755559402667131671)
    ·
      refine ⟨18770995133339104000697507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12513996755559402667131671 18770995133339104000697507)
      ·
        refine ⟨28156492700008656001046261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18770995133339104000697507 28156492700008656001046261)
        ·
          refine ⟨2639671190625811500098087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28156492700008656001046261 2639671190625811500098087)
          ·
            refine ⟨3959506785938717250147131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639671190625811500098087 3959506785938717250147131)
            ·
              refine ⟨5939260178908075875220697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959506785938717250147131 5939260178908075875220697)
              ·
                refine ⟨4454445134181056906415523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5939260178908075875220697 4454445134181056906415523)
                ·
                  refine ⟨6681667701271585359623285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454445134181056906415523 6681667701271585359623285)
                  ·
                    refine ⟨626406346994211127464683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6681667701271585359623285 626406346994211127464683)
                    ·
                      rfl

theorem cell23_3659766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_3659766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659766 prefixEnd_3659766 := by exact prefixLift 3659766
  have htrace : WordTrace (prefixWord ++ tailWord_3659766) baseStart_3659766 baseEnd_3659766 := by
    simpa [prefixWord, tailWord_3659766, baseEnd_3659766] using wordTrace_append hprefix tailTrace_3659766
  have hstable : (prefixWord ++ tailWord_3659766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659766).length < 2 ^ (prefixWord ++ tailWord_3659766).sum := by decide
  have hdescent : baseEnd_3659766 < baseStart_3659766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659805 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_3659805 : Nat := 118140960795 + 3659805 * 2 ^ 59
def prefixEnd_3659805 : Nat := 4983230072969 + 3 ^ 40 * 3659805 * 2
def baseEnd_3659805 : Nat := 626413022242719576602123

theorem tailTrace_3659805 : CollatzResearch.WordTrace tailWord_3659805 prefixEnd_3659805 626413022242719576602123 := by
  unfold tailWord_3659805
  simp only [CollatzResearch.WordTrace]
  refine ⟨133484054506159004776740869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88989369670772669851160579 133484054506159004776740869)
  ·
    refine ⟨25028260219904813395638913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133484054506159004776740869 25028260219904813395638913)
    ·
      refine ⟨18771195164928610046729185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25028260219904813395638913 18771195164928610046729185)
      ·
        refine ⟨14078396373696457535046889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18771195164928610046729185 14078396373696457535046889)
        ·
          refine ⟨10558797280272343151285167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14078396373696457535046889 10558797280272343151285167)
          ·
            refine ⟨15838195920408514726927751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10558797280272343151285167 15838195920408514726927751)
            ·
              refine ⟨23757293880612772090391627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15838195920408514726927751 23757293880612772090391627)
              ·
                refine ⟨35635940820919158135587441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23757293880612772090391627 35635940820919158135587441)
                ·
                  refine ⟨26726955615689368601690581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35635940820919158135587441 26726955615689368601690581)
                  ·
                    refine ⟨626413022242719576602123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26726955615689368601690581 626413022242719576602123)
                    ·
                      rfl

theorem cell23_3659805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_3659805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659805 prefixEnd_3659805 := by exact prefixLift 3659805
  have htrace : WordTrace (prefixWord ++ tailWord_3659805) baseStart_3659805 baseEnd_3659805 := by
    simpa [prefixWord, tailWord_3659805, baseEnd_3659805] using wordTrace_append hprefix tailTrace_3659805
  have hstable : (prefixWord ++ tailWord_3659805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659805).length < 2 ^ (prefixWord ++ tailWord_3659805).sum := by decide
  have hdescent : baseEnd_3659805 < baseStart_3659805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659865 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 7]
def baseStart_3659865 : Nat := 118140960795 + 3659865 * 2 ^ 59
def prefixEnd_3659865 : Nat := 4983230072969 + 3 ^ 40 * 3659865 * 2
def baseEnd_3659865 : Nat := 208807763951936499450677

theorem tailTrace_3659865 : CollatzResearch.WordTrace tailWord_3659865 prefixEnd_3659865 208807763951936499450677 := by
  unfold tailWord_3659865
  simp only [CollatzResearch.WordTrace]
  refine ⟨133486242885941635023925049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88990828590627756682616699 133486242885941635023925049)
  ·
    refine ⟨100114682164456226267943787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133486242885941635023925049 100114682164456226267943787)
    ·
      refine ⟨150172023246684339401915681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100114682164456226267943787 150172023246684339401915681)
      ·
        refine ⟨112629017435013254551436761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150172023246684339401915681 112629017435013254551436761)
        ·
          refine ⟨84471763076259940913577571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112629017435013254551436761 84471763076259940913577571)
          ·
            refine ⟨126707644614389911370366357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84471763076259940913577571 126707644614389911370366357)
            ·
              refine ⟨5939420841299527095485923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126707644614389911370366357 5939420841299527095485923)
              ·
                refine ⟨8909131261949290643228885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939420841299527095485923 8909131261949290643228885)
                ·
                  refine ⟨208807763951936499450677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8909131261949290643228885 208807763951936499450677)
                  ·
                    rfl

theorem cell23_3659865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 7].length) (baseStart_3659865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659865 prefixEnd_3659865 := by exact prefixLift 3659865
  have htrace : WordTrace (prefixWord ++ tailWord_3659865) baseStart_3659865 baseEnd_3659865 := by
    simpa [prefixWord, tailWord_3659865, baseEnd_3659865] using wordTrace_append hprefix tailTrace_3659865
  have hstable : (prefixWord ++ tailWord_3659865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659865).length < 2 ^ (prefixWord ++ tailWord_3659865).sum := by decide
  have hdescent : baseEnd_3659865 < baseStart_3659865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659870 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_3659870 : Nat := 118140960795 + 3659870 * 2 ^ 59
def prefixEnd_3659870 : Nat := 4983230072969 + 3 ^ 40 * 3659870 * 2
def baseEnd_3659870 : Nat := 1879272442970700975493571

theorem tailTrace_3659870 : CollatzResearch.WordTrace tailWord_3659870 prefixEnd_3659870 1879272442970700975493571 := by
  unfold tailWord_3659870
  simp only [CollatzResearch.WordTrace]
  refine ⟨16685803156365440109732133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88990950167282347251904709 16685803156365440109732133)
  ·
    refine ⟨3128588091818520020574775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16685803156365440109732133 3128588091818520020574775)
    ·
      refine ⟨4692882137727780030862163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128588091818520020574775 4692882137727780030862163)
      ·
        refine ⟨7039323206591670046293245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692882137727780030862163 7039323206591670046293245)
        ·
          refine ⟨2639746202471876267359967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7039323206591670046293245 2639746202471876267359967)
          ·
            refine ⟨3959619303707814401039951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639746202471876267359967 3959619303707814401039951)
            ·
              refine ⟨5939428955561721601559927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959619303707814401039951 5939428955561721601559927)
              ·
                refine ⟨8909143433342582402339891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939428955561721601559927 8909143433342582402339891)
                ·
                  refine ⟨13363715150013873603509837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8909143433342582402339891 13363715150013873603509837)
                  ·
                    refine ⟨5011393181255202601316189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13363715150013873603509837 5011393181255202601316189)
                    ·
                      refine ⟨1879272442970700975493571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5011393181255202601316189 1879272442970700975493571)
                      ·
                        rfl

theorem cell23_3659870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_3659870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659870 prefixEnd_3659870 := by exact prefixLift 3659870
  have htrace : WordTrace (prefixWord ++ tailWord_3659870) baseStart_3659870 baseEnd_3659870 := by
    simpa [prefixWord, tailWord_3659870, baseEnd_3659870] using wordTrace_append hprefix tailTrace_3659870
  have hstable : (prefixWord ++ tailWord_3659870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659870).length < 2 ^ (prefixWord ++ tailWord_3659870).sum := by decide
  have hdescent : baseEnd_3659870 < baseStart_3659870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659895 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 1, 7]
def baseStart_3659895 : Nat := 118140960795 + 3659895 * 2 ^ 59
def prefixEnd_3659895 : Nat := 4983230072969 + 3 ^ 40 * 3659895 * 2
def baseEnd_3659895 : Nat := 626428426662354459226985

theorem tailTrace_3659895 : CollatzResearch.WordTrace tailWord_3659895 prefixEnd_3659895 626428426662354459226985 := by
  unfold tailWord_3659895
  simp only [CollatzResearch.WordTrace]
  refine ⟨133487337075832950147517139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88991558050555300098344759 133487337075832950147517139)
  ·
    refine ⟨200231005613749425221275709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133487337075832950147517139 200231005613749425221275709)
    ·
      refine ⟨75086627105156034457978391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200231005613749425221275709 75086627105156034457978391)
      ·
        refine ⟨112629940657734051686967587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75086627105156034457978391 112629940657734051686967587)
        ·
          refine ⟨168944910986601077530451381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112629940657734051686967587 168944910986601077530451381)
          ·
            refine ⟨15838585404993851018479817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168944910986601077530451381 15838585404993851018479817)
            ·
              refine ⟨11878939053745388263859863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15838585404993851018479817 11878939053745388263859863)
              ·
                refine ⟨17818408580618082395789795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11878939053745388263859863 17818408580618082395789795)
                ·
                  refine ⟨26727612870927123593684693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17818408580618082395789795 26727612870927123593684693)
                  ·
                    refine ⟨626428426662354459226985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26727612870927123593684693 626428426662354459226985)
                    ·
                      rfl

theorem cell23_3659895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_3659895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659895 prefixEnd_3659895 := by exact prefixLift 3659895
  have htrace : WordTrace (prefixWord ++ tailWord_3659895) baseStart_3659895 baseEnd_3659895 := by
    simpa [prefixWord, tailWord_3659895, baseEnd_3659895] using wordTrace_append hprefix tailTrace_3659895
  have hstable : (prefixWord ++ tailWord_3659895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659895).length < 2 ^ (prefixWord ++ tailWord_3659895).sum := by decide
  have hdescent : baseEnd_3659895 < baseStart_3659895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659912 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 4, 5]
def baseStart_3659912 : Nat := 118140960795 + 3659912 * 2 ^ 59
def prefixEnd_3659912 : Nat := 4983230072969 + 3 ^ 40 * 3659912 * 2
def baseEnd_3659912 : Nat := 626431336386063270389459

theorem tailTrace_3659912 : CollatzResearch.WordTrace tailWord_3659912 prefixEnd_3659912 626431336386063270389459 := by
  unfold tailWord_3659912
  simp only [CollatzResearch.WordTrace]
  refine ⟨66743978558385681025442995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88991971411180908033923993 66743978558385681025442995)
  ·
    refine ⟨100115967837578521538164493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66743978558385681025442995 100115967837578521538164493)
    ·
      refine ⟨37543487939091945576811685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100115967837578521538164493 37543487939091945576811685)
      ·
        refine ⟨7039403988579739795652191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37543487939091945576811685 7039403988579739795652191)
        ·
          refine ⟨10559105982869609693478287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7039403988579739795652191 10559105982869609693478287)
          ·
            refine ⟨15838658974304414540217431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10559105982869609693478287 15838658974304414540217431)
            ·
              refine ⟨23757988461456621810326147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15838658974304414540217431 23757988461456621810326147)
              ·
                refine ⟨35636982692184932715489221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23757988461456621810326147 35636982692184932715489221)
                ·
                  refine ⟨6681934254784674884154229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35636982692184932715489221 6681934254784674884154229)
                  ·
                    refine ⟨626431336386063270389459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6681934254784674884154229 626431336386063270389459)
                    ·
                      rfl

theorem cell23_3659912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_3659912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659912 prefixEnd_3659912 := by exact prefixLift 3659912
  have htrace : WordTrace (prefixWord ++ tailWord_3659912) baseStart_3659912 baseEnd_3659912 := by
    simpa [prefixWord, tailWord_3659912, baseEnd_3659912] using wordTrace_append hprefix tailTrace_3659912
  have hstable : (prefixWord ++ tailWord_3659912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659912).length < 2 ^ (prefixWord ++ tailWord_3659912).sum := by decide
  have hdescent : baseEnd_3659912 < baseStart_3659912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659922 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3659922 : Nat := 118140960795 + 3659922 * 2 ^ 59
def prefixEnd_3659922 : Nat := 4983230072969 + 3 ^ 40 * 3659922 * 2
def baseEnd_3659922 : Nat := 1879299143964734772043331

theorem tailTrace_3659922 : CollatzResearch.WordTrace tailWord_3659922 prefixEnd_3659922 1879299143964734772043331 := by
  unfold tailWord_3659922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33372080461683783439687505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88992214564490089172500013 33372080461683783439687505)
  ·
    refine ⟨25029060346262837579765629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33372080461683783439687505 25029060346262837579765629)
    ·
      refine ⟨9385897629848564092412111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25029060346262837579765629 9385897629848564092412111)
      ·
        refine ⟨14078846444772846138618167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9385897629848564092412111 14078846444772846138618167)
        ·
          refine ⟨21118269667159269207927251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14078846444772846138618167 21118269667159269207927251)
          ·
            refine ⟨31677404500738903811890877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21118269667159269207927251 31677404500738903811890877)
            ·
              refine ⟨11879026687777088929459079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31677404500738903811890877 11879026687777088929459079)
              ·
                refine ⟨17818540031665633394188619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11879026687777088929459079 17818540031665633394188619)
                ·
                  refine ⟨26727810047498450091282929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17818540031665633394188619 26727810047498450091282929)
                  ·
                    refine ⟨20045857535623837568462197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26727810047498450091282929 20045857535623837568462197)
                    ·
                      refine ⟨1879299143964734772043331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20045857535623837568462197 1879299143964734772043331)
                      ·
                        rfl

theorem cell23_3659922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3659922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659922 prefixEnd_3659922 := by exact prefixLift 3659922
  have htrace : WordTrace (prefixWord ++ tailWord_3659922) baseStart_3659922 baseEnd_3659922 := by
    simpa [prefixWord, tailWord_3659922, baseEnd_3659922] using wordTrace_append hprefix tailTrace_3659922
  have hstable : (prefixWord ++ tailWord_3659922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659922).length < 2 ^ (prefixWord ++ tailWord_3659922).sum := by decide
  have hdescent : baseEnd_3659922 < baseStart_3659922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659932 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3659932 : Nat := 118140960795 + 3659932 * 2 ^ 59
def prefixEnd_3659932 : Nat := 4983230072969 + 3 ^ 40 * 3659932 * 2
def baseEnd_3659932 : Nat := 1879304278771279732918285

theorem tailTrace_3659932 : CollatzResearch.WordTrace tailWord_3659932 prefixEnd_3659932 1879304278771279732918285 := by
  unfold tailWord_3659932
  simp only [CollatzResearch.WordTrace]
  refine ⟨66744343288349452733307025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88992457717799270311076033 66744343288349452733307025)
  ·
    refine ⟨50058257466262089549980269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66744343288349452733307025 50058257466262089549980269)
    ·
      refine ⟨18771846549848283581242601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50058257466262089549980269 18771846549848283581242601)
      ·
        refine ⟨14078884912386212685931951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18771846549848283581242601 14078884912386212685931951)
        ·
          refine ⟨21118327368579319028897927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14078884912386212685931951 21118327368579319028897927)
          ·
            refine ⟨31677491052868978543346891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21118327368579319028897927 31677491052868978543346891)
            ·
              refine ⟨47516236579303467815020337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31677491052868978543346891 47516236579303467815020337)
              ·
                refine ⟨35637177434477600861265253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47516236579303467815020337 35637177434477600861265253)
                ·
                  refine ⟨6681970768964550161487235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35637177434477600861265253 6681970768964550161487235)
                  ·
                    refine ⟨10022956153446825242230853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6681970768964550161487235 10022956153446825242230853)
                    ·
                      refine ⟨1879304278771279732918285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10022956153446825242230853 1879304278771279732918285)
                      ·
                        rfl

theorem cell23_3659932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3659932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659932 prefixEnd_3659932 := by exact prefixLift 3659932
  have htrace : WordTrace (prefixWord ++ tailWord_3659932) baseStart_3659932 baseEnd_3659932 := by
    simpa [prefixWord, tailWord_3659932, baseEnd_3659932] using wordTrace_append hprefix tailTrace_3659932
  have hstable : (prefixWord ++ tailWord_3659932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659932).length < 2 ^ (prefixWord ++ tailWord_3659932).sum := by decide
  have hdescent : baseEnd_3659932 < baseStart_3659932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659946 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 2, 5]
def baseStart_3659946 : Nat := 118140960795 + 3659946 * 2 ^ 59
def prefixEnd_3659946 : Nat := 4983230072969 + 3 ^ 40 * 3659946 * 2
def baseEnd_3659946 : Nat := 626437155833480892714407

theorem tailTrace_3659946 : CollatzResearch.WordTrace tailWord_3659946 prefixEnd_3659946 626437155833480892714407 := by
  unfold tailWord_3659946
  simp only [CollatzResearch.WordTrace]
  refine ⟨33372299299662046464405923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88992798132432123905082461 33372299299662046464405923)
  ·
    refine ⟨50058448949493069696608885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33372299299662046464405923 50058448949493069696608885)
    ·
      refine ⟨4692979589014975284057083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50058448949493069696608885 4692979589014975284057083)
      ·
        refine ⟨7039469383522462926085625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692979589014975284057083 7039469383522462926085625)
        ·
          refine ⟨5279602037641847194564219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7039469383522462926085625 5279602037641847194564219)
          ·
            refine ⟨7919403056462770791846329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279602037641847194564219 7919403056462770791846329)
            ·
              refine ⟨5939552292347078093884747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7919403056462770791846329 5939552292347078093884747)
              ·
                refine ⟨8909328438520617140827121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939552292347078093884747 8909328438520617140827121)
                ·
                  refine ⟨6681996328890462855620341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8909328438520617140827121 6681996328890462855620341)
                  ·
                    refine ⟨626437155833480892714407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6681996328890462855620341 626437155833480892714407)
                    ·
                      rfl

theorem cell23_3659946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_3659946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659946 prefixEnd_3659946 := by exact prefixLift 3659946
  have htrace : WordTrace (prefixWord ++ tailWord_3659946) baseStart_3659946 baseEnd_3659946 := by
    simpa [prefixWord, tailWord_3659946, baseEnd_3659946] using wordTrace_append hprefix tailTrace_3659946
  have hstable : (prefixWord ++ tailWord_3659946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659946).length < 2 ^ (prefixWord ++ tailWord_3659946).sum := by decide
  have hdescent : baseEnd_3659946 < baseStart_3659946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659949 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_3659949 : Nat := 118140960795 + 3659949 * 2 ^ 59
def prefixEnd_3659949 : Nat := 4983230072969 + 3 ^ 40 * 3659949 * 2
def baseEnd_3659949 : Nat := 1879313007942406166405707

theorem tailTrace_3659949 : CollatzResearch.WordTrace tailWord_3659949 prefixEnd_3659949 1879313007942406166405707 := by
  unfold tailWord_3659949
  simp only [CollatzResearch.WordTrace]
  refine ⟨133489306617637317369982901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88992871078424878246655267 133489306617637317369982901)
  ·
    refine ⟨12514622495403498503435897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133489306617637317369982901 12514622495403498503435897)
    ·
      refine ⟨9385966871552623877576923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12514622495403498503435897 9385966871552623877576923)
      ·
        refine ⟨14078950307328935816365385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9385966871552623877576923 14078950307328935816365385)
        ·
          refine ⟨10559212730496701862274039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14078950307328935816365385 10559212730496701862274039)
          ·
            refine ⟨15838819095745052793411059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10559212730496701862274039 15838819095745052793411059)
            ·
              refine ⟨23758228643617579190116589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15838819095745052793411059 23758228643617579190116589)
              ·
                refine ⟨8909335741356592196293721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23758228643617579190116589 8909335741356592196293721)
                ·
                  refine ⟨6682001806017444147220291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8909335741356592196293721 6682001806017444147220291)
                  ·
                    refine ⟨10023002709026166220830437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6682001806017444147220291 10023002709026166220830437)
                    ·
                      refine ⟨1879313007942406166405707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10023002709026166220830437 1879313007942406166405707)
                      ·
                        rfl

theorem cell23_3659949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_3659949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3659949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3659949 prefixEnd_3659949 := by exact prefixLift 3659949
  have htrace : WordTrace (prefixWord ++ tailWord_3659949) baseStart_3659949 baseEnd_3659949 := by
    simpa [prefixWord, tailWord_3659949, baseEnd_3659949] using wordTrace_append hprefix tailTrace_3659949
  have hstable : (prefixWord ++ tailWord_3659949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659949).length < 2 ^ (prefixWord ++ tailWord_3659949).sum := by decide
  have hdescent : baseEnd_3659949 < baseStart_3659949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660003 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3660003 : Nat := 118140960795 + 3660003 * 2 ^ 59
def prefixEnd_3660003 : Nat := 4983230072969 + 3 ^ 40 * 3660003 * 2
def baseEnd_3660003 : Nat := 1879340735897748955130459

theorem tailTrace_3660003 : CollatzResearch.WordTrace tailWord_3660003 prefixEnd_3660003 1879340735897748955130459 := by
  unfold tailWord_3660003
  simp only [CollatzResearch.WordTrace]
  refine ⟨133491276159441684592448663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88994184106294456394965775 133491276159441684592448663)
  ·
    refine ⟨200236914239162526888672995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133491276159441684592448663 200236914239162526888672995)
    ·
      refine ⟨300355371358743790333009493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200236914239162526888672995 300355371358743790333009493)
      ·
        refine ⟨3519789508110278792964955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 300355371358743790333009493 3519789508110278792964955)
        ·
          refine ⟨5279684262165418189447433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519789508110278792964955 5279684262165418189447433)
          ·
            refine ⟨3959763196624063642085575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5279684262165418189447433 3959763196624063642085575)
            ·
              refine ⟨5939644794936095463128363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959763196624063642085575 5939644794936095463128363)
              ·
                refine ⟨8909467192404143194692545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939644794936095463128363 8909467192404143194692545)
                ·
                  refine ⟨6682100394303107396019409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8909467192404143194692545 6682100394303107396019409)
                  ·
                    refine ⟨5011575295727330547014557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6682100394303107396019409 5011575295727330547014557)
                    ·
                      refine ⟨1879340735897748955130459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5011575295727330547014557 1879340735897748955130459)
                      ·
                        rfl

theorem cell23_3660003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3660003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3660003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3660003 prefixEnd_3660003 := by exact prefixLift 3660003
  have htrace : WordTrace (prefixWord ++ tailWord_3660003) baseStart_3660003 baseEnd_3660003 := by
    simpa [prefixWord, tailWord_3660003, baseEnd_3660003] using wordTrace_append hprefix tailTrace_3660003
  have hstable : (prefixWord ++ tailWord_3660003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660003).length < 2 ^ (prefixWord ++ tailWord_3660003).sum := by decide
  have hdescent : baseEnd_3660003 < baseStart_3660003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
