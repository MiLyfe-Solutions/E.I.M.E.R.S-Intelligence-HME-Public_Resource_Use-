import V185TrunkScan23Chunk0967

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5730071 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 1, 7]
def baseStart_5730071 : Nat := 118140960795 + 5730071 * 2 ^ 59
def prefixEnd_5730071 : Nat := 4983230072969 + 3 ^ 40 * 5730071 * 2
def baseEnd_5730071 : Nat := 980760202463051934853463

theorem tailTrace_5730071 : CollatzResearch.WordTrace tailWord_5730071 prefixEnd_5730071 980760202463051934853463 := by
  unfold tailWord_5730071
  simp only [CollatzResearch.WordTrace]
  refine ⟨208992858823938860060134067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139328572549292573373422711 208992858823938860060134067)
  ·
    refine ⟨313489288235908290090201101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208992858823938860060134067 313489288235908290090201101)
    ·
      refine ⟨117558483088465608783825413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313489288235908290090201101 117558483088465608783825413)
      ·
        refine ⟨22042215579087301646967265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117558483088465608783825413 22042215579087301646967265)
        ·
          refine ⟨16531661684315476235225449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22042215579087301646967265 16531661684315476235225449)
          ·
            refine ⟨12398746263236607176419087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16531661684315476235225449 12398746263236607176419087)
            ·
              refine ⟨18598119394854910764628631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12398746263236607176419087 18598119394854910764628631)
              ·
                refine ⟨27897179092282366146942947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18598119394854910764628631 27897179092282366146942947)
                ·
                  refine ⟨41845768638423549220414421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27897179092282366146942947 41845768638423549220414421)
                  ·
                    refine ⟨980760202463051934853463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41845768638423549220414421 980760202463051934853463)
                    ·
                      rfl

theorem cell23_5730071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_5730071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730071 prefixEnd_5730071 := by exact prefixLift 5730071
  have htrace : WordTrace (prefixWord ++ tailWord_5730071) baseStart_5730071 baseEnd_5730071 := by
    simpa [prefixWord, tailWord_5730071, baseEnd_5730071] using wordTrace_append hprefix tailTrace_5730071
  have hstable : (prefixWord ++ tailWord_5730071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730071).length < 2 ^ (prefixWord ++ tailWord_5730071).sum := by decide
  have hdescent : baseEnd_5730071 < baseStart_5730071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730108 : List Nat := [2, 2, 2, 2, 1, 1, 4, 1, 2, 4, 2]
def baseStart_5730108 : Nat := 118140960795 + 5730108 * 2 ^ 59
def prefixEnd_5730108 : Nat := 4983230072969 + 3 ^ 40 * 5730108 * 2
def baseEnd_5730108 : Nat := 2942299606173372159797719

theorem tailTrace_5730108 : CollatzResearch.WordTrace tailWord_5730108 prefixEnd_5730108 2942299606173372159797719 := by
  unfold tailWord_5730108
  simp only [CollatzResearch.WordTrace]
  refine ⟨104497104162402407689615489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139329472216536543586153985 104497104162402407689615489)
  ·
    refine ⟨78372828121801805767211617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104497104162402407689615489 78372828121801805767211617)
    ·
      refine ⟨58779621091351354325408713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78372828121801805767211617 58779621091351354325408713)
      ·
        refine ⟨44084715818513515744056535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58779621091351354325408713 44084715818513515744056535)
        ·
          refine ⟨66127073727770273616084803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44084715818513515744056535 66127073727770273616084803)
          ·
            refine ⟨99190610591655410424127205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66127073727770273616084803 99190610591655410424127205)
            ·
              refine ⟨18598239485935389454523851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99190610591655410424127205 18598239485935389454523851)
              ·
                refine ⟨27897359228903084181785777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18598239485935389454523851 27897359228903084181785777)
                ·
                  refine ⟨20923019421677313136339333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27897359228903084181785777 20923019421677313136339333)
                  ·
                    refine ⟨3923066141564496213063625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20923019421677313136339333 3923066141564496213063625)
                    ·
                      refine ⟨2942299606173372159797719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923066141564496213063625 2942299606173372159797719)
                      ·
                        rfl

theorem cell23_5730108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_5730108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730108 prefixEnd_5730108 := by exact prefixLift 5730108
  have htrace : WordTrace (prefixWord ++ tailWord_5730108) baseStart_5730108 baseEnd_5730108 := by
    simpa [prefixWord, tailWord_5730108, baseEnd_5730108] using wordTrace_append hprefix tailTrace_5730108
  have hstable : (prefixWord ++ tailWord_5730108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730108).length < 2 ^ (prefixWord ++ tailWord_5730108).sum := by decide
  have hdescent : baseEnd_5730108 < baseStart_5730108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730152 : List Nat := [2, 1, 4, 2, 1, 1, 5, 2, 1, 4]
def baseStart_5730152 : Nat := 118140960795 + 5730152 * 2 ^ 59
def prefixEnd_5730152 : Nat := 4983230072969 + 3 ^ 40 * 5730152 * 2
def baseEnd_5730152 : Nat := 980774066440723329215839

theorem tailTrace_5730152 : CollatzResearch.WordTrace tailWord_5730152 prefixEnd_5730152 980774066440723329215839 := by
  unfold tailWord_5730152
  simp only [CollatzResearch.WordTrace]
  refine ⟨104497906568322705446916355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139330542091096940595888473 104497906568322705446916355)
  ·
    refine ⟨156746859852484058170374533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104497906568322705446916355 156746859852484058170374533)
    ·
      refine ⟨29390036222340760906945225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156746859852484058170374533 29390036222340760906945225)
      ·
        refine ⟨22042527166755570680208919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29390036222340760906945225 22042527166755570680208919)
        ·
          refine ⟨33063790750133356020313379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22042527166755570680208919 33063790750133356020313379)
          ·
            refine ⟨49595686125200034030470069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33063790750133356020313379 49595686125200034030470069)
            ·
              refine ⟨4649595574237503190356569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49595686125200034030470069 4649595574237503190356569)
              ·
                refine ⟨3487196680678127392767427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4649595574237503190356569 3487196680678127392767427)
                ·
                  refine ⟨5230795021017191089151141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487196680678127392767427 5230795021017191089151141)
                  ·
                    refine ⟨980774066440723329215839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5230795021017191089151141 980774066440723329215839)
                    ·
                      rfl

theorem cell23_5730152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_5730152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730152 prefixEnd_5730152 := by exact prefixLift 5730152
  have htrace : WordTrace (prefixWord ++ tailWord_5730152) baseStart_5730152 baseEnd_5730152 := by
    simpa [prefixWord, tailWord_5730152, baseEnd_5730152] using wordTrace_append hprefix tailTrace_5730152
  have hstable : (prefixWord ++ tailWord_5730152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730152).length < 2 ^ (prefixWord ++ tailWord_5730152).sum := by decide
  have hdescent : baseEnd_5730152 < baseStart_5730152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730161 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 3, 5]
def baseStart_5730161 : Nat := 118140960795 + 5730161 * 2 ^ 59
def prefixEnd_5730161 : Nat := 4983230072969 + 3 ^ 40 * 5730161 * 2
def baseEnd_5730161 : Nat := 980775606882686817478325

theorem tailTrace_5730161 : CollatzResearch.WordTrace tailWord_5730161 prefixEnd_5730161 980775606882686817478325 := by
  unfold tailWord_5730161
  simp only [CollatzResearch.WordTrace]
  refine ⟨208996141393612805430910337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139330760929075203620606891 208996141393612805430910337)
  ·
    refine ⟨156747106045209604073182753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208996141393612805430910337 156747106045209604073182753)
    ·
      refine ⟨117560329533907203054887065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156747106045209604073182753 117560329533907203054887065)
      ·
        refine ⟨88170247150430402291165299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117560329533907203054887065 88170247150430402291165299)
        ·
          refine ⟨132255370725645603436747949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88170247150430402291165299 132255370725645603436747949)
          ·
            refine ⟨49595764022117101288780481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132255370725645603436747949 49595764022117101288780481)
            ·
              refine ⟨37196823016587825966585361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49595764022117101288780481 37196823016587825966585361)
              ·
                refine ⟨27897617262440869474939021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37196823016587825966585361 27897617262440869474939021)
                ·
                  refine ⟨10461606473415326053102133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27897617262440869474939021 10461606473415326053102133)
                  ·
                    refine ⟨980775606882686817478325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10461606473415326053102133 980775606882686817478325)
                    ·
                      rfl

theorem cell23_5730161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_5730161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730161 prefixEnd_5730161 := by exact prefixLift 5730161
  have htrace : WordTrace (prefixWord ++ tailWord_5730161) baseStart_5730161 baseEnd_5730161 := by
    simpa [prefixWord, tailWord_5730161, baseEnd_5730161] using wordTrace_append hprefix tailTrace_5730161
  have hstable : (prefixWord ++ tailWord_5730161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730161).length < 2 ^ (prefixWord ++ tailWord_5730161).sum := by decide
  have hdescent : baseEnd_5730161 < baseStart_5730161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730185 : List Nat := [1, 2, 1, 1, 5, 1, 4, 1, 2, 3, 2]
def baseStart_5730185 : Nat := 118140960795 + 5730185 * 2 ^ 59
def prefixEnd_5730185 : Nat := 4983230072969 + 3 ^ 40 * 5730185 * 2
def baseEnd_5730185 : Nat := 2942339144183768358534865

theorem tailTrace_5730185 : CollatzResearch.WordTrace tailWord_5730185 prefixEnd_5730185 2942339144183768358534865 := by
  unfold tailWord_5730185
  simp only [CollatzResearch.WordTrace]
  refine ⟨208997016745525857529784009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139331344497017238353189339 208997016745525857529784009)
  ·
    refine ⟨156747762559144393147338007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208997016745525857529784009 156747762559144393147338007)
    ·
      refine ⟨235121643838716589721007011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156747762559144393147338007 235121643838716589721007011)
      ·
        refine ⟨352682465758074884581510517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235121643838716589721007011 352682465758074884581510517)
        ·
          refine ⟨33063981164819520429516611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 352682465758074884581510517 33063981164819520429516611)
          ·
            refine ⟨49595971747229280644274917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33063981164819520429516611 49595971747229280644274917)
            ·
              refine ⟨9299244702605490120801547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49595971747229280644274917 9299244702605490120801547)
              ·
                refine ⟨13948867053908235181202321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9299244702605490120801547 13948867053908235181202321)
                ·
                  refine ⟨10461650290431176385901741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13948867053908235181202321 10461650290431176385901741)
                  ·
                    refine ⟨3923118858911691144713153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10461650290431176385901741 3923118858911691144713153)
                    ·
                      refine ⟨2942339144183768358534865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923118858911691144713153 2942339144183768358534865)
                      ·
                        rfl

theorem cell23_5730185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 1, 2, 3, 2].length) (baseStart_5730185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730185 prefixEnd_5730185 := by exact prefixLift 5730185
  have htrace : WordTrace (prefixWord ++ tailWord_5730185) baseStart_5730185 baseEnd_5730185 := by
    simpa [prefixWord, tailWord_5730185, baseEnd_5730185] using wordTrace_append hprefix tailTrace_5730185
  have hstable : (prefixWord ++ tailWord_5730185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730185).length < 2 ^ (prefixWord ++ tailWord_5730185).sum := by decide
  have hdescent : baseEnd_5730185 < baseStart_5730185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730209 : List Nat := [1, 2, 3, 4, 2, 1, 1, 4, 1, 1, 3]
def baseStart_5730209 : Nat := 118140960795 + 5730209 * 2 ^ 59
def prefixEnd_5730209 : Nat := 4983230072969 + 3 ^ 40 * 5730209 * 2
def baseEnd_5730209 : Nat := 2942351467719476264634755

theorem tailTrace_5730209 : CollatzResearch.WordTrace tailWord_5730209 prefixEnd_5730209 2942351467719476264634755 := by
  unfold tailWord_5730209
  simp only [CollatzResearch.WordTrace]
  refine ⟨208997892097438909628657681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139331928064959273085771787 208997892097438909628657681)
  ·
    refine ⟨156748419073079182221493261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208997892097438909628657681 156748419073079182221493261)
    ·
      refine ⟨58780657152404693333059973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156748419073079182221493261 58780657152404693333059973)
      ·
        refine ⟨11021373216075879999948745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58780657152404693333059973 11021373216075879999948745)
        ·
          refine ⟨8266029912056909999961559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11021373216075879999948745 8266029912056909999961559)
          ·
            refine ⟨12399044868085364999942339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8266029912056909999961559 12399044868085364999942339)
            ·
              refine ⟨18598567302128047499913509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12399044868085364999942339 18598567302128047499913509)
              ·
                refine ⟨3487231369149008906233783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18598567302128047499913509 3487231369149008906233783)
                ·
                  refine ⟨5230847053723513359350675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487231369149008906233783 5230847053723513359350675)
                  ·
                    refine ⟨7846270580585270039026013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5230847053723513359350675 7846270580585270039026013)
                    ·
                      refine ⟨2942351467719476264634755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7846270580585270039026013 2942351467719476264634755)
                      ·
                        rfl

theorem cell23_5730209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_5730209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730209 prefixEnd_5730209 := by exact prefixLift 5730209
  have htrace : WordTrace (prefixWord ++ tailWord_5730209) baseStart_5730209 baseEnd_5730209 := by
    simpa [prefixWord, tailWord_5730209, baseEnd_5730209] using wordTrace_append hprefix tailTrace_5730209
  have hstable : (prefixWord ++ tailWord_5730209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730209).length < 2 ^ (prefixWord ++ tailWord_5730209).sum := by decide
  have hdescent : baseEnd_5730209 < baseStart_5730209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730211 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 4]
def baseStart_5730211 : Nat := 118140960795 + 5730211 * 2 ^ 59
def prefixEnd_5730211 : Nat := 4983230072969 + 3 ^ 40 * 5730211 * 2
def baseEnd_5730211 : Nat := 2942352494680785256809745

theorem tailTrace_5730211 : CollatzResearch.WordTrace tailWord_5730211 prefixEnd_5730211 2942352494680785256809745 := by
  unfold tailWord_5730211
  simp only [CollatzResearch.WordTrace]
  refine ⟨208997965043431663970230487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139331976695621109313486991 208997965043431663970230487)
  ·
    refine ⟨313496947565147495955345731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208997965043431663970230487 313496947565147495955345731)
    ·
      refine ⟨470245421347721243933018597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313496947565147495955345731 470245421347721243933018597)
      ·
        refine ⟨88171016502697733237440987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 470245421347721243933018597 88171016502697733237440987)
        ·
          refine ⟨132256524754046599856161481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88171016502697733237440987 132256524754046599856161481)
          ·
            refine ⟨99192393565534949892121111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132256524754046599856161481 99192393565534949892121111)
            ·
              refine ⟨148788590348302424838181667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99192393565534949892121111 148788590348302424838181667)
              ·
                refine ⟨223182885522453637257272501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148788590348302424838181667 223182885522453637257272501)
                ·
                  refine ⟨20923395517730028492869297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223182885522453637257272501 20923395517730028492869297)
                  ·
                    refine ⟨15692546638297521369651973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20923395517730028492869297 15692546638297521369651973)
                    ·
                      refine ⟨2942352494680785256809745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15692546638297521369651973 2942352494680785256809745)
                      ·
                        rfl

theorem cell23_5730211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_5730211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730211 prefixEnd_5730211 := by exact prefixLift 5730211
  have htrace : WordTrace (prefixWord ++ tailWord_5730211) baseStart_5730211 baseEnd_5730211 := by
    simpa [prefixWord, tailWord_5730211, baseEnd_5730211] using wordTrace_append hprefix tailTrace_5730211
  have hstable : (prefixWord ++ tailWord_5730211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730211).length < 2 ^ (prefixWord ++ tailWord_5730211).sum := by decide
  have hdescent : baseEnd_5730211 < baseStart_5730211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730225 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 2, 4]
def baseStart_5730225 : Nat := 118140960795 + 5730225 * 2 ^ 59
def prefixEnd_5730225 : Nat := 4983230072969 + 3 ^ 40 * 5730225 * 2
def baseEnd_5730225 : Nat := 980786561136649400678227

theorem tailTrace_5730225 : CollatzResearch.WordTrace tailWord_5730225 prefixEnd_5730225 980786561136649400678227 := by
  unfold tailWord_5730225
  simp only [CollatzResearch.WordTrace]
  refine ⟨208998475665380944361240129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139332317110253962907493419 208998475665380944361240129)
  ·
    refine ⟨156748856749035708270930097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 208998475665380944361240129 156748856749035708270930097)
    ·
      refine ⟨117561642561776781203197573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156748856749035708270930097 117561642561776781203197573)
      ·
        refine ⟨22042807980333146475599545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117561642561776781203197573 22042807980333146475599545)
        ·
          refine ⟨16532105985249859856699659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22042807980333146475599545 16532105985249859856699659)
          ·
            refine ⟨24798158977874789785049489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16532105985249859856699659 24798158977874789785049489)
            ·
              refine ⟨18598619233406092338787117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24798158977874789785049489 18598619233406092338787117)
              ·
                refine ⟨6974482212527284627045169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18598619233406092338787117 6974482212527284627045169)
                ·
                  refine ⟨5230861659395463470283877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6974482212527284627045169 5230861659395463470283877)
                  ·
                    refine ⟨980786561136649400678227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5230861659395463470283877 980786561136649400678227)
                    ·
                      rfl

theorem cell23_5730225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_5730225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730225 prefixEnd_5730225 := by exact prefixLift 5730225
  have htrace : WordTrace (prefixWord ++ tailWord_5730225) baseStart_5730225 baseEnd_5730225 := by
    simpa [prefixWord, tailWord_5730225, baseEnd_5730225] using wordTrace_append hprefix tailTrace_5730225
  have hstable : (prefixWord ++ tailWord_5730225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730225).length < 2 ^ (prefixWord ++ tailWord_5730225).sum := by decide
  have hdescent : baseEnd_5730225 < baseStart_5730225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730236 : List Nat := [2, 2, 2, 5, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5730236 : Nat := 118140960795 + 5730236 * 2 ^ 59
def prefixEnd_5730236 : Nat := 4983230072969 + 3 ^ 40 * 5730236 * 2
def baseEnd_5730236 : Nat := 2942365331697147658997131

theorem tailTrace_5730236 : CollatzResearch.WordTrace tailWord_5730236 prefixEnd_5730236 2942365331697147658997131 := by
  unfold tailWord_5730236
  simp only [CollatzResearch.WordTrace]
  refine ⟨104499438434170546619945281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139332584578894062159927041 104499438434170546619945281)
  ·
    refine ⟨78374578825627909964958961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104499438434170546619945281 78374578825627909964958961)
    ·
      refine ⟨58780934119220932473719221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78374578825627909964958961 58780934119220932473719221)
      ·
        refine ⟨5510712573676962419411177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58780934119220932473719221 5510712573676962419411177)
        ·
          refine ⟨4133034430257721814558383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5510712573676962419411177 4133034430257721814558383)
          ·
            refine ⟨6199551645386582721837575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4133034430257721814558383 6199551645386582721837575)
            ·
              refine ⟨9299327468079874082756363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6199551645386582721837575 9299327468079874082756363)
              ·
                refine ⟨13948991202119811124134545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9299327468079874082756363 13948991202119811124134545)
                ·
                  refine ⟨10461743401589858343100909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13948991202119811124134545 10461743401589858343100909)
                  ·
                    refine ⟨3923153775596196878662841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10461743401589858343100909 3923153775596196878662841)
                    ·
                      refine ⟨2942365331697147658997131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923153775596196878662841 2942365331697147658997131)
                      ·
                        rfl

theorem cell23_5730236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5730236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730236 prefixEnd_5730236 := by exact prefixLift 5730236
  have htrace : WordTrace (prefixWord ++ tailWord_5730236) baseStart_5730236 baseEnd_5730236 := by
    simpa [prefixWord, tailWord_5730236, baseEnd_5730236] using wordTrace_append hprefix tailTrace_5730236
  have hstable : (prefixWord ++ tailWord_5730236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730236).length < 2 ^ (prefixWord ++ tailWord_5730236).sum := by decide
  have hdescent : baseEnd_5730236 < baseStart_5730236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730252 : List Nat := [2, 2, 1, 4, 1, 2, 4, 1, 1, 2, 3]
def baseStart_5730252 : Nat := 118140960795 + 5730252 * 2 ^ 59
def prefixEnd_5730252 : Nat := 4983230072969 + 3 ^ 40 * 5730252 * 2
def baseEnd_5730252 : Nat := 2942373547387619596397057

theorem tailTrace_5730252 : CollatzResearch.WordTrace tailWord_5730252 prefixEnd_5730252 2942373547387619596397057 := by
  unfold tailWord_5730252
  simp only [CollatzResearch.WordTrace]
  refine ⟨104499730218141563986236505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139332973624188751981648673 104499730218141563986236505)
  ·
    refine ⟨78374797663606172989677379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104499730218141563986236505 78374797663606172989677379)
    ·
      refine ⟨117562196495409259484516069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78374797663606172989677379 117562196495409259484516069)
      ·
        refine ⟨22042911842889236153346763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117562196495409259484516069 22042911842889236153346763)
        ·
          refine ⟨33064367764333854230020145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22042911842889236153346763 33064367764333854230020145)
          ·
            refine ⟨24798275823250390672515109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33064367764333854230020145 24798275823250390672515109)
            ·
              refine ⟨4649676716859448251096583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24798275823250390672515109 4649676716859448251096583)
              ·
                refine ⟨6974515075289172376644875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649676716859448251096583 6974515075289172376644875)
                ·
                  refine ⟨10461772612933758564967313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6974515075289172376644875 10461772612933758564967313)
                  ·
                    refine ⟨7846329459700318923725485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10461772612933758564967313 7846329459700318923725485)
                    ·
                      refine ⟨2942373547387619596397057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7846329459700318923725485 2942373547387619596397057)
                      ·
                        rfl

theorem cell23_5730252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_5730252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730252 prefixEnd_5730252 := by exact prefixLift 5730252
  have htrace : WordTrace (prefixWord ++ tailWord_5730252) baseStart_5730252 baseEnd_5730252 := by
    simpa [prefixWord, tailWord_5730252, baseEnd_5730252] using wordTrace_append hprefix tailTrace_5730252
  have hstable : (prefixWord ++ tailWord_5730252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730252).length < 2 ^ (prefixWord ++ tailWord_5730252).sum := by decide
  have hdescent : baseEnd_5730252 < baseStart_5730252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730291 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 5]
def baseStart_5730291 : Nat := 118140960795 + 5730291 * 2 ^ 59
def prefixEnd_5730291 : Nat := 4983230072969 + 3 ^ 40 * 5730291 * 2
def baseEnd_5730291 : Nat := 2942393573133144943809377

theorem tailTrace_5730291 : CollatzResearch.WordTrace tailWord_5730291 prefixEnd_5730291 2942393573133144943809377 := by
  unfold tailWord_5730291
  simp only [CollatzResearch.WordTrace]
  refine ⟨209000882883141837633142727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139333921922094558422095151 209000882883141837633142727)
  ·
    refine ⟨313501324324712756449714091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209000882883141837633142727 313501324324712756449714091)
    ·
      refine ⟨470251986487069134674571137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313501324324712756449714091 470251986487069134674571137)
      ·
        refine ⟨352688989865301851005928353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470251986487069134674571137 352688989865301851005928353)
        ·
          refine ⟨264516742398976388254446265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352688989865301851005928353 264516742398976388254446265)
          ·
            refine ⟨198387556799232291190834699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264516742398976388254446265 198387556799232291190834699)
            ·
              refine ⟨297581335198848436786252049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198387556799232291190834699 297581335198848436786252049)
              ·
                refine ⟨223186001399136327589689037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297581335198848436786252049 223186001399136327589689037)
                ·
                  refine ⟨83694750524676122846133389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223186001399136327589689037 83694750524676122846133389)
                  ·
                    refine ⟨31385531446753546067300021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83694750524676122846133389 31385531446753546067300021)
                    ·
                      refine ⟨2942393573133144943809377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31385531446753546067300021 2942393573133144943809377)
                      ·
                        rfl

theorem cell23_5730291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_5730291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730291 prefixEnd_5730291 := by exact prefixLift 5730291
  have htrace : WordTrace (prefixWord ++ tailWord_5730291) baseStart_5730291 baseEnd_5730291 := by
    simpa [prefixWord, tailWord_5730291, baseEnd_5730291] using wordTrace_append hprefix tailTrace_5730291
  have hstable : (prefixWord ++ tailWord_5730291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730291).length < 2 ^ (prefixWord ++ tailWord_5730291).sum := by decide
  have hdescent : baseEnd_5730291 < baseStart_5730291 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730305 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 3, 4, 2]
def baseStart_5730305 : Nat := 118140960795 + 5730305 * 2 ^ 59
def prefixEnd_5730305 : Nat := 4983230072969 + 3 ^ 40 * 5730305 * 2
def baseEnd_5730305 : Nat := 2942400761862307889034313

theorem tailTrace_5730305 : CollatzResearch.WordTrace tailWord_5730305 prefixEnd_5730305 2942400761862307889034313 := by
  unfold tailWord_5730305
  simp only [CollatzResearch.WordTrace]
  refine ⟨209001393505091118024152369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139334262336727412016101579 209001393505091118024152369)
  ·
    refine ⟨156751045128818338518114277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209001393505091118024152369 156751045128818338518114277)
    ·
      refine ⟨29390820961653438472146427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156751045128818338518114277 29390820961653438472146427)
      ·
        refine ⟨44086231442480157708219641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29390820961653438472146427 44086231442480157708219641)
        ·
          refine ⟨33064673581860118281164731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44086231442480157708219641 33064673581860118281164731)
          ·
            refine ⟨49597010372790177421747097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33064673581860118281164731 49597010372790177421747097)
            ·
              refine ⟨37197757779592633066310323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49597010372790177421747097 37197757779592633066310323)
              ·
                refine ⟨55796636669388949599465485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37197757779592633066310323 55796636669388949599465485)
                ·
                  refine ⟨20923738751020856099799557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55796636669388949599465485 20923738751020856099799557)
                  ·
                    refine ⟨3923201015816410518712417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20923738751020856099799557 3923201015816410518712417)
                    ·
                      refine ⟨2942400761862307889034313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923201015816410518712417 2942400761862307889034313)
                      ·
                        rfl

theorem cell23_5730305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_5730305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730305 prefixEnd_5730305 := by exact prefixLift 5730305
  have htrace : WordTrace (prefixWord ++ tailWord_5730305) baseStart_5730305 baseEnd_5730305 := by
    simpa [prefixWord, tailWord_5730305, baseEnd_5730305] using wordTrace_append hprefix tailTrace_5730305
  have hstable : (prefixWord ++ tailWord_5730305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730305).length < 2 ^ (prefixWord ++ tailWord_5730305).sum := by decide
  have hdescent : baseEnd_5730305 < baseStart_5730305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730317 : List Nat := [1, 7, 1, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5730317 : Nat := 118140960795 + 5730317 * 2 ^ 59
def prefixEnd_5730317 : Nat := 4983230072969 + 3 ^ 40 * 5730317 * 2
def baseEnd_5730317 : Nat := 2942406923630161842084259

theorem tailTrace_5730317 : CollatzResearch.WordTrace tailWord_5730317 prefixEnd_5730317 2942406923630161842084259 := by
  unfold tailWord_5730317
  simp only [CollatzResearch.WordTrace]
  refine ⟨209001831181047644073589205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139334554120698429382392803 209001831181047644073589205)
  ·
    refine ⟨4898480418305804157974747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 209001831181047644073589205 4898480418305804157974747)
    ·
      refine ⟨7347720627458706236962121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4898480418305804157974747 7347720627458706236962121)
      ·
        refine ⟨5510790470594029677721591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7347720627458706236962121 5510790470594029677721591)
        ·
          refine ⟨8266185705891044516582387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5510790470594029677721591 8266185705891044516582387)
          ·
            refine ⟨12399278558836566774873581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8266185705891044516582387 12399278558836566774873581)
            ·
              refine ⟨4649729459563712540577593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12399278558836566774873581 4649729459563712540577593)
              ·
                refine ⟨3487297094672784405433195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4649729459563712540577593 3487297094672784405433195)
                ·
                  refine ⟨5230945642009176608149793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487297094672784405433195 5230945642009176608149793)
                  ·
                    refine ⟨3923209231506882456112345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5230945642009176608149793 3923209231506882456112345)
                    ·
                      refine ⟨2942406923630161842084259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923209231506882456112345 2942406923630161842084259)
                      ·
                        rfl

theorem cell23_5730317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5730317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730317 prefixEnd_5730317 := by exact prefixLift 5730317
  have htrace : WordTrace (prefixWord ++ tailWord_5730317) baseStart_5730317 baseEnd_5730317 := by
    simpa [prefixWord, tailWord_5730317, baseEnd_5730317] using wordTrace_append hprefix tailTrace_5730317
  have hstable : (prefixWord ++ tailWord_5730317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730317).length < 2 ^ (prefixWord ++ tailWord_5730317).sum := by decide
  have hdescent : baseEnd_5730317 < baseStart_5730317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730331 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 8]
def baseStart_5730331 : Nat := 118140960795 + 5730331 * 2 ^ 59
def prefixEnd_5730331 : Nat := 4983230072969 + 3 ^ 40 * 5730331 * 2
def baseEnd_5730331 : Nat := 2942414112359324787309193

theorem tailTrace_5730331 : CollatzResearch.WordTrace tailWord_5730331 prefixEnd_5730331 2942414112359324787309193 := by
  unfold tailWord_5730331
  simp only [CollatzResearch.WordTrace]
  refine ⟨209002341802996924464598847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139334894535331282976399231 209002341802996924464598847)
  ·
    refine ⟨313503512704495386696898271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209002341802996924464598847 313503512704495386696898271)
    ·
      refine ⟨470255269056743080045347407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313503512704495386696898271 470255269056743080045347407)
      ·
        refine ⟨705382903585114620068021111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470255269056743080045347407 705382903585114620068021111)
        ·
          refine ⟨1058074355377671930102031667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705382903585114620068021111 1058074355377671930102031667)
          ·
            refine ⟨1587111533066507895153047501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058074355377671930102031667 1587111533066507895153047501)
            ·
              refine ⟨595166824899940460682392813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1587111533066507895153047501 595166824899940460682392813)
              ·
                refine ⟨223187559337477672755897305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 595166824899940460682392813 223187559337477672755897305)
                ·
                  refine ⟨167390669503108254566922979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223187559337477672755897305 167390669503108254566922979)
                  ·
                    refine ⟨251086004254662381850384469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167390669503108254566922979 251086004254662381850384469)
                    ·
                      refine ⟨2942414112359324787309193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 251086004254662381850384469 2942414112359324787309193)
                      ·
                        rfl

theorem cell23_5730331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_5730331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730331 prefixEnd_5730331 := by exact prefixLift 5730331
  have htrace : WordTrace (prefixWord ++ tailWord_5730331) baseStart_5730331 baseEnd_5730331 := by
    simpa [prefixWord, tailWord_5730331, baseEnd_5730331] using wordTrace_append hprefix tailTrace_5730331
  have hstable : (prefixWord ++ tailWord_5730331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730331).length < 2 ^ (prefixWord ++ tailWord_5730331).sum := by decide
  have hdescent : baseEnd_5730331 < baseStart_5730331 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730343 : List Nat := [1, 1, 7, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_5730343 : Nat := 118140960795 + 5730343 * 2 ^ 59
def prefixEnd_5730343 : Nat := 4983230072969 + 3 ^ 40 * 5730343 * 2
def baseEnd_5730343 : Nat := 2942420274127178740359139

theorem tailTrace_5730343 : CollatzResearch.WordTrace tailWord_5730343 prefixEnd_5730343 2942420274127178740359139 := by
  unfold tailWord_5730343
  simp only [CollatzResearch.WordTrace]
  refine ⟨209002779478953450514035683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139335186319302300342690455 209002779478953450514035683)
  ·
    refine ⟨313504169218430175771053525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209002779478953450514035683 313504169218430175771053525)
    ·
      refine ⟨7347753966056957244634067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 313504169218430175771053525 7347753966056957244634067)
      ·
        refine ⟨11021630949085435866951101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7347753966056957244634067 11021630949085435866951101)
        ·
          refine ⟨4133111605907038450106663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11021630949085435866951101 4133111605907038450106663)
          ·
            refine ⟨6199667408860557675159995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4133111605907038450106663 6199667408860557675159995)
            ·
              refine ⟨9299501113290836512739993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6199667408860557675159995 9299501113290836512739993)
              ·
                refine ⟨6974625834968127384554995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9299501113290836512739993 6974625834968127384554995)
                ·
                  refine ⟨10461938752452191076832493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6974625834968127384554995 10461938752452191076832493)
                  ·
                    refine ⟨3923227032169571653812185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10461938752452191076832493 3923227032169571653812185)
                    ·
                      refine ⟨2942420274127178740359139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923227032169571653812185 2942420274127178740359139)
                      ·
                        rfl

theorem cell23_5730343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_5730343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730343 prefixEnd_5730343 := by exact prefixLift 5730343
  have htrace : WordTrace (prefixWord ++ tailWord_5730343) baseStart_5730343 baseEnd_5730343 := by
    simpa [prefixWord, tailWord_5730343, baseEnd_5730343] using wordTrace_append hprefix tailTrace_5730343
  have hstable : (prefixWord ++ tailWord_5730343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730343).length < 2 ^ (prefixWord ++ tailWord_5730343).sum := by decide
  have hdescent : baseEnd_5730343 < baseStart_5730343 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730368 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 5]
def baseStart_5730368 : Nat := 118140960795 + 5730368 * 2 ^ 59
def prefixEnd_5730368 : Nat := 4983230072969 + 3 ^ 40 * 5730368 * 2
def baseEnd_5730368 : Nat := 2942433111143541142546523

theorem tailTrace_5730368 : CollatzResearch.WordTrace tailWord_5730368 prefixEnd_5730368 2942433111143541142546523 := by
  unfold tailWord_5730368
  simp only [CollatzResearch.WordTrace]
  refine ⟨104501845651931439891847879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139335794202575253189130505 104501845651931439891847879)
  ·
    refine ⟨156752768477897159837771819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104501845651931439891847879 156752768477897159837771819)
    ·
      refine ⟨235129152716845739756657729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156752768477897159837771819 235129152716845739756657729)
      ·
        refine ⟨176346864537634304817493297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235129152716845739756657729 176346864537634304817493297)
        ·
          refine ⟨132260148403225728613119973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176346864537634304817493297 132260148403225728613119973)
          ·
            refine ⟨24798777825604824114959995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132260148403225728613119973 24798777825604824114959995)
            ·
              refine ⟨37198166738407236172439993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24798777825604824114959995 37198166738407236172439993)
              ·
                refine ⟨27898625053805427129329995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37198166738407236172439993 27898625053805427129329995)
                ·
                  refine ⟨41847937580708140693994993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27898625053805427129329995 41847937580708140693994993)
                  ·
                    refine ⟨31385953185531105520496245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41847937580708140693994993 31385953185531105520496245)
                    ·
                      refine ⟨2942433111143541142546523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31385953185531105520496245 2942433111143541142546523)
                      ·
                        rfl

theorem cell23_5730368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_5730368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730368 prefixEnd_5730368 := by exact prefixLift 5730368
  have htrace : WordTrace (prefixWord ++ tailWord_5730368) baseStart_5730368 baseEnd_5730368 := by
    simpa [prefixWord, tailWord_5730368, baseEnd_5730368] using wordTrace_append hprefix tailTrace_5730368
  have hstable : (prefixWord ++ tailWord_5730368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730368).length < 2 ^ (prefixWord ++ tailWord_5730368).sum := by decide
  have hdescent : baseEnd_5730368 < baseStart_5730368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730378 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_5730378 : Nat := 118140960795 + 5730378 * 2 ^ 59
def prefixEnd_5730378 : Nat := 4983230072969 + 3 ^ 40 * 5730378 * 2
def baseEnd_5730378 : Nat := 2942438245950086103421477

theorem tailTrace_5730378 : CollatzResearch.WordTrace tailWord_5730378 prefixEnd_5730378 2942438245950086103421477 := by
  unfold tailWord_5730378
  simp only [CollatzResearch.WordTrace]
  refine ⟨52251014008456662872889947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139336037355884434327706525 52251014008456662872889947)
  ·
    refine ⟨78376521012684994309334921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52251014008456662872889947 78376521012684994309334921)
    ·
      refine ⟨58782390759513745732001191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78376521012684994309334921 58782390759513745732001191)
      ·
        refine ⟨88173586139270618598001787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58782390759513745732001191 88173586139270618598001787)
        ·
          refine ⟨132260379208905927897002681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88173586139270618598001787 132260379208905927897002681)
          ·
            refine ⟨99195284406679445922752011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132260379208905927897002681 99195284406679445922752011)
            ·
              refine ⟨148792926610019168884128017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99195284406679445922752011 148792926610019168884128017)
              ·
                refine ⟨111594694957514376663096013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148792926610019168884128017 111594694957514376663096013)
                ·
                  refine ⟨41848010609067891248661005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111594694957514376663096013 41848010609067891248661005)
                  ·
                    refine ⟨15693003978400459218247877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41848010609067891248661005 15693003978400459218247877)
                    ·
                      refine ⟨2942438245950086103421477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15693003978400459218247877 2942438245950086103421477)
                      ·
                        rfl

theorem cell23_5730378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_5730378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730378 prefixEnd_5730378 := by exact prefixLift 5730378
  have htrace : WordTrace (prefixWord ++ tailWord_5730378) baseStart_5730378 baseEnd_5730378 := by
    simpa [prefixWord, tailWord_5730378, baseEnd_5730378] using wordTrace_append hprefix tailTrace_5730378
  have hstable : (prefixWord ++ tailWord_5730378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730378).length < 2 ^ (prefixWord ++ tailWord_5730378).sum := by decide
  have hdescent : baseEnd_5730378 < baseStart_5730378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730388 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_5730388 : Nat := 118140960795 + 5730388 * 2 ^ 59
def prefixEnd_5730388 : Nat := 4983230072969 + 3 ^ 40 * 5730388 * 2
def baseEnd_5730388 : Nat := 980814460252210354765477

theorem tailTrace_5730388 : CollatzResearch.WordTrace tailWord_5730388 prefixEnd_5730388 980814460252210354765477 := by
  unfold tailWord_5730388
  simp only [CollatzResearch.WordTrace]
  refine ⟨104502210381895211599711909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139336280509193615466282545 104502210381895211599711909)
  ·
    refine ⟨19594164446605352174945983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104502210381895211599711909 19594164446605352174945983)
    ·
      refine ⟨29391246669908028262418975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19594164446605352174945983 29391246669908028262418975)
      ·
        refine ⟨44086870004862042393628463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29391246669908028262418975 44086870004862042393628463)
        ·
          refine ⟨66130305007293063590442695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44086870004862042393628463 66130305007293063590442695)
          ·
            refine ⟨99195457510939595385664043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66130305007293063590442695 99195457510939595385664043)
            ·
              refine ⟨148793186266409393078496065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99195457510939595385664043 148793186266409393078496065)
              ·
                refine ⟨111594889699807044808872049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148793186266409393078496065 111594889699807044808872049)
                ·
                  refine ⟨83696167274855283606654037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111594889699807044808872049 83696167274855283606654037)
                  ·
                    refine ⟨980814460252210354765477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83696167274855283606654037 980814460252210354765477)
                    ·
                      rfl

theorem cell23_5730388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_5730388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730388 prefixEnd_5730388 := by exact prefixLift 5730388
  have htrace : WordTrace (prefixWord ++ tailWord_5730388) baseStart_5730388 baseEnd_5730388 := by
    simpa [prefixWord, tailWord_5730388, baseEnd_5730388] using wordTrace_append hprefix tailTrace_5730388
  have hstable : (prefixWord ++ tailWord_5730388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730388).length < 2 ^ (prefixWord ++ tailWord_5730388).sum := by decide
  have hdescent : baseEnd_5730388 < baseStart_5730388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730405 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 5, 4]
def baseStart_5730405 : Nat := 118140960795 + 5730405 * 2 ^ 59
def prefixEnd_5730405 : Nat := 4983230072969 + 3 ^ 40 * 5730405 * 2
def baseEnd_5730405 : Nat := 980817369975919165927951

theorem tailTrace_5730405 : CollatzResearch.WordTrace tailWord_5730405 prefixEnd_5730405 980817369975919165927951 := by
  unfold tailWord_5730405
  simp only [CollatzResearch.WordTrace]
  refine ⟨209005040804728835102792669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139336693869819223401861779 209005040804728835102792669)
  ·
    refine ⟨78376890301773313163547251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209005040804728835102792669 78376890301773313163547251)
    ·
      refine ⟨117565335452659969745320877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78376890301773313163547251 117565335452659969745320877)
      ·
        refine ⟨44087000794747488654495329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117565335452659969745320877 44087000794747488654495329)
        ·
          refine ⟨33065250596060616490871497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44087000794747488654495329 33065250596060616490871497)
          ·
            refine ⟨24798937947045462368153623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33065250596060616490871497 24798937947045462368153623)
            ·
              refine ⟨37198406920568193552230435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24798937947045462368153623 37198406920568193552230435)
              ·
                refine ⟨55797610380852290328345653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37198406920568193552230435 55797610380852290328345653)
                ·
                  refine ⟨5231025973204902218282405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55797610380852290328345653 5231025973204902218282405)
                  ·
                    refine ⟨980817369975919165927951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5231025973204902218282405 980817369975919165927951)
                    ·
                      rfl

theorem cell23_5730405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_5730405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730405 prefixEnd_5730405 := by exact prefixLift 5730405
  have htrace : WordTrace (prefixWord ++ tailWord_5730405) baseStart_5730405 baseEnd_5730405 := by
    simpa [prefixWord, tailWord_5730405, baseEnd_5730405] using wordTrace_append hprefix tailTrace_5730405
  have hstable : (prefixWord ++ tailWord_5730405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730405).length < 2 ^ (prefixWord ++ tailWord_5730405).sum := by decide
  have hdescent : baseEnd_5730405 < baseStart_5730405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730412 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 4]
def baseStart_5730412 : Nat := 118140960795 + 5730412 * 2 ^ 59
def prefixEnd_5730412 : Nat := 4983230072969 + 3 ^ 40 * 5730412 * 2
def baseEnd_5730412 : Nat := 2942455704292338970396321

theorem tailTrace_5730412 : CollatzResearch.WordTrace tailWord_5730412 prefixEnd_5730412 2942455704292338970396321 := by
  unfold tailWord_5730412
  simp only [CollatzResearch.WordTrace]
  refine ⟨104502648057851737649148745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139336864077135650198864993 104502648057851737649148745)
  ·
    refine ⟨78376986043388803236861559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104502648057851737649148745 78376986043388803236861559)
    ·
      refine ⟨117565479065083204855292339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78376986043388803236861559 117565479065083204855292339)
      ·
        refine ⟨176348218597624807282938509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117565479065083204855292339 176348218597624807282938509)
        ·
          refine ⟨66130581974109302731101941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176348218597624807282938509 66130581974109302731101941)
          ·
            refine ⟨6199742060072747131040807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66130581974109302731101941 6199742060072747131040807)
            ·
              refine ⟨9299613090109120696561211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6199742060072747131040807 9299613090109120696561211)
              ·
                refine ⟨13949419635163681044841817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9299613090109120696561211 13949419635163681044841817)
                ·
                  refine ⟨10462064726372760783631363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13949419635163681044841817 10462064726372760783631363)
                  ·
                    refine ⟨15693097089559141175447045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10462064726372760783631363 15693097089559141175447045)
                    ·
                      refine ⟨2942455704292338970396321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15693097089559141175447045 2942455704292338970396321)
                      ·
                        rfl

theorem cell23_5730412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_5730412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730412 prefixEnd_5730412 := by exact prefixLift 5730412
  have htrace : WordTrace (prefixWord ++ tailWord_5730412) baseStart_5730412 baseEnd_5730412 := by
    simpa [prefixWord, tailWord_5730412, baseEnd_5730412] using wordTrace_append hprefix tailTrace_5730412
  have hstable : (prefixWord ++ tailWord_5730412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730412).length < 2 ^ (prefixWord ++ tailWord_5730412).sum := by decide
  have hdescent : baseEnd_5730412 < baseStart_5730412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730415 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 3]
def baseStart_5730415 : Nat := 118140960795 + 5730415 * 2 ^ 59
def prefixEnd_5730415 : Nat := 4983230072969 + 3 ^ 40 * 5730415 * 2
def baseEnd_5730415 : Nat := 2942457244734302458658807

theorem tailTrace_5730415 : CollatzResearch.WordTrace tailWord_5730415 prefixEnd_5730415 2942457244734302458658807 := by
  unfold tailWord_5730415
  simp only [CollatzResearch.WordTrace]
  refine ⟨209005405534692606810656699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139336937023128404540437799 209005405534692606810656699)
  ·
    refine ⟨313508108302038910215985049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209005405534692606810656699 313508108302038910215985049)
    ·
      refine ⟨235131081226529182661988787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313508108302038910215985049 235131081226529182661988787)
      ·
        refine ⟨352696621839793773992983181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235131081226529182661988787 352696621839793773992983181)
        ·
          refine ⟨132261233189922665247368693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352696621839793773992983181 132261233189922665247368693)
          ·
            refine ⟨12399490611555249866940815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132261233189922665247368693 12399490611555249866940815)
            ·
              refine ⟨18599235917332874800411223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12399490611555249866940815 18599235917332874800411223)
              ·
                refine ⟨27898853875999312200616835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18599235917332874800411223 27898853875999312200616835)
                ·
                  refine ⟨41848280813998968300925253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27898853875999312200616835 41848280813998968300925253)
                  ·
                    refine ⟨7846552652624806556423485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41848280813998968300925253 7846552652624806556423485)
                    ·
                      refine ⟨2942457244734302458658807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7846552652624806556423485 2942457244734302458658807)
                      ·
                        rfl

theorem cell23_5730415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 3].length) (baseStart_5730415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730415 prefixEnd_5730415 := by exact prefixLift 5730415
  have htrace : WordTrace (prefixWord ++ tailWord_5730415) baseStart_5730415 baseEnd_5730415 := by
    simpa [prefixWord, tailWord_5730415, baseEnd_5730415] using wordTrace_append hprefix tailTrace_5730415
  have hstable : (prefixWord ++ tailWord_5730415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730415).length < 2 ^ (prefixWord ++ tailWord_5730415).sum := by decide
  have hdescent : baseEnd_5730415 < baseStart_5730415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730435 : List Nat := [1, 1, 1, 3, 3, 3, 3, 2, 6]
def baseStart_5730435 : Nat := 118140960795 + 5730435 * 2 ^ 59
def prefixEnd_5730435 : Nat := 4983230072969 + 3 ^ 40 * 5730435 * 2
def baseEnd_5730435 : Nat := 326940834927488042267635

theorem tailTrace_5730435 : CollatzResearch.WordTrace tailWord_5730435 prefixEnd_5730435 326940834927488042267635 := by
  unfold tailWord_5730435
  simp only [CollatzResearch.WordTrace]
  refine ⟨209006134994620150226384759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139337423329746766817589839 209006134994620150226384759)
  ·
    refine ⟨313509202491930225339577139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209006134994620150226384759 313509202491930225339577139)
    ·
      refine ⟨470263803737895338009365709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313509202491930225339577139 470263803737895338009365709)
      ·
        refine ⟨176348926401710751753512141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 470263803737895338009365709 176348926401710751753512141)
        ·
          refine ⟨66130847400641531907567053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176348926401710751753512141 66130847400641531907567053)
          ·
            refine ⟨24799067775240574465337645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66130847400641531907567053 24799067775240574465337645)
            ·
              refine ⟨9299650415715215424501617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24799067775240574465337645 9299650415715215424501617)
              ·
                refine ⟨6974737811786411568376213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9299650415715215424501617 6974737811786411568376213)
                ·
                  refine ⟨326940834927488042267635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6974737811786411568376213 326940834927488042267635)
                  ·
                    rfl

theorem cell23_5730435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 6].length) (baseStart_5730435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730435 prefixEnd_5730435 := by exact prefixLift 5730435
  have htrace : WordTrace (prefixWord ++ tailWord_5730435) baseStart_5730435 baseEnd_5730435 := by
    simpa [prefixWord, tailWord_5730435, baseEnd_5730435] using wordTrace_append hprefix tailTrace_5730435
  have hstable : (prefixWord ++ tailWord_5730435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730435).length < 2 ^ (prefixWord ++ tailWord_5730435).sum := by decide
  have hdescent : baseEnd_5730435 < baseStart_5730435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730539 : List Nat := [1, 1, 1, 1, 2, 5, 5, 1, 1, 2, 3]
def baseStart_5730539 : Nat := 118140960795 + 5730539 * 2 ^ 59
def prefixEnd_5730539 : Nat := 4983230072969 + 3 ^ 40 * 5730539 * 2
def baseEnd_5730539 : Nat := 2942520916335459973508237

theorem tailTrace_5730539 : CollatzResearch.WordTrace tailWord_5730539 prefixEnd_5730539 2942520916335459973508237 := by
  unfold tailWord_5730539
  simp only [CollatzResearch.WordTrace]
  refine ⟨209009928186243375988170671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139339952124162250658780447 209009928186243375988170671)
  ·
    refine ⟨313514892279365063982256007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209009928186243375988170671 313514892279365063982256007)
    ·
      refine ⟨470272338419047595973384011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313514892279365063982256007 470272338419047595973384011)
      ·
        refine ⟨705408507628571393960076017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470272338419047595973384011 705408507628571393960076017)
        ·
          refine ⟨529056380721428545470057013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705408507628571393960076017 529056380721428545470057013)
          ·
            refine ⟨49599035692633926137817845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 529056380721428545470057013 49599035692633926137817845)
            ·
              refine ⟨4649909596184430575420423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49599035692633926137817845 4649909596184430575420423)
              ·
                refine ⟨6974864394276645863130635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649909596184430575420423 6974864394276645863130635)
                ·
                  refine ⟨10462296591414968794695953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6974864394276645863130635 10462296591414968794695953)
                  ·
                    refine ⟨7846722443561226596021965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10462296591414968794695953 7846722443561226596021965)
                    ·
                      refine ⟨2942520916335459973508237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7846722443561226596021965 2942520916335459973508237)
                      ·
                        rfl

theorem cell23_5730539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 1, 1, 2, 3].length) (baseStart_5730539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730539 prefixEnd_5730539 := by exact prefixLift 5730539
  have htrace : WordTrace (prefixWord ++ tailWord_5730539) baseStart_5730539 baseEnd_5730539 := by
    simpa [prefixWord, tailWord_5730539, baseEnd_5730539] using wordTrace_append hprefix tailTrace_5730539
  have hstable : (prefixWord ++ tailWord_5730539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730539).length < 2 ^ (prefixWord ++ tailWord_5730539).sum := by decide
  have hdescent : baseEnd_5730539 < baseStart_5730539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730552 : List Nat := [2, 1, 2, 1, 1, 2, 1, 5, 4, 1, 3]
def baseStart_5730552 : Nat := 118140960795 + 5730552 * 2 ^ 59
def prefixEnd_5730552 : Nat := 4983230072969 + 3 ^ 40 * 5730552 * 2
def baseEnd_5730552 : Nat := 2942527591583968422645677

theorem tailTrace_5730552 : CollatzResearch.WordTrace tailWord_5730552 prefixEnd_5730552 2942527591583968422645677 := by
  unfold tailWord_5730552
  simp only [CollatzResearch.WordTrace]
  refine ⟨104505201167598139604196955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139340268223464186138929273 104505201167598139604196955)
  ·
    refine ⟨156757801751397209406295433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104505201167598139604196955 156757801751397209406295433)
    ·
      refine ⟨117568351313547907054721575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156757801751397209406295433 117568351313547907054721575)
      ·
        refine ⟨176352526970321860582082363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117568351313547907054721575 176352526970321860582082363)
        ·
          refine ⟨264528790455482790873123545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176352526970321860582082363 264528790455482790873123545)
          ·
            refine ⟨198396592841612093154842659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264528790455482790873123545 198396592841612093154842659)
            ·
              refine ⟨297594889262418139732263989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198396592841612093154842659 297594889262418139732263989)
              ·
                refine ⟨27899520868351700599899749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 297594889262418139732263989 27899520868351700599899749)
                ·
                  refine ⟨5231160162815943862481203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27899520868351700599899749 5231160162815943862481203)
                  ·
                    refine ⟨7846740244223915793721805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5231160162815943862481203 7846740244223915793721805)
                    ·
                      refine ⟨2942527591583968422645677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7846740244223915793721805 2942527591583968422645677)
                      ·
                        rfl

theorem cell23_5730552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_5730552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730552 prefixEnd_5730552 := by exact prefixLift 5730552
  have htrace : WordTrace (prefixWord ++ tailWord_5730552) baseStart_5730552 baseEnd_5730552 := by
    simpa [prefixWord, tailWord_5730552, baseEnd_5730552] using wordTrace_append hprefix tailTrace_5730552
  have hstable : (prefixWord ++ tailWord_5730552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730552).length < 2 ^ (prefixWord ++ tailWord_5730552).sum := by decide
  have hdescent : baseEnd_5730552 < baseStart_5730552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730569 : List Nat := [1, 2, 1, 1, 3, 4, 2, 3, 2, 1, 3]
def baseStart_5730569 : Nat := 118140960795 + 5730569 * 2 ^ 59
def prefixEnd_5730569 : Nat := 4983230072969 + 3 ^ 40 * 5730569 * 2
def baseEnd_5730569 : Nat := 2942536320755094856133099

theorem tailTrace_5730569 : CollatzResearch.WordTrace tailWord_5730569 prefixEnd_5730569 2942536320755094856133099 := by
  unfold tailWord_5730569
  simp only [CollatzResearch.WordTrace]
  refine ⟨209011022376134691111762761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139340681584089794074508507 209011022376134691111762761)
  ·
    refine ⟨156758266782101018333822071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209011022376134691111762761 156758266782101018333822071)
    ·
      refine ⟨235137400173151527500733107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156758266782101018333822071 235137400173151527500733107)
      ·
        refine ⟨352706100259727291251099661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235137400173151527500733107 352706100259727291251099661)
        ·
          refine ⟨132264787597397734219162373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352706100259727291251099661 132264787597397734219162373)
          ·
            refine ⟨24799647674512075166092945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132264787597397734219162373 24799647674512075166092945)
            ·
              refine ⟨18599735755884056374569709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24799647674512075166092945 18599735755884056374569709)
              ·
                refine ⟨6974900908456521140463641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18599735755884056374569709 6974900908456521140463641)
                ·
                  refine ⟨5231175681342390855347731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6974900908456521140463641 5231175681342390855347731)
                  ·
                    refine ⟨7846763522013586283021597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5231175681342390855347731 7846763522013586283021597)
                    ·
                      refine ⟨2942536320755094856133099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7846763522013586283021597 2942536320755094856133099)
                      ·
                        rfl

theorem cell23_5730569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 1, 3].length) (baseStart_5730569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730569 prefixEnd_5730569 := by exact prefixLift 5730569
  have htrace : WordTrace (prefixWord ++ tailWord_5730569) baseStart_5730569 baseEnd_5730569 := by
    simpa [prefixWord, tailWord_5730569, baseEnd_5730569] using wordTrace_append hprefix tailTrace_5730569
  have hstable : (prefixWord ++ tailWord_5730569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730569).length < 2 ^ (prefixWord ++ tailWord_5730569).sum := by decide
  have hdescent : baseEnd_5730569 < baseStart_5730569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730590 : List Nat := [4, 3, 2, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_5730590 : Nat := 118140960795 + 5730590 * 2 ^ 59
def prefixEnd_5730590 : Nat := 4983230072969 + 3 ^ 40 * 5730590 * 2
def baseEnd_5730590 : Nat := 2942547103848839273970503

theorem tailTrace_5730590 : CollatzResearch.WordTrace tailWord_5730590 prefixEnd_5730590 2942547103848839273970503 := by
  unfold tailWord_5730590
  simp only [CollatzResearch.WordTrace]
  refine ⟨26126473538632326462284653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139341192206039074465518149 26126473538632326462284653)
  ·
    refine ⟨9797427576987122423356745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26126473538632326462284653 9797427576987122423356745)
    ·
      refine ⟨7348070682740341817517559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9797427576987122423356745 7348070682740341817517559)
      ·
        refine ⟨11022106024110512726276339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7348070682740341817517559 11022106024110512726276339)
        ·
          refine ⟨16533159036165769089414509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11022106024110512726276339 16533159036165769089414509)
          ·
            refine ⟨6199934638562163408530441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16533159036165769089414509 6199934638562163408530441)
            ·
              refine ⟨4649950978921622556397831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6199934638562163408530441 4649950978921622556397831)
              ·
                refine ⟨6974926468382433834596747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4649950978921622556397831 6974926468382433834596747)
                ·
                  refine ⟨10462389702573650751895121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6974926468382433834596747 10462389702573650751895121)
                  ·
                    refine ⟨7846792276930238063921341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10462389702573650751895121 7846792276930238063921341)
                    ·
                      refine ⟨2942547103848839273970503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7846792276930238063921341 2942547103848839273970503)
                      ·
                        rfl

theorem cell23_5730590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_5730590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730590 prefixEnd_5730590 := by exact prefixLift 5730590
  have htrace : WordTrace (prefixWord ++ tailWord_5730590) baseStart_5730590 baseEnd_5730590 := by
    simpa [prefixWord, tailWord_5730590, baseEnd_5730590] using wordTrace_append hprefix tailTrace_5730590
  have hstable : (prefixWord ++ tailWord_5730590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730590).length < 2 ^ (prefixWord ++ tailWord_5730590).sum := by decide
  have hdescent : baseEnd_5730590 < baseStart_5730590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730595 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 5]
def baseStart_5730595 : Nat := 118140960795 + 5730595 * 2 ^ 59
def prefixEnd_5730595 : Nat := 4983230072969 + 3 ^ 40 * 5730595 * 2
def baseEnd_5730595 : Nat := 2942549671252111754407979

theorem tailTrace_5730595 : CollatzResearch.WordTrace tailWord_5730595 prefixEnd_5730595 2942549671252111754407979 := by
  unfold tailWord_5730595
  simp only [CollatzResearch.WordTrace]
  refine ⟨209011970674040497552209239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139341313782693665034806159 209011970674040497552209239)
  ·
    refine ⟨313517956011060746328313859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209011970674040497552209239 313517956011060746328313859)
    ·
      refine ⟨470276934016591119492470789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313517956011060746328313859 470276934016591119492470789)
      ·
        refine ⟨88176925128110834904838273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 470276934016591119492470789 88176925128110834904838273)
        ·
          refine ⟨66132693846083126178628705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88176925128110834904838273 66132693846083126178628705)
          ·
            refine ⟨49599520384562344633971529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66132693846083126178628705 49599520384562344633971529)
            ·
              refine ⟨37199640288421758475478647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49599520384562344633971529 37199640288421758475478647)
              ·
                refine ⟨55799460432632637713217971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37199640288421758475478647 55799460432632637713217971)
                ·
                  refine ⟨83699190648948956569826957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55799460432632637713217971 83699190648948956569826957)
                  ·
                    refine ⟨31387196493355858713685109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83699190648948956569826957 31387196493355858713685109)
                    ·
                      refine ⟨2942549671252111754407979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31387196493355858713685109 2942549671252111754407979)
                      ·
                        rfl

theorem cell23_5730595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_5730595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730595 prefixEnd_5730595 := by exact prefixLift 5730595
  have htrace : WordTrace (prefixWord ++ tailWord_5730595) baseStart_5730595 baseEnd_5730595 := by
    simpa [prefixWord, tailWord_5730595, baseEnd_5730595] using wordTrace_append hprefix tailTrace_5730595
  have hstable : (prefixWord ++ tailWord_5730595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730595).length < 2 ^ (prefixWord ++ tailWord_5730595).sum := by decide
  have hdescent : baseEnd_5730595 < baseStart_5730595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730596 : List Nat := [2, 3, 1, 3, 1, 3, 1, 3, 1, 3, 2]
def baseStart_5730596 : Nat := 118140960795 + 5730596 * 2 ^ 59
def prefixEnd_5730596 : Nat := 4983230072969 + 3 ^ 40 * 5730596 * 2
def baseEnd_5730596 : Nat := 2942550184732766250495475

theorem tailTrace_5730596 : CollatzResearch.WordTrace tailWord_5730596 prefixEnd_5730596 2942550184732766250495475 := by
  unfold tailWord_5730596
  simp only [CollatzResearch.WordTrace]
  refine ⟨104506003573518437361497821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139341338098024583148663761 104506003573518437361497821)
  ·
    refine ⟨39189751340069414010561683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104506003573518437361497821 39189751340069414010561683)
    ·
      refine ⟨58784627010104121015842525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39189751340069414010561683 58784627010104121015842525)
      ·
        refine ⟨22044235128789045380940947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58784627010104121015842525 22044235128789045380940947)
        ·
          refine ⟨33066352693183568071411421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22044235128789045380940947 33066352693183568071411421)
          ·
            refine ⟨12399882259943838026779283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33066352693183568071411421 12399882259943838026779283)
            ·
              refine ⟨18599823389915757040168925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12399882259943838026779283 18599823389915757040168925)
              ·
                refine ⟨6974933771218408890063347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18599823389915757040168925 6974933771218408890063347)
                ·
                  refine ⟨10462400656827613335095021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6974933771218408890063347 10462400656827613335095021)
                  ·
                    refine ⟨3923400246310355000660633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10462400656827613335095021 3923400246310355000660633)
                    ·
                      refine ⟨2942550184732766250495475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923400246310355000660633 2942550184732766250495475)
                      ·
                        rfl

theorem cell23_5730596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_5730596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730596 prefixEnd_5730596 := by exact prefixLift 5730596
  have htrace : WordTrace (prefixWord ++ tailWord_5730596) baseStart_5730596 baseEnd_5730596 := by
    simpa [prefixWord, tailWord_5730596, baseEnd_5730596] using wordTrace_append hprefix tailTrace_5730596
  have hstable : (prefixWord ++ tailWord_5730596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730596).length < 2 ^ (prefixWord ++ tailWord_5730596).sum := by decide
  have hdescent : baseEnd_5730596 < baseStart_5730596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730642 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_5730642 : Nat := 118140960795 + 5730642 * 2 ^ 59
def prefixEnd_5730642 : Nat := 4983230072969 + 3 ^ 40 * 5730642 * 2
def baseEnd_5730642 : Nat := 2942573804842873070520263

theorem tailTrace_5730642 : CollatzResearch.WordTrace tailWord_5730642 prefixEnd_5730642 2942573804842873070520263 := by
  unfold tailWord_5730642
  simp only [CollatzResearch.WordTrace]
  refine ⟨52253421226217556144792545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139342456603246816386113453 52253421226217556144792545)
  ·
    refine ⟨39190065919663167108594409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52253421226217556144792545 39190065919663167108594409)
    ·
      refine ⟨29392549439747375331445807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39190065919663167108594409 29392549439747375331445807)
      ·
        refine ⟨44088824159621062997168711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29392549439747375331445807 44088824159621062997168711)
        ·
          refine ⟨66133236239431594495753067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44088824159621062997168711 66133236239431594495753067)
          ·
            refine ⟨99199854359147391743629601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66133236239431594495753067 99199854359147391743629601)
            ·
              refine ⟨74399890769360543807722201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99199854359147391743629601 74399890769360543807722201)
              ·
                refine ⟨55799918077020407855791651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74399890769360543807722201 55799918077020407855791651)
                ·
                  refine ⟨83699877115530611783687477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55799918077020407855791651 83699877115530611783687477)
                  ·
                    refine ⟨7846863479580994854720701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83699877115530611783687477 7846863479580994854720701)
                    ·
                      refine ⟨2942573804842873070520263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7846863479580994854720701 2942573804842873070520263)
                      ·
                        rfl

theorem cell23_5730642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_5730642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730642 prefixEnd_5730642 := by exact prefixLift 5730642
  have htrace : WordTrace (prefixWord ++ tailWord_5730642) baseStart_5730642 baseEnd_5730642 := by
    simpa [prefixWord, tailWord_5730642, baseEnd_5730642] using wordTrace_append hprefix tailTrace_5730642
  have hstable : (prefixWord ++ tailWord_5730642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730642).length < 2 ^ (prefixWord ++ tailWord_5730642).sum := by decide
  have hdescent : baseEnd_5730642 < baseStart_5730642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730669 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_5730669 : Nat := 118140960795 + 5730669 * 2 ^ 59
def prefixEnd_5730669 : Nat := 4983230072969 + 3 ^ 40 * 5730669 * 2
def baseEnd_5730669 : Nat := 2942587668820544464882639

theorem tailTrace_5730669 : CollatzResearch.WordTrace tailWord_5730669 prefixEnd_5730669 2942587668820544464882639 := by
  unfold tailWord_5730669
  simp only [CollatzResearch.WordTrace]
  refine ⟨209014669675772408190403061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139343113117181605460268707 209014669675772408190403061)
  ·
    refine ⟨19595125282103663267850287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209014669675772408190403061 19595125282103663267850287)
    ·
      refine ⟨29392687923155494901775431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19595125282103663267850287 29392687923155494901775431)
      ·
        refine ⟨44089031884733242352663147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29392687923155494901775431 44089031884733242352663147)
        ·
          refine ⟨66133547827099863528994721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44089031884733242352663147 66133547827099863528994721)
          ·
            refine ⟨49600160870324897646746041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66133547827099863528994721 49600160870324897646746041)
            ·
              refine ⟨37200120652743673235059531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49600160870324897646746041 37200120652743673235059531)
              ·
                refine ⟨55800180979115509852589297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37200120652743673235059531 55800180979115509852589297)
                ·
                  refine ⟨41850135734336632389441973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55800180979115509852589297 41850135734336632389441973)
                  ·
                    refine ⟨3923450225094059286510185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41850135734336632389441973 3923450225094059286510185)
                    ·
                      refine ⟨2942587668820544464882639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923450225094059286510185 2942587668820544464882639)
                      ·
                        rfl

theorem cell23_5730669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_5730669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730669 prefixEnd_5730669 := by exact prefixLift 5730669
  have htrace : WordTrace (prefixWord ++ tailWord_5730669) baseStart_5730669 baseEnd_5730669 := by
    simpa [prefixWord, tailWord_5730669, baseEnd_5730669] using wordTrace_append hprefix tailTrace_5730669
  have hstable : (prefixWord ++ tailWord_5730669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730669).length < 2 ^ (prefixWord ++ tailWord_5730669).sum := by decide
  have hdescent : baseEnd_5730669 < baseStart_5730669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730672 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 5]
def baseStart_5730672 : Nat := 118140960795 + 5730672 * 2 ^ 59
def prefixEnd_5730672 : Nat := 4983230072969 + 3 ^ 40 * 5730672 * 2
def baseEnd_5730672 : Nat := 2942589209262507953145125

theorem tailTrace_5730672 : CollatzResearch.WordTrace tailWord_5730672 prefixEnd_5730672 2942589209262507953145125 := by
  unfold tailWord_5730672
  simp only [CollatzResearch.WordTrace]
  refine ⟨104507389547380769851381135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139343186063174359801841513 104507389547380769851381135)
  ·
    refine ⟨156761084321071154777071703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104507389547380769851381135 156761084321071154777071703)
    ·
      refine ⟨235141626481606732165607555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156761084321071154777071703 235141626481606732165607555)
      ·
        refine ⟨352712439722410098248411333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235141626481606732165607555 352712439722410098248411333)
        ·
          refine ⟨66133582447951893421577125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 352712439722410098248411333 66133582447951893421577125)
          ·
            refine ⟨12400046708990980016545711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66133582447951893421577125 12400046708990980016545711)
            ·
              refine ⟨18600070063486470024818567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12400046708990980016545711 18600070063486470024818567)
              ·
                refine ⟨27900105095229705037227851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18600070063486470024818567 27900105095229705037227851)
                ·
                  refine ⟨41850157642844557555841777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27900105095229705037227851 41850157642844557555841777)
                  ·
                    refine ⟨31387618232133418166881333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41850157642844557555841777 31387618232133418166881333)
                    ·
                      refine ⟨2942589209262507953145125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31387618232133418166881333 2942589209262507953145125)
                      ·
                        rfl

theorem cell23_5730672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 5].length) (baseStart_5730672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730672 prefixEnd_5730672 := by exact prefixLift 5730672
  have htrace : WordTrace (prefixWord ++ tailWord_5730672) baseStart_5730672 baseEnd_5730672 := by
    simpa [prefixWord, tailWord_5730672, baseEnd_5730672] using wordTrace_append hprefix tailTrace_5730672
  have hstable : (prefixWord ++ tailWord_5730672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730672).length < 2 ^ (prefixWord ++ tailWord_5730672).sum := by decide
  have hdescent : baseEnd_5730672 < baseStart_5730672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730699 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 4]
def baseStart_5730699 : Nat := 118140960795 + 5730699 * 2 ^ 59
def prefixEnd_5730699 : Nat := 4983230072969 + 3 ^ 40 * 5730699 * 2
def baseEnd_5730699 : Nat := 2942603073240179347507501

theorem tailTrace_5730699 : CollatzResearch.WordTrace tailWord_5730699 prefixEnd_5730699 2942603073240179347507501 := by
  unfold tailWord_5730699
  simp only [CollatzResearch.WordTrace]
  refine ⟨209015763865663723313995151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139343842577109148875996767 209015763865663723313995151)
  ·
    refine ⟨313523645798495584970992727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209015763865663723313995151 313523645798495584970992727)
    ·
      refine ⟨470285468697743377456489091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313523645798495584970992727 470285468697743377456489091)
      ·
        refine ⟨705428203046615066184733637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470285468697743377456489091 705428203046615066184733637)
        ·
          refine ⟨132267788071240324909637557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 705428203046615066184733637 132267788071240324909637557)
          ·
            refine ⟨12400105131678780460278521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132267788071240324909637557 12400105131678780460278521)
            ·
              refine ⟨9300078848759085345208891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12400105131678780460278521 9300078848759085345208891)
              ·
                refine ⟨13950118273138628017813337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9300078848759085345208891 13950118273138628017813337)
                ·
                  refine ⟨10462588704853971013360003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13950118273138628017813337 10462588704853971013360003)
                  ·
                    refine ⟨15693883057280956520040005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10462588704853971013360003 15693883057280956520040005)
                    ·
                      refine ⟨2942603073240179347507501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15693883057280956520040005 2942603073240179347507501)
                      ·
                        rfl

theorem cell23_5730699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 4].length) (baseStart_5730699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730699 prefixEnd_5730699 := by exact prefixLift 5730699
  have htrace : WordTrace (prefixWord ++ tailWord_5730699) baseStart_5730699 baseEnd_5730699 := by
    simpa [prefixWord, tailWord_5730699, baseEnd_5730699] using wordTrace_append hprefix tailTrace_5730699
  have hstable : (prefixWord ++ tailWord_5730699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730699).length < 2 ^ (prefixWord ++ tailWord_5730699).sum := by decide
  have hdescent : baseEnd_5730699 < baseStart_5730699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730719 : List Nat := [1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 3]
def baseStart_5730719 : Nat := 118140960795 + 5730719 * 2 ^ 59
def prefixEnd_5730719 : Nat := 4983230072969 + 3 ^ 40 * 5730719 * 2
def baseEnd_5730719 : Nat := 2942613342853269269257409

theorem tailTrace_5730719 : CollatzResearch.WordTrace tailWord_5730719 prefixEnd_5730719 2942613342853269269257409 := by
  unfold tailWord_5730719
  simp only [CollatzResearch.WordTrace]
  refine ⟨209016493325591266729723211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139344328883727511153148807 209016493325591266729723211)
  ·
    refine ⟨313524739988386900094584817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209016493325591266729723211 313524739988386900094584817)
    ·
      refine ⟨235143554991290175070938613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313524739988386900094584817 235143554991290175070938613)
      ·
        refine ⟨22044708280433453912900495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235143554991290175070938613 22044708280433453912900495)
        ·
          refine ⟨33067062420650180869350743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22044708280433453912900495 33067062420650180869350743)
          ·
            refine ⟨49600593630975271304026115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33067062420650180869350743 49600593630975271304026115)
            ·
              refine ⟨74400890446462906956039173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49600593630975271304026115 74400890446462906956039173)
              ·
                refine ⟨13950166958711795054257345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74400890446462906956039173 13950166958711795054257345)
                ·
                  refine ⟨10462625219033846290693009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13950166958711795054257345 10462625219033846290693009)
                  ·
                    refine ⟨7846968914275384718019757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10462625219033846290693009 7846968914275384718019757)
                    ·
                      refine ⟨2942613342853269269257409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7846968914275384718019757 2942613342853269269257409)
                      ·
                        rfl

theorem cell23_5730719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_5730719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730719 prefixEnd_5730719 := by exact prefixLift 5730719
  have htrace : WordTrace (prefixWord ++ tailWord_5730719) baseStart_5730719 baseEnd_5730719 := by
    simpa [prefixWord, tailWord_5730719, baseEnd_5730719] using wordTrace_append hprefix tailTrace_5730719
  have hstable : (prefixWord ++ tailWord_5730719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730719).length < 2 ^ (prefixWord ++ tailWord_5730719).sum := by decide
  have hdescent : baseEnd_5730719 < baseStart_5730719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730732 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 3]
def baseStart_5730732 : Nat := 118140960795 + 5730732 * 2 ^ 59
def prefixEnd_5730732 : Nat := 4983230072969 + 3 ^ 40 * 5730732 * 2
def baseEnd_5730732 : Nat := 2942620018101777718394849

theorem tailTrace_5730732 : CollatzResearch.WordTrace tailWord_5730732 prefixEnd_5730732 2942620018101777718394849 := by
  unfold tailWord_5730732
  simp only [CollatzResearch.WordTrace]
  refine ⟨104508483737272084974973225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139344644983029446633297633 104508483737272084974973225)
  ·
    refine ⟨78381362802954063731229919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104508483737272084974973225 78381362802954063731229919)
    ·
      refine ⟨117572044204431095596844879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78381362802954063731229919 117572044204431095596844879)
      ·
        refine ⟨176358066306646643395267319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117572044204431095596844879 176358066306646643395267319)
        ·
          refine ⟨264537099459969965092900979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176358066306646643395267319 264537099459969965092900979)
          ·
            refine ⟨396805649189954947639351469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264537099459969965092900979 396805649189954947639351469)
            ·
              refine ⟨148802118446233105364756801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396805649189954947639351469 148802118446233105364756801)
              ·
                refine ⟨111601588834674829023567601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148802118446233105364756801 111601588834674829023567601)
                ·
                  refine ⟨83701191626006121767675701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111601588834674829023567601 83701191626006121767675701)
                  ·
                    refine ⟨7846986714938073915719597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83701191626006121767675701 7846986714938073915719597)
                    ·
                      refine ⟨2942620018101777718394849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7846986714938073915719597 2942620018101777718394849)
                      ·
                        rfl

theorem cell23_5730732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_5730732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730732 prefixEnd_5730732 := by exact prefixLift 5730732
  have htrace : WordTrace (prefixWord ++ tailWord_5730732) baseStart_5730732 baseEnd_5730732 := by
    simpa [prefixWord, tailWord_5730732, baseEnd_5730732] using wordTrace_append hprefix tailTrace_5730732
  have hstable : (prefixWord ++ tailWord_5730732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730732).length < 2 ^ (prefixWord ++ tailWord_5730732).sum := by decide
  have hdescent : baseEnd_5730732 < baseStart_5730732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730733 : List Nat := [1, 5, 2, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_5730733 : Nat := 118140960795 + 5730733 * 2 ^ 59
def prefixEnd_5730733 : Nat := 4983230072969 + 3 ^ 40 * 5730733 * 2
def baseEnd_5730733 : Nat := 2942620531582432214482345

theorem tailTrace_5730733 : CollatzResearch.WordTrace tailWord_5730733 prefixEnd_5730733 2942620531582432214482345 := by
  unfold tailWord_5730733
  simp only [CollatzResearch.WordTrace]
  refine ⟨209017003947540547120732853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139344669298360364747155235 209017003947540547120732853)
  ·
    refine ⟨19595344120081926292568705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209017003947540547120732853 19595344120081926292568705)
    ·
      refine ⟨14696508090061444719426529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19595344120081926292568705 14696508090061444719426529)
      ·
        refine ⟨11022381067546083539569897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14696508090061444719426529 11022381067546083539569897)
        ·
          refine ⟨8266785800659562654677423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11022381067546083539569897 8266785800659562654677423)
          ·
            refine ⟨12400178700989343982016135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8266785800659562654677423 12400178700989343982016135)
            ·
              refine ⟨18600268051484015973024203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12400178700989343982016135 18600268051484015973024203)
              ·
                refine ⟨27900402077226023959536305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18600268051484015973024203 27900402077226023959536305)
                ·
                  refine ⟨20925301557919517969652229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27900402077226023959536305 20925301557919517969652229)
                  ·
                    refine ⟨3923494042109909619309793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20925301557919517969652229 3923494042109909619309793)
                    ·
                      refine ⟨2942620531582432214482345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923494042109909619309793 2942620531582432214482345)
                      ·
                        rfl

theorem cell23_5730733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_5730733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730733 prefixEnd_5730733 := by exact prefixLift 5730733
  have htrace : WordTrace (prefixWord ++ tailWord_5730733) baseStart_5730733 baseEnd_5730733 := by
    simpa [prefixWord, tailWord_5730733, baseEnd_5730733] using wordTrace_append hprefix tailTrace_5730733
  have hstable : (prefixWord ++ tailWord_5730733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730733).length < 2 ^ (prefixWord ++ tailWord_5730733).sum := by decide
  have hdescent : baseEnd_5730733 < baseStart_5730733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730783 : List Nat := [1, 1, 2, 3, 3, 2, 2, 4, 1, 1, 3]
def baseStart_5730783 : Nat := 118140960795 + 5730783 * 2 ^ 59
def prefixEnd_5730783 : Nat := 4983230072969 + 3 ^ 40 * 5730783 * 2
def baseEnd_5730783 : Nat := 2942646205615157018857115

theorem tailTrace_5730783 : CollatzResearch.WordTrace tailWord_5730783 prefixEnd_5730783 2942646205615157018857115 := by
  unfold tailWord_5730783
  simp only [CollatzResearch.WordTrace]
  refine ⟨209018827597359405660053003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139345885064906270440035335 209018827597359405660053003)
  ·
    refine ⟨313528241396039108490079505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209018827597359405660053003 313528241396039108490079505)
    ·
      refine ⟨235146181047029331367559629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313528241396039108490079505 235146181047029331367559629)
      ·
        refine ⟨88179817892635999262834861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235146181047029331367559629 88179817892635999262834861)
        ·
          refine ⟨33067431709738499723563073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88179817892635999262834861 33067431709738499723563073)
          ·
            refine ⟨24800573782303874792672305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33067431709738499723563073 24800573782303874792672305)
            ·
              refine ⟨18600430336727906094504229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24800573782303874792672305 18600430336727906094504229)
              ·
                refine ⟨3487580688136482392719543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18600430336727906094504229 3487580688136482392719543)
                ·
                  refine ⟨5231371032204723589079315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487580688136482392719543 5231371032204723589079315)
                  ·
                    refine ⟨7847056548307085383618973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5231371032204723589079315 7847056548307085383618973)
                    ·
                      refine ⟨2942646205615157018857115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7847056548307085383618973 2942646205615157018857115)
                      ·
                        rfl

theorem cell23_5730783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_5730783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730783 prefixEnd_5730783 := by exact prefixLift 5730783
  have htrace : WordTrace (prefixWord ++ tailWord_5730783) baseStart_5730783 baseEnd_5730783 := by
    simpa [prefixWord, tailWord_5730783, baseEnd_5730783] using wordTrace_append hprefix tailTrace_5730783
  have hstable : (prefixWord ++ tailWord_5730783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730783).length < 2 ^ (prefixWord ++ tailWord_5730783).sum := by decide
  have hdescent : baseEnd_5730783 < baseStart_5730783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730806 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_5730806 : Nat := 118140960795 + 5730806 * 2 ^ 59
def prefixEnd_5730806 : Nat := 4983230072969 + 3 ^ 40 * 5730806 * 2
def baseEnd_5730806 : Nat := 2942658015670210428869509

theorem tailTrace_5730806 : CollatzResearch.WordTrace tailWord_5730806 prefixEnd_5730806 2942658015670210428869509 := by
  unfold tailWord_5730806
  simp only [CollatzResearch.WordTrace]
  refine ⟨13063729154767255036758767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139346444317517387058760181 13063729154767255036758767)
  ·
    refine ⟨19595593732150882555138151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13063729154767255036758767 19595593732150882555138151)
    ·
      refine ⟨29393390598226323832707227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19595593732150882555138151 29393390598226323832707227)
      ·
        refine ⟨44090085897339485749060841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29393390598226323832707227 44090085897339485749060841)
        ·
          refine ⟨33067564423004614311795631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44090085897339485749060841 33067564423004614311795631)
          ·
            refine ⟨49601346634506921467693447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33067564423004614311795631 49601346634506921467693447)
            ·
              refine ⟨74402019951760382201540171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49601346634506921467693447 74402019951760382201540171)
              ·
                refine ⟨111603029927640573302310257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74402019951760382201540171 111603029927640573302310257)
                ·
                  refine ⟨83702272445730429976732693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111603029927640573302310257 83702272445730429976732693)
                  ·
                    refine ⟨3923544020893613905159345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83702272445730429976732693 3923544020893613905159345)
                    ·
                      refine ⟨2942658015670210428869509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923544020893613905159345 2942658015670210428869509)
                      ·
                        rfl

theorem cell23_5730806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_5730806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730806 prefixEnd_5730806 := by exact prefixLift 5730806
  have htrace : WordTrace (prefixWord ++ tailWord_5730806) baseStart_5730806 baseEnd_5730806 := by
    simpa [prefixWord, tailWord_5730806, baseEnd_5730806] using wordTrace_append hprefix tailTrace_5730806
  have hstable : (prefixWord ++ tailWord_5730806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730806).length < 2 ^ (prefixWord ++ tailWord_5730806).sum := by decide
  have hdescent : baseEnd_5730806 < baseStart_5730806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730809 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 3, 2, 3]
def baseStart_5730809 : Nat := 118140960795 + 5730809 * 2 ^ 59
def prefixEnd_5730809 : Nat := 4983230072969 + 3 ^ 40 * 5730809 * 2
def baseEnd_5730809 : Nat := 2942659556112173917131995

theorem tailTrace_5730809 : CollatzResearch.WordTrace tailWord_5730809 prefixEnd_5730809 2942659556112173917131995 := by
  unfold tailWord_5730809
  simp only [CollatzResearch.WordTrace]
  refine ⟨209019775895265212100499481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139346517263510141400332987 209019775895265212100499481)
  ·
    refine ⟨156764831921448909075374611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209019775895265212100499481 156764831921448909075374611)
    ·
      refine ⟨235147247882173363613061917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156764831921448909075374611 235147247882173363613061917)
      ·
        refine ⟨88180217955815011354898219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235147247882173363613061917 88180217955815011354898219)
        ·
          refine ⟨132270326933722517032347329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88180217955815011354898219 132270326933722517032347329)
          ·
            refine ⟨99202745200291887774260497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132270326933722517032347329 99202745200291887774260497)
            ·
              refine ⟨74402058900218915830695373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99202745200291887774260497 74402058900218915830695373)
              ·
                refine ⟨27900772087582093436510765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74402058900218915830695373 27900772087582093436510765)
                ·
                  refine ⟨10462789532843285038691537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27900772087582093436510765 10462789532843285038691537)
                  ·
                    refine ⟨7847092149632463779018653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10462789532843285038691537 7847092149632463779018653)
                    ·
                      refine ⟨2942659556112173917131995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7847092149632463779018653 2942659556112173917131995)
                      ·
                        rfl

theorem cell23_5730809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_5730809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730809 prefixEnd_5730809 := by exact prefixLift 5730809
  have htrace : WordTrace (prefixWord ++ tailWord_5730809) baseStart_5730809 baseEnd_5730809 := by
    simpa [prefixWord, tailWord_5730809, baseEnd_5730809] using wordTrace_append hprefix tailTrace_5730809
  have hstable : (prefixWord ++ tailWord_5730809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730809).length < 2 ^ (prefixWord ++ tailWord_5730809).sum := by decide
  have hdescent : baseEnd_5730809 < baseStart_5730809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730826 : List Nat := [3, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_5730826 : Nat := 118140960795 + 5730826 * 2 ^ 59
def prefixEnd_5730826 : Nat := 4983230072969 + 3 ^ 40 * 5730826 * 2
def baseEnd_5730826 : Nat := 2942668285283300350619417

theorem tailTrace_5730826 : CollatzResearch.WordTrace tailWord_5730826 prefixEnd_5730826 2942668285283300350619417 := by
  unfold tailWord_5730826
  simp only [CollatzResearch.WordTrace]
  refine ⟨52255098984050906000967083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139346930624135749335912221 52255098984050906000967083)
  ·
    refine ⟨78382648476076359001450625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52255098984050906000967083 78382648476076359001450625)
    ·
      refine ⟨58786986357057269251087969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78382648476076359001450625 58786986357057269251087969)
      ·
        refine ⟨44090239767792951938315977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58786986357057269251087969 44090239767792951938315977)
        ·
          refine ⟨33067679825844713953736983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44090239767792951938315977 33067679825844713953736983)
          ·
            refine ⟨49601519738767070930605475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33067679825844713953736983 49601519738767070930605475)
            ·
              refine ⟨74402279608150606395908213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49601519738767070930605475 74402279608150606395908213)
              ·
                refine ⟨6975213713264119349616395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74402279608150606395908213 6975213713264119349616395)
                ·
                  refine ⟨10462820569896179024424593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6975213713264119349616395 10462820569896179024424593)
                  ·
                    refine ⟨7847115427422134268318445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10462820569896179024424593 7847115427422134268318445)
                    ·
                      refine ⟨2942668285283300350619417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7847115427422134268318445 2942668285283300350619417)
                      ·
                        rfl

theorem cell23_5730826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_5730826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730826 prefixEnd_5730826 := by exact prefixLift 5730826
  have htrace : WordTrace (prefixWord ++ tailWord_5730826) baseStart_5730826 baseEnd_5730826 := by
    simpa [prefixWord, tailWord_5730826, baseEnd_5730826] using wordTrace_append hprefix tailTrace_5730826
  have hstable : (prefixWord ++ tailWord_5730826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730826).length < 2 ^ (prefixWord ++ tailWord_5730826).sum := by decide
  have hdescent : baseEnd_5730826 < baseStart_5730826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730836 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 1, 1, 6]
def baseStart_5730836 : Nat := 118140960795 + 5730836 * 2 ^ 59
def prefixEnd_5730836 : Nat := 4983230072969 + 3 ^ 40 * 5730836 * 2
def baseEnd_5730836 : Nat := 2942673420089845311494371

theorem tailTrace_5730836 : CollatzResearch.WordTrace tailWord_5730836 prefixEnd_5730836 2942673420089845311494371 := by
  unfold tailWord_5730836
  simp only [CollatzResearch.WordTrace]
  refine ⟨104510380333083697855866181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139347173777444930474488241 104510380333083697855866181)
  ·
    refine ⟨19595696312453193347974909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104510380333083697855866181 19595696312453193347974909)
    ·
      refine ⟨7348386117169947505490591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19595696312453193347974909 7348386117169947505490591)
      ·
        refine ⟨11022579175754921258235887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7348386117169947505490591 11022579175754921258235887)
        ·
          refine ⟨16533868763632381887353831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11022579175754921258235887 16533868763632381887353831)
          ·
            refine ⟨24800803145448572831030747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16533868763632381887353831 24800803145448572831030747)
            ·
              refine ⟨37201204718172859246546121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24800803145448572831030747 37201204718172859246546121)
              ·
                refine ⟨27900903538629644434909591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37201204718172859246546121 27900903538629644434909591)
                ·
                  refine ⟨41851355307944466652364387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27900903538629644434909591 41851355307944466652364387)
                  ·
                    refine ⟨62777032961916699978546581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41851355307944466652364387 62777032961916699978546581)
                    ·
                      refine ⟨2942673420089845311494371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62777032961916699978546581 2942673420089845311494371)
                      ·
                        rfl

theorem cell23_5730836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_5730836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730836 prefixEnd_5730836 := by exact prefixLift 5730836
  have htrace : WordTrace (prefixWord ++ tailWord_5730836) baseStart_5730836 baseEnd_5730836 := by
    simpa [prefixWord, tailWord_5730836, baseEnd_5730836] using wordTrace_append hprefix tailTrace_5730836
  have hstable : (prefixWord ++ tailWord_5730836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730836).length < 2 ^ (prefixWord ++ tailWord_5730836).sum := by decide
  have hdescent : baseEnd_5730836 < baseStart_5730836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730840 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 3, 2, 2]
def baseStart_5730840 : Nat := 118140960795 + 5730840 * 2 ^ 59
def prefixEnd_5730840 : Nat := 4983230072969 + 3 ^ 40 * 5730840 * 2
def baseEnd_5730840 : Nat := 2942675474012463295844353

theorem tailTrace_5730840 : CollatzResearch.WordTrace tailWord_5730840 prefixEnd_5730840 2942675474012463295844353 := by
  unfold tailWord_5730840
  simp only [CollatzResearch.WordTrace]
  refine ⟨104510453279076452197438987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139347271038768602929918649 104510453279076452197438987)
  ·
    refine ⟨156765679918614678296158481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104510453279076452197438987 156765679918614678296158481)
    ·
      refine ⟨117574259938961008722118861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156765679918614678296158481 117574259938961008722118861)
      ·
        refine ⟨44090347477110378270794573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117574259938961008722118861 44090347477110378270794573)
        ·
          refine ⟨16533880303916391851547965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44090347477110378270794573 16533880303916391851547965)
          ·
            refine ⟨6200205113968646944330487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16533880303916391851547965 6200205113968646944330487)
            ·
              refine ⟨9300307670952970416495731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6200205113968646944330487 9300307670952970416495731)
              ·
                refine ⟨13950461506429455624743597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9300307670952970416495731 13950461506429455624743597)
                ·
                  refine ⟨5231423064911045859278849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13950461506429455624743597 5231423064911045859278849)
                  ·
                    refine ⟨3923567298683284394459137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5231423064911045859278849 3923567298683284394459137)
                    ·
                      refine ⟨2942675474012463295844353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923567298683284394459137 2942675474012463295844353)
                      ·
                        rfl

theorem cell23_5730840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_5730840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730840 prefixEnd_5730840 := by exact prefixLift 5730840
  have htrace : WordTrace (prefixWord ++ tailWord_5730840) baseStart_5730840 baseEnd_5730840 := by
    simpa [prefixWord, tailWord_5730840, baseEnd_5730840] using wordTrace_append hprefix tailTrace_5730840
  have hstable : (prefixWord ++ tailWord_5730840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730840).length < 2 ^ (prefixWord ++ tailWord_5730840).sum := by decide
  have hdescent : baseEnd_5730840 < baseStart_5730840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730913 : List Nat := [1, 2, 3, 1, 1, 5, 2, 1, 1, 4, 2]
def baseStart_5730913 : Nat := 118140960795 + 5730913 * 2 ^ 59
def prefixEnd_5730913 : Nat := 4983230072969 + 3 ^ 40 * 5730913 * 2
def baseEnd_5730913 : Nat := 2942712958100241510231517

theorem tailTrace_5730913 : CollatzResearch.WordTrace tailWord_5730913 prefixEnd_5730913 2942712958100241510231517 := by
  unfold tailWord_5730913
  simp only [CollatzResearch.WordTrace]
  refine ⟨209023569086888437862285393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139349046057925625241523595 209023569086888437862285393)
  ·
    refine ⟨156767676815166328396714045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209023569086888437862285393 156767676815166328396714045)
    ·
      refine ⟨58787878805687373148767767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156767676815166328396714045 58787878805687373148767767)
      ·
        refine ⟨88181818208531059723151651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58787878805687373148767767 88181818208531059723151651)
        ·
          refine ⟨132272727312796589584727477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88181818208531059723151651 132272727312796589584727477)
          ·
            refine ⟨12400568185574680273568201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 132272727312796589584727477 12400568185574680273568201)
            ·
              refine ⟨9300426139181010205176151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12400568185574680273568201 9300426139181010205176151)
              ·
                refine ⟨13950639208771515307764227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9300426139181010205176151 13950639208771515307764227)
                ·
                  refine ⟨20925958813157272961646341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13950639208771515307764227 20925958813157272961646341)
                  ·
                    refine ⟨3923617277466988680308689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20925958813157272961646341 3923617277466988680308689)
                    ·
                      refine ⟨2942712958100241510231517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923617277466988680308689 2942712958100241510231517)
                      ·
                        rfl

theorem cell23_5730913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_5730913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730913 prefixEnd_5730913 := by exact prefixLift 5730913
  have htrace : WordTrace (prefixWord ++ tailWord_5730913) baseStart_5730913 baseEnd_5730913 := by
    simpa [prefixWord, tailWord_5730913, baseEnd_5730913] using wordTrace_append hprefix tailTrace_5730913
  have hstable : (prefixWord ++ tailWord_5730913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730913).length < 2 ^ (prefixWord ++ tailWord_5730913).sum := by decide
  have hdescent : baseEnd_5730913 < baseStart_5730913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730934 : List Nat := [5, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_5730934 : Nat := 118140960795 + 5730934 * 2 ^ 59
def prefixEnd_5730934 : Nat := 4983230072969 + 3 ^ 40 * 5730934 * 2
def baseEnd_5730934 : Nat := 2942723741193985928068921

theorem tailTrace_5730934 : CollatzResearch.WordTrace tailWord_5730934 prefixEnd_5730934 2942723741193985928068921 := by
  unfold tailWord_5730934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13064020938738272403049991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139349556679874905632533237 13064020938738272403049991)
  ·
    refine ⟨19596031408107408604574987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13064020938738272403049991 19596031408107408604574987)
    ·
      refine ⟨29394047112161112906862481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19596031408107408604574987 29394047112161112906862481)
      ·
        refine ⟨22045535334120834680146861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29394047112161112906862481 22045535334120834680146861)
        ·
          refine ⟨8267075750295313005055073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22045535334120834680146861 8267075750295313005055073)
          ·
            refine ⟨6200306812721484753791305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8267075750295313005055073 6200306812721484753791305)
            ·
              refine ⟨4650230109541113565343479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6200306812721484753791305 4650230109541113565343479)
              ·
                refine ⟨6975345164311670348015219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650230109541113565343479 6975345164311670348015219)
                ·
                  refine ⟨10463017746467505522022829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6975345164311670348015219 10463017746467505522022829)
                  ·
                    refine ⟨3923631654925314570758561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10463017746467505522022829 3923631654925314570758561)
                    ·
                      refine ⟨2942723741193985928068921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923631654925314570758561 2942723741193985928068921)
                      ·
                        rfl

theorem cell23_5730934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_5730934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730934 prefixEnd_5730934 := by exact prefixLift 5730934
  have htrace : WordTrace (prefixWord ++ tailWord_5730934) baseStart_5730934 baseEnd_5730934 := by
    simpa [prefixWord, tailWord_5730934, baseEnd_5730934] using wordTrace_append hprefix tailTrace_5730934
  have hstable : (prefixWord ++ tailWord_5730934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730934).length < 2 ^ (prefixWord ++ tailWord_5730934).sum := by decide
  have hdescent : baseEnd_5730934 < baseStart_5730934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730956 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 2, 5, 2]
def baseStart_5730956 : Nat := 118140960795 + 5730956 * 2 ^ 59
def prefixEnd_5730956 : Nat := 4983230072969 + 3 ^ 40 * 5730956 * 2
def baseEnd_5730956 : Nat := 2942735037768384841993819

theorem tailTrace_5730956 : CollatzResearch.WordTrace tailWord_5730956 prefixEnd_5730956 2942735037768384841993819 := by
  unfold tailWord_5730956
  simp only [CollatzResearch.WordTrace]
  refine ⟨104512568712866328103050361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139350091617155104137400481 104512568712866328103050361)
  ·
    refine ⟨78384426534649746077287771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104512568712866328103050361 78384426534649746077287771)
    ·
      refine ⟨117576639801974619115931657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78384426534649746077287771 117576639801974619115931657)
      ·
        refine ⟨88182479851480964336948743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117576639801974619115931657 88182479851480964336948743)
        ·
          refine ⟨132273719777221446505423115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88182479851480964336948743 132273719777221446505423115)
          ·
            refine ⟨198410579665832169758134673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132273719777221446505423115 198410579665832169758134673)
            ·
              refine ⟨148807934749374127318601005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198410579665832169758134673 148807934749374127318601005)
              ·
                refine ⟨55802975531015297744475377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148807934749374127318601005 55802975531015297744475377)
                ·
                  refine ⟨41852231648261473308356533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55802975531015297744475377 41852231648261473308356533)
                  ·
                    refine ⟨3923646717024513122658425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41852231648261473308356533 3923646717024513122658425)
                    ·
                      refine ⟨2942735037768384841993819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923646717024513122658425 2942735037768384841993819)
                      ·
                        rfl

theorem cell23_5730956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_5730956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730956 prefixEnd_5730956 := by exact prefixLift 5730956
  have htrace : WordTrace (prefixWord ++ tailWord_5730956) baseStart_5730956 baseEnd_5730956 := by
    simpa [prefixWord, tailWord_5730956, baseEnd_5730956] using wordTrace_append hprefix tailTrace_5730956
  have hstable : (prefixWord ++ tailWord_5730956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730956).length < 2 ^ (prefixWord ++ tailWord_5730956).sum := by decide
  have hdescent : baseEnd_5730956 < baseStart_5730956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730964 : List Nat := [2, 4, 2, 2, 1, 2, 3, 1, 2, 2, 2]
def baseStart_5730964 : Nat := 118140960795 + 5730964 * 2 ^ 59
def prefixEnd_5730964 : Nat := 4983230072969 + 3 ^ 40 * 5730964 * 2
def baseEnd_5730964 : Nat := 2942739145613620810693783

theorem tailTrace_5730964 : CollatzResearch.WordTrace tailWord_5730964 prefixEnd_5730964 2942739145613620810693783 := by
  unfold tailWord_5730964
  simp only [CollatzResearch.WordTrace]
  refine ⟨104512714604851836786195973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139350286139802449048261297 104512714604851836786195973)
  ·
    refine ⟨19596133988409719397411745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104512714604851836786195973 19596133988409719397411745)
    ·
      refine ⟨14697100491307289548058809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19596133988409719397411745 14697100491307289548058809)
      ·
        refine ⟨11022825368480467161044107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14697100491307289548058809 11022825368480467161044107)
        ·
          refine ⟨16534238052720700741566161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11022825368480467161044107 16534238052720700741566161)
          ·
            refine ⟨12400678539540525556174621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16534238052720700741566161 12400678539540525556174621)
            ·
              refine ⟨4650254452327697083565483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12400678539540525556174621 4650254452327697083565483)
              ·
                refine ⟨6975381678491545625348225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650254452327697083565483 6975381678491545625348225)
                ·
                  refine ⟨5231536258868659219011169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6975381678491545625348225 5231536258868659219011169)
                  ·
                    refine ⟨3923652194151494414258377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5231536258868659219011169 3923652194151494414258377)
                    ·
                      refine ⟨2942739145613620810693783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923652194151494414258377 2942739145613620810693783)
                      ·
                        rfl

theorem cell23_5730964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_5730964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730964 prefixEnd_5730964 := by exact prefixLift 5730964
  have htrace : WordTrace (prefixWord ++ tailWord_5730964) baseStart_5730964 baseEnd_5730964 := by
    simpa [prefixWord, tailWord_5730964, baseEnd_5730964] using wordTrace_append hprefix tailTrace_5730964
  have hstable : (prefixWord ++ tailWord_5730964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730964).length < 2 ^ (prefixWord ++ tailWord_5730964).sum := by decide
  have hdescent : baseEnd_5730964 < baseStart_5730964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5730969 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 4]
def baseStart_5730969 : Nat := 118140960795 + 5730969 * 2 ^ 59
def prefixEnd_5730969 : Nat := 4983230072969 + 3 ^ 40 * 5730969 * 2
def baseEnd_5730969 : Nat := 2942741713016893291131259

theorem tailTrace_5730969 : CollatzResearch.WordTrace tailWord_5730969 prefixEnd_5730969 2942741713016893291131259 := by
  unfold tailWord_5730969
  simp only [CollatzResearch.WordTrace]
  refine ⟨209025611574685559426323961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139350407716457039617549307 209025611574685559426323961)
  ·
    refine ⟨156769208681014169569742971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209025611574685559426323961 156769208681014169569742971)
    ·
      refine ⟨235153813021521254354614457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156769208681014169569742971 235153813021521254354614457)
      ·
        refine ⟨176365359766140940765960843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235153813021521254354614457 176365359766140940765960843)
        ·
          refine ⟨264548039649211411148941265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176365359766140940765960843 264548039649211411148941265)
          ·
            refine ⟨198411029736908558361705949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264548039649211411148941265 198411029736908558361705949)
            ·
              refine ⟨74404136151340709385639731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198411029736908558361705949 74404136151340709385639731)
              ·
                refine ⟨111606204227011064078459597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74404136151340709385639731 111606204227011064078459597)
                ·
                  refine ⟨41852326585129149029422349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111606204227011064078459597 41852326585129149029422349)
                  ·
                    refine ⟨15694622469423430886033381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41852326585129149029422349 15694622469423430886033381)
                    ·
                      refine ⟨2942741713016893291131259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15694622469423430886033381 2942741713016893291131259)
                      ·
                        rfl

theorem cell23_5730969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_5730969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5730969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5730969 prefixEnd_5730969 := by exact prefixLift 5730969
  have htrace : WordTrace (prefixWord ++ tailWord_5730969) baseStart_5730969 baseEnd_5730969 := by
    simpa [prefixWord, tailWord_5730969, baseEnd_5730969] using wordTrace_append hprefix tailTrace_5730969
  have hstable : (prefixWord ++ tailWord_5730969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5730969).length < 2 ^ (prefixWord ++ tailWord_5730969).sum := by decide
  have hdescent : baseEnd_5730969 < baseStart_5730969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5730969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731093 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_5731093 : Nat := 118140960795 + 5731093 * 2 ^ 59
def prefixEnd_5731093 : Nat := 4983230072969 + 3 ^ 40 * 5731093 * 2
def baseEnd_5731093 : Nat := 2942805384618050805980689

theorem tailTrace_5731093 : CollatzResearch.WordTrace tailWord_5731093 prefixEnd_5731093 2942805384618050805980689 := by
  unfold tailWord_5731093
  simp only [CollatzResearch.WordTrace]
  refine ⟨209030134226236328603837933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139353422817490885735891955 209030134226236328603837933)
  ·
    refine ⟨78386300334838623226439225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209030134226236328603837933 78386300334838623226439225)
    ·
      refine ⟨58789725251128967419829419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78386300334838623226439225 58789725251128967419829419)
      ·
        refine ⟨88184587876693451129744129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58789725251128967419829419 88184587876693451129744129)
        ·
          refine ⟨66138440907520088347308097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88184587876693451129744129 66138440907520088347308097)
          ·
            refine ⟨49603830680640066260481073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66138440907520088347308097 49603830680640066260481073)
            ·
              refine ⟨37202873010480049695360805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49603830680640066260481073 37202873010480049695360805)
              ·
                refine ⟨6975538689465009317880151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37202873010480049695360805 6975538689465009317880151)
                ·
                  refine ⟨10463308034197513976820227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6975538689465009317880151 10463308034197513976820227)
                  ·
                    refine ⟨15694962051296270965230341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10463308034197513976820227 15694962051296270965230341)
                    ·
                      refine ⟨2942805384618050805980689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15694962051296270965230341 2942805384618050805980689)
                      ·
                        rfl

theorem cell23_5731093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_5731093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731093 prefixEnd_5731093 := by exact prefixLift 5731093
  have htrace : WordTrace (prefixWord ++ tailWord_5731093) baseStart_5731093 baseEnd_5731093 := by
    simpa [prefixWord, tailWord_5731093, baseEnd_5731093] using wordTrace_append hprefix tailTrace_5731093
  have hstable : (prefixWord ++ tailWord_5731093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731093).length < 2 ^ (prefixWord ++ tailWord_5731093).sum := by decide
  have hdescent : baseEnd_5731093 < baseStart_5731093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731113 : List Nat := [1, 2, 1, 1, 1, 1, 1, 9, 1, 2, 3]
def baseStart_5731113 : Nat := 118140960795 + 5731113 * 2 ^ 59
def prefixEnd_5731113 : Nat := 4983230072969 + 3 ^ 40 * 5731113 * 2
def baseEnd_5731113 : Nat := 2942815654231140727730597

theorem tailTrace_5731113 : CollatzResearch.WordTrace tailWord_5731113 prefixEnd_5731113 2942815654231140727730597 := by
  unfold tailWord_5731113
  simp only [CollatzResearch.WordTrace]
  refine ⟨209030863686163872019565993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139353909124109248013043995 209030863686163872019565993)
  ·
    refine ⟨156773147764622904014674495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209030863686163872019565993 156773147764622904014674495)
    ·
      refine ⟨235159721646934356022011743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156773147764622904014674495 235159721646934356022011743)
      ·
        refine ⟨352739582470401534033017615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235159721646934356022011743 352739582470401534033017615)
        ·
          refine ⟨529109373705602301049526423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352739582470401534033017615 529109373705602301049526423)
          ·
            refine ⟨793664060558403451574289635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529109373705602301049526423 793664060558403451574289635)
            ·
              refine ⟨1190496090837605177361434453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793664060558403451574289635 1190496090837605177361434453)
              ·
                refine ⟨6975563032251592836102155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1190496090837605177361434453 6975563032251592836102155)
                ·
                  refine ⟨10463344548377389254153233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6975563032251592836102155 10463344548377389254153233)
                  ·
                    refine ⟨7847508411283041940614925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10463344548377389254153233 7847508411283041940614925)
                    ·
                      refine ⟨2942815654231140727730597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7847508411283041940614925 2942815654231140727730597)
                      ·
                        rfl

theorem cell23_5731113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 1, 2, 3].length) (baseStart_5731113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731113 prefixEnd_5731113 := by exact prefixLift 5731113
  have htrace : WordTrace (prefixWord ++ tailWord_5731113) baseStart_5731113 baseEnd_5731113 := by
    simpa [prefixWord, tailWord_5731113, baseEnd_5731113] using wordTrace_append hprefix tailTrace_5731113
  have hstable : (prefixWord ++ tailWord_5731113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731113).length < 2 ^ (prefixWord ++ tailWord_5731113).sum := by decide
  have hdescent : baseEnd_5731113 < baseStart_5731113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731127 : List Nat := [1, 1, 3, 1, 2, 1, 3, 6, 1, 2, 2]
def baseStart_5731127 : Nat := 118140960795 + 5731127 * 2 ^ 59
def prefixEnd_5731127 : Nat := 4983230072969 + 3 ^ 40 * 5731127 * 2
def baseEnd_5731127 : Nat := 2942822842960303672955533

theorem tailTrace_5731127 : CollatzResearch.WordTrace tailWord_5731127 prefixEnd_5731127 2942822842960303672955533 := by
  unfold tailWord_5731127
  simp only [CollatzResearch.WordTrace]
  refine ⟨209031374308113152410575635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139354249538742101607050423 209031374308113152410575635)
  ·
    refine ⟨313547061462169728615863453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209031374308113152410575635 313547061462169728615863453)
    ·
      refine ⟨117580148048313648230948795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313547061462169728615863453 117580148048313648230948795)
      ·
        refine ⟨176370222072470472346423193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117580148048313648230948795 176370222072470472346423193)
        ·
          refine ⟨132277666554352854259817395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176370222072470472346423193 132277666554352854259817395)
          ·
            refine ⟨198416499831529281389726093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132277666554352854259817395 198416499831529281389726093)
            ·
              refine ⟨74406187436823480521147285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198416499831529281389726093 74406187436823480521147285)
              ·
                refine ⟨3487790036101100649428779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74406187436823480521147285 3487790036101100649428779)
                ·
                  refine ⟨5231685054151650974143169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487790036101100649428779 5231685054151650974143169)
                  ·
                    refine ⟨3923763790613738230607377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5231685054151650974143169 3923763790613738230607377)
                    ·
                      refine ⟨2942822842960303672955533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923763790613738230607377 2942822842960303672955533)
                      ·
                        rfl

theorem cell23_5731127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 6, 1, 2, 2].length) (baseStart_5731127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731127 prefixEnd_5731127 := by exact prefixLift 5731127
  have htrace : WordTrace (prefixWord ++ tailWord_5731127) baseStart_5731127 baseEnd_5731127 := by
    simpa [prefixWord, tailWord_5731127, baseEnd_5731127] using wordTrace_append hprefix tailTrace_5731127
  have hstable : (prefixWord ++ tailWord_5731127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731127).length < 2 ^ (prefixWord ++ tailWord_5731127).sum := by decide
  have hdescent : baseEnd_5731127 < baseStart_5731127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731137 : List Nat := [1, 2, 5, 3, 1, 2, 1, 1, 1, 6]
def baseStart_5731137 : Nat := 118140960795 + 5731137 * 2 ^ 59
def prefixEnd_5731137 : Nat := 4983230072969 + 3 ^ 40 * 5731137 * 2
def baseEnd_5731137 : Nat := 980942659255616211276829

theorem tailTrace_5731137 : CollatzResearch.WordTrace tailWord_5731137 prefixEnd_5731137 980942659255616211276829 := by
  unfold tailWord_5731137
  simp only [CollatzResearch.WordTrace]
  refine ⟨209031739038076924118439665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139354492692051282745626443 209031739038076924118439665)
  ·
    refine ⟨156773804278557693088829749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209031739038076924118439665 156773804278557693088829749)
    ·
      refine ⟨14697544151114783727077789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156773804278557693088829749 14697544151114783727077789)
      ·
        refine ⟨5511579056668043897654171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14697544151114783727077789 5511579056668043897654171)
        ·
          refine ⟨8267368585002065846481257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5511579056668043897654171 8267368585002065846481257)
          ·
            refine ⟨6200526438751549384860943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8267368585002065846481257 6200526438751549384860943)
            ·
              refine ⟨9300789658127324077291415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6200526438751549384860943 9300789658127324077291415)
              ·
                refine ⟨13951184487190986115937123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9300789658127324077291415 13951184487190986115937123)
                ·
                  refine ⟨20926776730786479173905685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13951184487190986115937123 20926776730786479173905685)
                  ·
                    refine ⟨980942659255616211276829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20926776730786479173905685 980942659255616211276829)
                    ·
                      rfl

theorem cell23_5731137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_5731137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731137 prefixEnd_5731137 := by exact prefixLift 5731137
  have htrace : WordTrace (prefixWord ++ tailWord_5731137) baseStart_5731137 baseEnd_5731137 := by
    simpa [prefixWord, tailWord_5731137, baseEnd_5731137] using wordTrace_append hprefix tailTrace_5731137
  have hstable : (prefixWord ++ tailWord_5731137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731137).length < 2 ^ (prefixWord ++ tailWord_5731137).sum := by decide
  have hdescent : baseEnd_5731137 < baseStart_5731137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731196 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_5731196 : Nat := 118140960795 + 5731196 * 2 ^ 59
def prefixEnd_5731196 : Nat := 4983230072969 + 3 ^ 40 * 5731196 * 2
def baseEnd_5731196 : Nat := 2942858273125463902992715

theorem tailTrace_5731196 : CollatzResearch.WordTrace tailWord_5731196 prefixEnd_5731196 2942858273125463902992715 := by
  unfold tailWord_5731196
  simp only [CollatzResearch.WordTrace]
  refine ⟨104516945472431588597418721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139355927296575451463224961 104516945472431588597418721)
  ·
    refine ⟨78387709104323691448064041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104516945472431588597418721 78387709104323691448064041)
    ·
      refine ⟨58790781828242768586048031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78387709104323691448064041 58790781828242768586048031)
      ·
        refine ⟨88186172742364152879072047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58790781828242768586048031 88186172742364152879072047)
        ·
          refine ⟨132279259113546229318608071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88186172742364152879072047 132279259113546229318608071)
          ·
            refine ⟨198418888670319343977912107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132279259113546229318608071 198418888670319343977912107)
            ·
              refine ⟨297628333005479015966868161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198418888670319343977912107 297628333005479015966868161)
              ·
                refine ⟨223221249754109261975151121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297628333005479015966868161 223221249754109261975151121)
                ·
                  refine ⟨167415937315581946481363341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223221249754109261975151121 167415937315581946481363341)
                  ·
                    refine ⟨62780976493343229930511253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 167415937315581946481363341 62780976493343229930511253)
                    ·
                      refine ⟨2942858273125463902992715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62780976493343229930511253 2942858273125463902992715)
                      ·
                        rfl

theorem cell23_5731196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_5731196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731196 prefixEnd_5731196 := by exact prefixLift 5731196
  have htrace : WordTrace (prefixWord ++ tailWord_5731196) baseStart_5731196 baseEnd_5731196 := by
    simpa [prefixWord, tailWord_5731196, baseEnd_5731196] using wordTrace_append hprefix tailTrace_5731196
  have hstable : (prefixWord ++ tailWord_5731196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731196).length < 2 ^ (prefixWord ++ tailWord_5731196).sum := by decide
  have hdescent : baseEnd_5731196 < baseStart_5731196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731200 : List Nat := [2, 1, 1, 2, 1, 2, 2, 2, 6, 2, 2]
def baseStart_5731200 : Nat := 118140960795 + 5731200 * 2 ^ 59
def prefixEnd_5731200 : Nat := 4983230072969 + 3 ^ 40 * 5731200 * 2
def baseEnd_5731200 : Nat := 2942860327048081887342697

theorem tailTrace_5731200 : CollatzResearch.WordTrace tailWord_5731200 prefixEnd_5731200 2942860327048081887342697 := by
  unfold tailWord_5731200
  simp only [CollatzResearch.WordTrace]
  refine ⟨104517018418424342938991527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139356024557899123918655369 104517018418424342938991527)
  ·
    refine ⟨156775527627636514408487291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104517018418424342938991527 156775527627636514408487291)
    ·
      refine ⟨235163291441454771612730937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156775527627636514408487291 235163291441454771612730937)
      ·
        refine ⟨176372468581091078709548203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235163291441454771612730937 176372468581091078709548203)
        ·
          refine ⟨264558702871636618064322305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176372468581091078709548203 264558702871636618064322305)
          ·
            refine ⟨198419027153727463548241729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264558702871636618064322305 198419027153727463548241729)
            ·
              refine ⟨148814270365295597661181297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198419027153727463548241729 148814270365295597661181297)
              ·
                refine ⟨111610702773971698245885973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148814270365295597661181297 111610702773971698245885973)
                ·
                  refine ⟨5231751692529923355275905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111610702773971698245885973 5231751692529923355275905)
                  ·
                    refine ⟨3923813769397442516456929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5231751692529923355275905 3923813769397442516456929)
                    ·
                      refine ⟨2942860327048081887342697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923813769397442516456929 2942860327048081887342697)
                      ·
                        rfl

theorem cell23_5731200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 6, 2, 2].length) (baseStart_5731200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731200 prefixEnd_5731200 := by exact prefixLift 5731200
  have htrace : WordTrace (prefixWord ++ tailWord_5731200) baseStart_5731200 baseEnd_5731200 := by
    simpa [prefixWord, tailWord_5731200, baseEnd_5731200] using wordTrace_append hprefix tailTrace_5731200
  have hstable : (prefixWord ++ tailWord_5731200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731200).length < 2 ^ (prefixWord ++ tailWord_5731200).sum := by decide
  have hdescent : baseEnd_5731200 < baseStart_5731200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731234 : List Nat := [3, 3, 1, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_5731234 : Nat := 118140960795 + 5731234 * 2 ^ 59
def prefixEnd_5731234 : Nat := 4983230072969 + 3 ^ 40 * 5731234 * 2
def baseEnd_5731234 : Nat := 2942877785390334754317541

theorem tailTrace_5731234 : CollatzResearch.WordTrace tailWord_5731234 prefixEnd_5731234 2942877785390334754317541 := by
  unfold tailWord_5731234
  simp only [CollatzResearch.WordTrace]
  refine ⟨52258819229681377421180189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139356851279150339789813837 52258819229681377421180189)
  ·
    refine ⟨19597057211130516532942571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52258819229681377421180189 19597057211130516532942571)
    ·
      refine ⟨29395585816695774799413857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19597057211130516532942571 29395585816695774799413857)
      ·
        refine ⟨22046689362521831099560393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29395585816695774799413857 22046689362521831099560393)
        ·
          refine ⟨16535017021891373324670295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22046689362521831099560393 16535017021891373324670295)
          ·
            refine ⟨24802525532837059987005443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16535017021891373324670295 24802525532837059987005443)
            ·
              refine ⟨37203788299255589980508165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24802525532837059987005443 37203788299255589980508165)
              ·
                refine ⟨6975710306110423121345281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37203788299255589980508165 6975710306110423121345281)
                ·
                  refine ⟨5231782729582817341008961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6975710306110423121345281 5231782729582817341008961)
                  ·
                    refine ⟨3923837047187113005756721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5231782729582817341008961 3923837047187113005756721)
                    ·
                      refine ⟨2942877785390334754317541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923837047187113005756721 2942877785390334754317541)
                      ·
                        rfl

theorem cell23_5731234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_5731234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731234 prefixEnd_5731234 := by exact prefixLift 5731234
  have htrace : WordTrace (prefixWord ++ tailWord_5731234) baseStart_5731234 baseEnd_5731234 := by
    simpa [prefixWord, tailWord_5731234, baseEnd_5731234] using wordTrace_append hprefix tailTrace_5731234
  have hstable : (prefixWord ++ tailWord_5731234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731234).length < 2 ^ (prefixWord ++ tailWord_5731234).sum := by decide
  have hdescent : baseEnd_5731234 < baseStart_5731234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731253 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_5731253 : Nat := 118140960795 + 5731253 * 2 ^ 59
def prefixEnd_5731253 : Nat := 4983230072969 + 3 ^ 40 * 5731253 * 2
def baseEnd_5731253 : Nat := 980962513840923393326651

theorem tailTrace_5731253 : CollatzResearch.WordTrace tailWord_5731253 prefixEnd_5731253 980962513840923393326651 := by
  unfold tailWord_5731253
  simp only [CollatzResearch.WordTrace]
  refine ⟨209035969905656675929662413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139357313270437783953108275 209035969905656675929662413)
  ·
    refine ⟨78388488714621253473623405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209035969905656675929662413 78388488714621253473623405)
    ·
      refine ⟨29395683267982970052608777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78388488714621253473623405 29395683267982970052608777)
      ·
        refine ⟨22046762450987227539456583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29395683267982970052608777 22046762450987227539456583)
        ·
          refine ⟨33070143676480841309184875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22046762450987227539456583 33070143676480841309184875)
          ·
            refine ⟨49605215514721261963777313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33070143676480841309184875 49605215514721261963777313)
            ·
              refine ⟨37203911636040946472832985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49605215514721261963777313 37203911636040946472832985)
              ·
                refine ⟨27902933727030709854624739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37203911636040946472832985 27902933727030709854624739)
                ·
                  refine ⟨41854400590546064781937109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27902933727030709854624739 41854400590546064781937109)
                  ·
                    refine ⟨980962513840923393326651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41854400590546064781937109 980962513840923393326651)
                    ·
                      rfl

theorem cell23_5731253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_5731253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731253 prefixEnd_5731253 := by exact prefixLift 5731253
  have htrace : WordTrace (prefixWord ++ tailWord_5731253) baseStart_5731253 baseEnd_5731253 := by
    simpa [prefixWord, tailWord_5731253, baseEnd_5731253] using wordTrace_append hprefix tailTrace_5731253
  have hstable : (prefixWord ++ tailWord_5731253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731253).length < 2 ^ (prefixWord ++ tailWord_5731253).sum := by decide
  have hdescent : baseEnd_5731253 < baseStart_5731253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731323 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 3]
def baseStart_5731323 : Nat := 118140960795 + 5731323 * 2 ^ 59
def prefixEnd_5731323 : Nat := 4983230072969 + 3 ^ 40 * 5731323 * 2
def baseEnd_5731323 : Nat := 2942923485168584906104631

theorem tailTrace_5731323 : CollatzResearch.WordTrace tailWord_5731323 prefixEnd_5731323 2942923485168584906104631 := by
  unfold tailWord_5731323
  simp only [CollatzResearch.WordTrace]
  refine ⟨209038523015403077884710623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139359015343602051923140415 209038523015403077884710623)
  ·
    refine ⟨313557784523104616827065935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209038523015403077884710623 313557784523104616827065935)
    ·
      refine ⟨470336676784656925240598903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313557784523104616827065935 470336676784656925240598903)
      ·
        refine ⟨705505015176985387860898355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470336676784656925240598903 705505015176985387860898355)
        ·
          refine ⟨1058257522765478081791347533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705505015176985387860898355 1058257522765478081791347533)
          ·
            refine ⟨396846571037054280671755325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1058257522765478081791347533 396846571037054280671755325)
            ·
              refine ⟨148817464138895355251908247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396846571037054280671755325 148817464138895355251908247)
              ·
                refine ⟨223226196208343032877862371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148817464138895355251908247 223226196208343032877862371)
                ·
                  refine ⟨334839294312514549316793557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223226196208343032877862371 334839294312514549316793557)
                  ·
                    refine ⟨7847795960449559749612349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 334839294312514549316793557 7847795960449559749612349)
                    ·
                      refine ⟨2942923485168584906104631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7847795960449559749612349 2942923485168584906104631)
                      ·
                        rfl

theorem cell23_5731323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 3].length) (baseStart_5731323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731323 prefixEnd_5731323 := by exact prefixLift 5731323
  have htrace : WordTrace (prefixWord ++ tailWord_5731323) baseStart_5731323 baseEnd_5731323 := by
    simpa [prefixWord, tailWord_5731323, baseEnd_5731323] using wordTrace_append hprefix tailTrace_5731323
  have hstable : (prefixWord ++ tailWord_5731323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731323).length < 2 ^ (prefixWord ++ tailWord_5731323).sum := by decide
  have hdescent : baseEnd_5731323 < baseStart_5731323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731351 : List Nat := [1, 1, 3, 5, 1, 2, 3, 2, 1, 4]
def baseStart_5731351 : Nat := 118140960795 + 5731351 * 2 ^ 59
def prefixEnd_5731351 : Nat := 4983230072969 + 3 ^ 40 * 5731351 * 2
def baseEnd_5731351 : Nat := 980979287542303598851501

theorem tailTrace_5731351 : CollatzResearch.WordTrace tailWord_5731351 prefixEnd_5731351 980979287542303598851501 := by
  unfold tailWord_5731351
  simp only [CollatzResearch.WordTrace]
  refine ⟨209039544259301638666729907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139359696172867759111153271 209039544259301638666729907)
  ·
    refine ⟨313559316388952458000094861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209039544259301638666729907 313559316388952458000094861)
    ·
      refine ⟨117584743645857171750035573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313559316388952458000094861 117584743645857171750035573)
      ·
        refine ⟨11023569716799109851565835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117584743645857171750035573 11023569716799109851565835)
        ·
          refine ⟨16535354575198664777348753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11023569716799109851565835 16535354575198664777348753)
          ·
            refine ⟨12401515931398998583011565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16535354575198664777348753 12401515931398998583011565)
            ·
              refine ⟨4650568474274624468629337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12401515931398998583011565 4650568474274624468629337)
              ·
                refine ⟨3487926355705968351472003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4650568474274624468629337 3487926355705968351472003)
                ·
                  refine ⟨5231889533558952527208005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3487926355705968351472003 5231889533558952527208005)
                  ·
                    refine ⟨980979287542303598851501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5231889533558952527208005 980979287542303598851501)
                    ·
                      rfl

theorem cell23_5731351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 1, 4].length) (baseStart_5731351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731351 prefixEnd_5731351 := by exact prefixLift 5731351
  have htrace : WordTrace (prefixWord ++ tailWord_5731351) baseStart_5731351 baseEnd_5731351 := by
    simpa [prefixWord, tailWord_5731351, baseEnd_5731351] using wordTrace_append hprefix tailTrace_5731351
  have hstable : (prefixWord ++ tailWord_5731351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731351).length < 2 ^ (prefixWord ++ tailWord_5731351).sum := by decide
  have hdescent : baseEnd_5731351 < baseStart_5731351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731364 : List Nat := [2, 3, 1, 4, 1, 3, 2, 1, 6]
def baseStart_5731364 : Nat := 118140960795 + 5731364 * 2 ^ 59
def prefixEnd_5731364 : Nat := 4983230072969 + 3 ^ 40 * 5731364 * 2
def baseEnd_5731364 : Nat := 326993837541713249521327

theorem tailTrace_5731364 : CollatzResearch.WordTrace tailWord_5731364 prefixEnd_5731364 326993837541713249521327 := by
  unfold tailWord_5731364
  simp only [CollatzResearch.WordTrace]
  refine ⟨104520009204127270943476573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139360012272169694591302097 104520009204127270943476573)
  ·
    refine ⟨39195003451547726603803715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104520009204127270943476573 39195003451547726603803715)
    ·
      refine ⟨58792505177321589905705573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39195003451547726603803715 58792505177321589905705573)
      ·
        refine ⟨11023594720747798107319795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58792505177321589905705573 11023594720747798107319795)
        ·
          refine ⟨16535392081121697160979693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11023594720747798107319795 16535392081121697160979693)
          ·
            refine ⟨6200772030420636435367385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16535392081121697160979693 6200772030420636435367385)
            ·
              refine ⟨4650579022815477326525539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6200772030420636435367385 4650579022815477326525539)
              ·
                refine ⟨6975868534223215989788309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650579022815477326525539 6975868534223215989788309)
                ·
                  refine ⟨326993837541713249521327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6975868534223215989788309 326993837541713249521327)
                  ·
                    rfl

theorem cell23_5731364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_5731364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731364 prefixEnd_5731364 := by exact prefixLift 5731364
  have htrace : WordTrace (prefixWord ++ tailWord_5731364) baseStart_5731364 baseEnd_5731364 := by
    simpa [prefixWord, tailWord_5731364, baseEnd_5731364] using wordTrace_append hprefix tailTrace_5731364
  have hstable : (prefixWord ++ tailWord_5731364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731364).length < 2 ^ (prefixWord ++ tailWord_5731364).sum := by decide
  have hdescent : baseEnd_5731364 < baseStart_5731364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731384 : List Nat := [2, 1, 2, 1, 5, 2, 2, 1, 2, 3, 2]
def baseStart_5731384 : Nat := 118140960795 + 5731384 * 2 ^ 59
def prefixEnd_5731384 : Nat := 4983230072969 + 3 ^ 40 * 5731384 * 2
def baseEnd_5731384 : Nat := 2942954807488509167441851

theorem tailTrace_5731384 : CollatzResearch.WordTrace tailWord_5731384 prefixEnd_5731384 2942954807488509167441851 := by
  unfold tailWord_5731384
  simp only [CollatzResearch.WordTrace]
  refine ⟨104520373934091042651340603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139360498578788056868454137 104520373934091042651340603)
  ·
    refine ⟨156780560901136563977010905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104520373934091042651340603 156780560901136563977010905)
    ·
      refine ⟨117585420675852422982758179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156780560901136563977010905 117585420675852422982758179)
      ·
        refine ⟨176378131013778634474137269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117585420675852422982758179 176378131013778634474137269)
        ·
          refine ⟨16535449782541746981950369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176378131013778634474137269 16535449782541746981950369)
          ·
            refine ⟨12401587336906310236462777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16535449782541746981950369 12401587336906310236462777)
            ·
              refine ⟨9301190502679732677347083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12401587336906310236462777 9301190502679732677347083)
              ·
                refine ⟨13951785754019599016020625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9301190502679732677347083 13951785754019599016020625)
                ·
                  refine ⟨10463839315514699262015469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13951785754019599016020625 10463839315514699262015469)
                  ·
                    refine ⟨3923939743318012223255801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10463839315514699262015469 3923939743318012223255801)
                    ·
                      refine ⟨2942954807488509167441851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3923939743318012223255801 2942954807488509167441851)
                      ·
                        rfl

theorem cell23_5731384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 2, 1, 2, 3, 2].length) (baseStart_5731384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731384 prefixEnd_5731384 := by exact prefixLift 5731384
  have htrace : WordTrace (prefixWord ++ tailWord_5731384) baseStart_5731384 baseEnd_5731384 := by
    simpa [prefixWord, tailWord_5731384, baseEnd_5731384] using wordTrace_append hprefix tailTrace_5731384
  have hstable : (prefixWord ++ tailWord_5731384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731384).length < 2 ^ (prefixWord ++ tailWord_5731384).sum := by decide
  have hdescent : baseEnd_5731384 < baseStart_5731384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731437 : List Nat := [1, 5, 1, 1, 2, 3, 3, 7]
def baseStart_5731437 : Nat := 118140960795 + 5731437 * 2 ^ 59
def prefixEnd_5731437 : Nat := 4983230072969 + 3 ^ 40 * 5731437 * 2
def baseEnd_5731437 : Nat := 108999334146785091114041

theorem tailTrace_5731437 : CollatzResearch.WordTrace tailWord_5731437 prefixEnd_5731437 108999334146785091114041 := by
  unfold tailWord_5731437
  simp only [CollatzResearch.WordTrace]
  refine ⟨209042680936990075354360565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139361787291326716902907043 209042680936990075354360565)
  ·
    refine ⟨19597751337842819564471303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209042680936990075354360565 19597751337842819564471303)
    ·
      refine ⟨29396627006764229346706955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19597751337842819564471303 29396627006764229346706955)
      ·
        refine ⟨44094940510146344020060433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29396627006764229346706955 44094940510146344020060433)
        ·
          refine ⟨33071205382609758015045325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44094940510146344020060433 33071205382609758015045325)
          ·
            refine ⟨12401702018478659255641997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33071205382609758015045325 12401702018478659255641997)
            ·
              refine ⟨4650638256929497220865749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12401702018478659255641997 4650638256929497220865749)
              ·
                refine ⟨108999334146785091114041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4650638256929497220865749 108999334146785091114041)
                ·
                  rfl

theorem cell23_5731437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 7].length) (baseStart_5731437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731437 prefixEnd_5731437 := by exact prefixLift 5731437
  have htrace : WordTrace (prefixWord ++ tailWord_5731437) baseStart_5731437 baseEnd_5731437 := by
    simpa [prefixWord, tailWord_5731437, baseEnd_5731437] using wordTrace_append hprefix tailTrace_5731437
  have hstable : (prefixWord ++ tailWord_5731437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731437).length < 2 ^ (prefixWord ++ tailWord_5731437).sum := by decide
  have hdescent : baseEnd_5731437 < baseStart_5731437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731447 : List Nat := [1, 1, 3, 1, 1, 4, 2, 2, 4, 1, 3]
def baseStart_5731447 : Nat := 118140960795 + 5731447 * 2 ^ 59
def prefixEnd_5731447 : Nat := 4983230072969 + 3 ^ 40 * 5731447 * 2
def baseEnd_5731447 : Nat := 2942987156769742420954061

theorem tailTrace_5731447 : CollatzResearch.WordTrace tailWord_5731447 prefixEnd_5731447 2942987156769742420954061 := by
  unfold tailWord_5731447
  simp only [CollatzResearch.WordTrace]
  refine ⟨209043045666953847062224595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139362030444635898041483063 209043045666953847062224595)
  ·
    refine ⟨313564568500430770593336893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209043045666953847062224595 313564568500430770593336893)
    ·
      refine ⟨117586713187661538972501335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313564568500430770593336893 117586713187661538972501335)
      ·
        refine ⟨176380069781492308458752003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117586713187661538972501335 176380069781492308458752003)
        ·
          refine ⟨264570104672238462688128005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176380069781492308458752003 264570104672238462688128005)
          ·
            refine ⟨49606894626044711754024001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264570104672238462688128005 49606894626044711754024001)
            ·
              refine ⟨37205170969533533815518001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49606894626044711754024001 37205170969533533815518001)
              ·
                refine ⟨27903878227150150361638501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37205170969533533815518001 27903878227150150361638501)
                ·
                  refine ⟨5231977167590653192807219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27903878227150150361638501 5231977167590653192807219)
                  ·
                    refine ⟨7847965751385979789210829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5231977167590653192807219 7847965751385979789210829)
                    ·
                      refine ⟨2942987156769742420954061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7847965751385979789210829 2942987156769742420954061)
                      ·
                        rfl

theorem cell23_5731447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_5731447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731447 prefixEnd_5731447 := by exact prefixLift 5731447
  have htrace : WordTrace (prefixWord ++ tailWord_5731447) baseStart_5731447 baseEnd_5731447 := by
    simpa [prefixWord, tailWord_5731447, baseEnd_5731447] using wordTrace_append hprefix tailTrace_5731447
  have hstable : (prefixWord ++ tailWord_5731447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731447).length < 2 ^ (prefixWord ++ tailWord_5731447).sum := by decide
  have hdescent : baseEnd_5731447 < baseStart_5731447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731500 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_5731500 : Nat := 118140960795 + 5731500 * 2 ^ 59
def prefixEnd_5731500 : Nat := 4983230072969 + 3 ^ 40 * 5731500 * 2
def baseEnd_5731500 : Nat := 2943014371244430713591317

theorem tailTrace_5731500 : CollatzResearch.WordTrace tailWord_5731500 prefixEnd_5731500 2943014371244430713591317 := by
  unfold tailWord_5731500
  simp only [CollatzResearch.WordTrace]
  refine ⟨104522489367880918556951977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139363319157174558075935969 104522489367880918556951977)
  ·
    refine ⟨78391867025910688917713983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104522489367880918556951977 78391867025910688917713983)
    ·
      refine ⟨117587800538866033376570975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78391867025910688917713983 117587800538866033376570975)
      ·
        refine ⟨176381700808299050064856463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117587800538866033376570975 176381700808299050064856463)
        ·
          refine ⟨264572551212448575097284695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176381700808299050064856463 264572551212448575097284695)
          ·
            refine ⟨396858826818672862645927043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264572551212448575097284695 396858826818672862645927043)
            ·
              refine ⟨595288240228009293968890565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396858826818672862645927043 595288240228009293968890565)
              ·
                refine ⟨111616545042751742619166981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 595288240228009293968890565 111616545042751742619166981)
                ·
                  refine ⟨20928102195515951741093809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111616545042751742619166981 20928102195515951741093809)
                  ·
                    refine ⟨15696076646636963805820357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20928102195515951741093809 15696076646636963805820357)
                    ·
                      refine ⟨2943014371244430713591317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15696076646636963805820357 2943014371244430713591317)
                      ·
                        rfl

theorem cell23_5731500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_5731500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731500 prefixEnd_5731500 := by exact prefixLift 5731500
  have htrace : WordTrace (prefixWord ++ tailWord_5731500) baseStart_5731500 baseEnd_5731500 := by
    simpa [prefixWord, tailWord_5731500, baseEnd_5731500] using wordTrace_append hprefix tailTrace_5731500
  have hstable : (prefixWord ++ tailWord_5731500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731500).length < 2 ^ (prefixWord ++ tailWord_5731500).sum := by decide
  have hdescent : baseEnd_5731500 < baseStart_5731500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731527 : List Nat := [1, 1, 4, 1, 1, 1, 1, 8, 5]
def baseStart_5731527 : Nat := 118140960795 + 5731527 * 2 ^ 59
def prefixEnd_5731527 : Nat := 4983230072969 + 3 ^ 40 * 5731527 * 2
def baseEnd_5731527 : Nat := 327003137246900234217077

theorem tailTrace_5731527 : CollatzResearch.WordTrace tailWord_5731527 prefixEnd_5731527 327003137246900234217077 := by
  unfold tailWord_5731527
  simp only [CollatzResearch.WordTrace]
  refine ⟨209045963506664020725136835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139363975671109347150091223 209045963506664020725136835)
  ·
    refine ⟨313568945259996031087705253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209045963506664020725136835 313568945259996031087705253)
    ·
      refine ⟨58794177236249255828944735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313568945259996031087705253 58794177236249255828944735)
      ·
        refine ⟨88191265854373883743417103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58794177236249255828944735 88191265854373883743417103)
        ·
          refine ⟨132286898781560825615125655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88191265854373883743417103 132286898781560825615125655)
          ·
            refine ⟨198430348172341238422688483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132286898781560825615125655 198430348172341238422688483)
            ·
              refine ⟨297645522258511857634032725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198430348172341238422688483 297645522258511857634032725)
              ·
                refine ⟨3488033463966935831648821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 297645522258511857634032725 3488033463966935831648821)
                ·
                  refine ⟨327003137246900234217077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3488033463966935831648821 327003137246900234217077)
                  ·
                    rfl

theorem cell23_5731527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 5].length) (baseStart_5731527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731527 prefixEnd_5731527 := by exact prefixLift 5731527
  have htrace : WordTrace (prefixWord ++ tailWord_5731527) baseStart_5731527 baseEnd_5731527 := by
    simpa [prefixWord, tailWord_5731527, baseEnd_5731527] using wordTrace_append hprefix tailTrace_5731527
  have hstable : (prefixWord ++ tailWord_5731527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731527).length < 2 ^ (prefixWord ++ tailWord_5731527).sum := by decide
  have hdescent : baseEnd_5731527 < baseStart_5731527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731542 : List Nat := [5, 2, 1, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_5731542 : Nat := 118140960795 + 5731542 * 2 ^ 59
def prefixEnd_5731542 : Nat := 4983230072969 + 3 ^ 40 * 5731542 * 2
def baseEnd_5731542 : Nat := 2943035937431919549266125

theorem tailTrace_5731542 : CollatzResearch.WordTrace tailWord_5731542 prefixEnd_5731542 2943035937431919549266125 := by
  unfold tailWord_5731542
  simp only [CollatzResearch.WordTrace]
  refine ⟨13065406912600604892933305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139364340401073118857955253 13065406912600604892933305)
  ·
    refine ⟨9799055184450453669699979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13065406912600604892933305 9799055184450453669699979)
    ·
      refine ⟨14698582776675680504549969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9799055184450453669699979 14698582776675680504549969)
      ·
        refine ⟨11023937082506760378412477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14698582776675680504549969 11023937082506760378412477)
        ·
          refine ⟨4133976405940035141904679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11023937082506760378412477 4133976405940035141904679)
          ·
            refine ⟨6200964608910052712857019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4133976405940035141904679 6200964608910052712857019)
            ·
              refine ⟨9301446913365079069285529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6200964608910052712857019 9301446913365079069285529)
              ·
                refine ⟨6976085185023809301964147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9301446913365079069285529 6976085185023809301964147)
                ·
                  refine ⟨10464127777535713952946221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6976085185023809301964147 10464127777535713952946221)
                  ·
                    refine ⟨3924047916575892732354833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10464127777535713952946221 3924047916575892732354833)
                    ·
                      refine ⟨2943035937431919549266125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924047916575892732354833 2943035937431919549266125)
                      ·
                        rfl

theorem cell23_5731542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_5731542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731542 prefixEnd_5731542 := by exact prefixLift 5731542
  have htrace : WordTrace (prefixWord ++ tailWord_5731542) baseStart_5731542 baseEnd_5731542 := by
    simpa [prefixWord, tailWord_5731542, baseEnd_5731542] using wordTrace_append hprefix tailTrace_5731542
  have hstable : (prefixWord ++ tailWord_5731542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731542).length < 2 ^ (prefixWord ++ tailWord_5731542).sum := by decide
  have hdescent : baseEnd_5731542 < baseStart_5731542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731577 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 4]
def baseStart_5731577 : Nat := 118140960795 + 5731577 * 2 ^ 59
def prefixEnd_5731577 : Nat := 4983230072969 + 3 ^ 40 * 5731577 * 2
def baseEnd_5731577 : Nat := 2943053909254826912328463

theorem tailTrace_5731577 : CollatzResearch.WordTrace tailWord_5731577 prefixEnd_5731577 2943053909254826912328463 := by
  unfold tailWord_5731577
  simp only [CollatzResearch.WordTrace]
  refine ⟨209047787156482879264456985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139365191437655252842971323 209047787156482879264456985)
  ·
    refine ⟨156785840367362159448342739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209047787156482879264456985 156785840367362159448342739)
    ·
      refine ⟨235178760551043239172514109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156785840367362159448342739 235178760551043239172514109)
      ·
        refine ⟨88192035206641214689692791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235178760551043239172514109 88192035206641214689692791)
        ·
          refine ⟨132288052809961822034539187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88192035206641214689692791 132288052809961822034539187)
          ·
            refine ⟨198432079214942733051808781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132288052809961822034539187 198432079214942733051808781)
            ·
              refine ⟨74412029705603524894428293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198432079214942733051808781 74412029705603524894428293)
              ·
                refine ⟨13952255569800660917705305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74412029705603524894428293 13952255569800660917705305)
                ·
                  refine ⟨10464191677350495688278979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13952255569800660917705305 10464191677350495688278979)
                  ·
                    refine ⟨15696287516025743532418469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10464191677350495688278979 15696287516025743532418469)
                    ·
                      refine ⟨2943053909254826912328463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15696287516025743532418469 2943053909254826912328463)
                      ·
                        rfl

theorem cell23_5731577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_5731577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731577 prefixEnd_5731577 := by exact prefixLift 5731577
  have htrace : WordTrace (prefixWord ++ tailWord_5731577) baseStart_5731577 baseEnd_5731577 := by
    simpa [prefixWord, tailWord_5731577, baseEnd_5731577] using wordTrace_append hprefix tailTrace_5731577
  have hstable : (prefixWord ++ tailWord_5731577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731577).length < 2 ^ (prefixWord ++ tailWord_5731577).sum := by decide
  have hdescent : baseEnd_5731577 < baseStart_5731577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731621 : List Nat := [1, 3, 1, 2, 4, 1, 1, 5, 1, 4]
def baseStart_5731621 : Nat := 118140960795 + 5731621 * 2 ^ 59
def prefixEnd_5731621 : Nat := 4983230072969 + 3 ^ 40 * 5731621 * 2
def baseEnd_5731621 : Nat := 981025500801208246726087

theorem tailTrace_5731621 : CollatzResearch.WordTrace tailWord_5731621 prefixEnd_5731621 981025500801208246726087 := by
  unfold tailWord_5731621
  simp only [CollatzResearch.WordTrace]
  refine ⟨209049391968323474779058717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139366261312215649852705811 209049391968323474779058717)
  ·
    refine ⟨78393521988121303042147019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209049391968323474779058717 78393521988121303042147019)
    ·
      refine ⟨117590282982181954563220529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78393521988121303042147019 117590282982181954563220529)
      ·
        refine ⟨88192712236636465922415397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117590282982181954563220529 88192712236636465922415397)
        ·
          refine ⟨16536133544369337360452887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88192712236636465922415397 16536133544369337360452887)
          ·
            refine ⟨24804200316554006040679331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16536133544369337360452887 24804200316554006040679331)
            ·
              refine ⟨37206300474831009061018997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24804200316554006040679331 37206300474831009061018997)
              ·
                refine ⟨3488090669515407099470531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37206300474831009061018997 3488090669515407099470531)
                ·
                  refine ⟨5232136004273110649205797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3488090669515407099470531 5232136004273110649205797)
                  ·
                    refine ⟨981025500801208246726087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5232136004273110649205797 981025500801208246726087)
                    ·
                      rfl

theorem cell23_5731621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 1, 4].length) (baseStart_5731621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731621 prefixEnd_5731621 := by exact prefixLift 5731621
  have htrace : WordTrace (prefixWord ++ tailWord_5731621) baseStart_5731621 baseEnd_5731621 := by
    simpa [prefixWord, tailWord_5731621, baseEnd_5731621] using wordTrace_append hprefix tailTrace_5731621
  have hstable : (prefixWord ++ tailWord_5731621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731621).length < 2 ^ (prefixWord ++ tailWord_5731621).sum := by decide
  have hdescent : baseEnd_5731621 < baseStart_5731621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731634 : List Nat := [3, 2, 1, 1, 4, 1, 3, 2, 6]
def baseStart_5731634 : Nat := 118140960795 + 5731634 * 2 ^ 59
def prefixEnd_5731634 : Nat := 4983230072969 + 3 ^ 40 * 5731634 * 2
def baseEnd_5731634 : Nat := 327009241961348132146189

theorem tailTrace_5731634 : CollatzResearch.WordTrace tailWord_5731634 prefixEnd_5731634 327009241961348132146189 := by
  unfold tailWord_5731634
  simp only [CollatzResearch.WordTrace]
  refine ⟨52262466529319094499820489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139366577411517585332854637 52262466529319094499820489)
  ·
    refine ⟨39196849896989320874865367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52262466529319094499820489 39196849896989320874865367)
    ·
      refine ⟨58795274845483981312298051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39196849896989320874865367 58795274845483981312298051)
      ·
        refine ⟨88192912268225971968447077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58795274845483981312298051 88192912268225971968447077)
        ·
          refine ⟨16536171050292369744083827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88192912268225971968447077 16536171050292369744083827)
          ·
            refine ⟨24804256575438554616125741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16536171050292369744083827 24804256575438554616125741)
            ·
              refine ⟨9301596215789457981047153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24804256575438554616125741 9301596215789457981047153)
              ·
                refine ⟨6976197161842093485785365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9301596215789457981047153 6976197161842093485785365)
                ·
                  refine ⟨327009241961348132146189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6976197161842093485785365 327009241961348132146189)
                  ·
                    rfl

theorem cell23_5731634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_5731634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731634 prefixEnd_5731634 := by exact prefixLift 5731634
  have htrace : WordTrace (prefixWord ++ tailWord_5731634) baseStart_5731634 baseEnd_5731634 := by
    simpa [prefixWord, tailWord_5731634, baseEnd_5731634] using wordTrace_append hprefix tailTrace_5731634
  have hstable : (prefixWord ++ tailWord_5731634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731634).length < 2 ^ (prefixWord ++ tailWord_5731634).sum := by decide
  have hdescent : baseEnd_5731634 < baseStart_5731634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731637 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_5731637 : Nat := 118140960795 + 5731637 * 2 ^ 59
def prefixEnd_5731637 : Nat := 4983230072969 + 3 ^ 40 * 5731637 * 2
def baseEnd_5731637 : Nat := 2943084718094096677578187

theorem tailTrace_5731637 : CollatzResearch.WordTrace tailWord_5731637 prefixEnd_5731637 2943084718094096677578187 := by
  unfold tailWord_5731637
  simp only [CollatzResearch.WordTrace]
  refine ⟨209049975536265509511641165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139366650357510339674427443 209049975536265509511641165)
  ·
    refine ⟨78393740826099566066865437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209049975536265509511641165 78393740826099566066865437)
    ·
      refine ⟨29397652809787337275074539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78393740826099566066865437 29397652809787337275074539)
      ·
        refine ⟨44096479214681005912611809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29397652809787337275074539 44096479214681005912611809)
        ·
          refine ⟨33072359411010754434458857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44096479214681005912611809 33072359411010754434458857)
          ·
            refine ⟨24804269558258065825844143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33072359411010754434458857 24804269558258065825844143)
            ·
              refine ⟨37206404337387098738766215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24804269558258065825844143 37206404337387098738766215)
              ·
                refine ⟨55809606506080648108149323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37206404337387098738766215 55809606506080648108149323)
                ·
                  refine ⟨83714409759120972162223985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55809606506080648108149323 83714409759120972162223985)
                  ·
                    refine ⟨62785807319340729121667989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83714409759120972162223985 62785807319340729121667989)
                    ·
                      refine ⟨2943084718094096677578187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62785807319340729121667989 2943084718094096677578187)
                      ·
                        rfl

theorem cell23_5731637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_5731637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731637 prefixEnd_5731637 := by exact prefixLift 5731637
  have htrace : WordTrace (prefixWord ++ tailWord_5731637) baseStart_5731637 baseEnd_5731637 := by
    simpa [prefixWord, tailWord_5731637, baseEnd_5731637] using wordTrace_append hprefix tailTrace_5731637
  have hstable : (prefixWord ++ tailWord_5731637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731637).length < 2 ^ (prefixWord ++ tailWord_5731637).sum := by decide
  have hdescent : baseEnd_5731637 < baseStart_5731637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731664 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 1, 5]
def baseStart_5731664 : Nat := 118140960795 + 5731664 * 2 ^ 59
def prefixEnd_5731664 : Nat := 4983230072969 + 3 ^ 40 * 5731664 * 2
def baseEnd_5731664 : Nat := 981032860690589357313521

theorem tailTrace_5731664 : CollatzResearch.WordTrace tailWord_5731664 prefixEnd_5731664 981032860690589357313521 := by
  unfold tailWord_5731664
  simp only [CollatzResearch.WordTrace]
  refine ⟨104525480153583846561437023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139367306871445128748582697 104525480153583846561437023)
  ·
    refine ⟨156788220230375769842155535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104525480153583846561437023 156788220230375769842155535)
    ·
      refine ⟨235182330345563654763233303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156788220230375769842155535 235182330345563654763233303)
      ·
        refine ⟨352773495518345482144849955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235182330345563654763233303 352773495518345482144849955)
        ·
          refine ⟨529160243277518223217274933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352773495518345482144849955 529160243277518223217274933)
          ·
            refine ⟨49608772807267333426619525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 529160243277518223217274933 49608772807267333426619525)
            ·
              refine ⟨9301644901362625017491161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49608772807267333426619525 9301644901362625017491161)
              ·
                refine ⟨6976233676021968763118371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9301644901362625017491161 6976233676021968763118371)
                ·
                  refine ⟨10464350514032953144677557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6976233676021968763118371 10464350514032953144677557)
                  ·
                    refine ⟨981032860690589357313521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10464350514032953144677557 981032860690589357313521)
                    ·
                      rfl

theorem cell23_5731664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 1, 5].length) (baseStart_5731664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731664 prefixEnd_5731664 := by exact prefixLift 5731664
  have htrace : WordTrace (prefixWord ++ tailWord_5731664) baseStart_5731664 baseEnd_5731664 := by
    simpa [prefixWord, tailWord_5731664, baseEnd_5731664] using wordTrace_append hprefix tailTrace_5731664
  have hstable : (prefixWord ++ tailWord_5731664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731664).length < 2 ^ (prefixWord ++ tailWord_5731664).sum := by decide
  have hdescent : baseEnd_5731664 < baseStart_5731664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731688 : List Nat := [2, 1, 4, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_5731688 : Nat := 118140960795 + 5731688 * 2 ^ 59
def prefixEnd_5731688 : Nat := 4983230072969 + 3 ^ 40 * 5731688 * 2
def baseEnd_5731688 : Nat := 2943110905607475978040453

theorem tailTrace_5731688 : CollatzResearch.WordTrace tailWord_5731688 prefixEnd_5731688 2943110905607475978040453 := by
  unfold tailWord_5731688
  simp only [CollatzResearch.WordTrace]
  refine ⟨104525917829540372610873859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139367890439387163481165145 104525917829540372610873859)
  ·
    refine ⟨156788876744310558916310789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104525917829540372610873859 156788876744310558916310789)
    ·
      refine ⟨29397914389558229796808273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156788876744310558916310789 29397914389558229796808273)
      ·
        refine ⟨22048435792168672347606205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29397914389558229796808273 22048435792168672347606205)
        ·
          refine ⟨8268163422063252130352327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22048435792168672347606205 8268163422063252130352327)
          ·
            refine ⟨12402245133094878195528491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8268163422063252130352327 12402245133094878195528491)
            ·
              refine ⟨18603367699642317293292737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12402245133094878195528491 18603367699642317293292737)
              ·
                refine ⟨13952525774731737969969553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18603367699642317293292737 13952525774731737969969553)
                ·
                  refine ⟨10464394331048803477477165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13952525774731737969969553 10464394331048803477477165)
                  ·
                    refine ⟨3924147874143301304053937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10464394331048803477477165 3924147874143301304053937)
                    ·
                      refine ⟨2943110905607475978040453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924147874143301304053937 2943110905607475978040453)
                      ·
                        rfl

theorem cell23_5731688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_5731688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731688 prefixEnd_5731688 := by exact prefixLift 5731688
  have htrace : WordTrace (prefixWord ++ tailWord_5731688) baseStart_5731688 baseEnd_5731688 := by
    simpa [prefixWord, tailWord_5731688, baseEnd_5731688] using wordTrace_append hprefix tailTrace_5731688
  have hstable : (prefixWord ++ tailWord_5731688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731688).length < 2 ^ (prefixWord ++ tailWord_5731688).sum := by decide
  have hdescent : baseEnd_5731688 < baseStart_5731688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731697 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_5731697 : Nat := 118140960795 + 5731697 * 2 ^ 59
def prefixEnd_5731697 : Nat := 4983230072969 + 3 ^ 40 * 5731697 * 2
def baseEnd_5731697 : Nat := 2943115526933366442827911

theorem tailTrace_5731697 : CollatzResearch.WordTrace tailWord_5731697 prefixEnd_5731697 2943115526933366442827911 := by
  unfold tailWord_5731697
  simp only [CollatzResearch.WordTrace]
  refine ⟨209052163916048139758825345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139368109277365426505883563 209052163916048139758825345)
  ·
    refine ⟨156789122937036104819119009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209052163916048139758825345 156789122937036104819119009)
    ·
      refine ⟨117591842202777078614339257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156789122937036104819119009 117591842202777078614339257)
      ·
        refine ⟨88193881652082808960754443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117591842202777078614339257 88193881652082808960754443)
        ·
          refine ⟨132290822478124213441131665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88193881652082808960754443 132290822478124213441131665)
          ·
            refine ⟨99218116858593160080848749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132290822478124213441131665 99218116858593160080848749)
            ·
              refine ⟨37206793821972435030318281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99218116858593160080848749 37206793821972435030318281)
              ·
                refine ⟨27905095366479326272738711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37206793821972435030318281 27905095366479326272738711)
                ·
                  refine ⟨41857643049718989409108067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27905095366479326272738711 41857643049718989409108067)
                  ·
                    refine ⟨62786464574578484113662101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41857643049718989409108067 62786464574578484113662101)
                    ·
                      refine ⟨2943115526933366442827911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62786464574578484113662101 2943115526933366442827911)
                      ·
                        rfl

theorem cell23_5731697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_5731697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731697 prefixEnd_5731697 := by exact prefixLift 5731697
  have htrace : WordTrace (prefixWord ++ tailWord_5731697) baseStart_5731697 baseEnd_5731697 := by
    simpa [prefixWord, tailWord_5731697, baseEnd_5731697] using wordTrace_append hprefix tailTrace_5731697
  have hstable : (prefixWord ++ tailWord_5731697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731697).length < 2 ^ (prefixWord ++ tailWord_5731697).sum := by decide
  have hdescent : baseEnd_5731697 < baseStart_5731697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731707 : List Nat := [1, 1, 1, 1, 1, 6, 4, 8]
def baseStart_5731707 : Nat := 118140960795 + 5731707 * 2 ^ 59
def prefixEnd_5731707 : Nat := 4983230072969 + 3 ^ 40 * 5731707 * 2
def baseEnd_5731707 : Nat := 109004468953330051988995

theorem tailTrace_5731707 : CollatzResearch.WordTrace tailWord_5731707 prefixEnd_5731707 109004468953330051988995 := by
  unfold tailWord_5731707
  simp only [CollatzResearch.WordTrace]
  refine ⟨209052528646011911466689375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139368352430674607644459583 209052528646011911466689375)
  ·
    refine ⟨313578792969017867200034063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209052528646011911466689375 313578792969017867200034063)
    ·
      refine ⟨470368189453526800800051095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313578792969017867200034063 470368189453526800800051095)
      ·
        refine ⟨705552284180290201200076643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470368189453526800800051095 705552284180290201200076643)
        ·
          refine ⟨1058328426270435301800114965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 705552284180290201200076643 1058328426270435301800114965)
          ·
            refine ⟨49609144981426654771880389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1058328426270435301800114965 49609144981426654771880389)
            ·
              refine ⟨9301714684017497769727573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49609144981426654771880389 9301714684017497769727573)
              ·
                refine ⟨109004468953330051988995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9301714684017497769727573 109004468953330051988995)
                ·
                  rfl

theorem cell23_5731707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 8].length) (baseStart_5731707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731707 prefixEnd_5731707 := by exact prefixLift 5731707
  have htrace : WordTrace (prefixWord ++ tailWord_5731707) baseStart_5731707 baseEnd_5731707 := by
    simpa [prefixWord, tailWord_5731707, baseEnd_5731707] using wordTrace_append hprefix tailTrace_5731707
  have hstable : (prefixWord ++ tailWord_5731707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731707).length < 2 ^ (prefixWord ++ tailWord_5731707).sum := by decide
  have hdescent : baseEnd_5731707 < baseStart_5731707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731721 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 3, 2, 3]
def baseStart_5731721 : Nat := 118140960795 + 5731721 * 2 ^ 59
def prefixEnd_5731721 : Nat := 4983230072969 + 3 ^ 40 * 5731721 * 2
def baseEnd_5731721 : Nat := 2943127850469074348927801

theorem tailTrace_5731721 : CollatzResearch.WordTrace tailWord_5731721 prefixEnd_5731721 2943127850469074348927801 := by
  unfold tailWord_5731721
  simp only [CollatzResearch.WordTrace]
  refine ⟨209053039267961191857699017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139368692845307461238466011 209053039267961191857699017)
  ·
    refine ⟨156789779450970893893274263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209053039267961191857699017 156789779450970893893274263)
    ·
      refine ⟨235184669176456340839911395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156789779450970893893274263 235184669176456340839911395)
      ·
        refine ⟨352777003764684511259867093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235184669176456340839911395 352777003764684511259867093)
        ·
          refine ⟨8268211025734793232653135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 352777003764684511259867093 8268211025734793232653135)
          ·
            refine ⟨12402316538602189848979703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8268211025734793232653135 12402316538602189848979703)
            ·
              refine ⟨18603474807903284773469555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12402316538602189848979703 18603474807903284773469555)
              ·
                refine ⟨27905212211854927160204333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18603474807903284773469555 27905212211854927160204333)
                ·
                  refine ⟨10464454579445597685076625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27905212211854927160204333 10464454579445597685076625)
                  ·
                    refine ⟨7848340934584198263807469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10464454579445597685076625 7848340934584198263807469)
                    ·
                      refine ⟨2943127850469074348927801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7848340934584198263807469 2943127850469074348927801)
                      ·
                        rfl

theorem cell23_5731721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 3, 2, 3].length) (baseStart_5731721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731721 prefixEnd_5731721 := by exact prefixLift 5731721
  have htrace : WordTrace (prefixWord ++ tailWord_5731721) baseStart_5731721 baseEnd_5731721 := by
    simpa [prefixWord, tailWord_5731721, baseEnd_5731721] using wordTrace_append hprefix tailTrace_5731721
  have hstable : (prefixWord ++ tailWord_5731721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731721).length < 2 ^ (prefixWord ++ tailWord_5731721).sum := by decide
  have hdescent : baseEnd_5731721 < baseStart_5731721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731738 : List Nat := [3, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3]
def baseStart_5731738 : Nat := 118140960795 + 5731738 * 2 ^ 59
def prefixEnd_5731738 : Nat := 4983230072969 + 3 ^ 40 * 5731738 * 2
def baseEnd_5731738 : Nat := 2943136579640200782415223

theorem tailTrace_5731738 : CollatzResearch.WordTrace tailWord_5731738 prefixEnd_5731738 2943136579640200782415223 := by
  unfold tailWord_5731738
  simp only [CollatzResearch.WordTrace]
  refine ⟨52263414827224900940266967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139369106205933069174045245 52263414827224900940266967)
  ·
    refine ⟨78395122240837351410400451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52263414827224900940266967 78395122240837351410400451)
    ·
      refine ⟨117592683361256027115600677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78395122240837351410400451 117592683361256027115600677)
      ·
        refine ⟨22048628130235505084175127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117592683361256027115600677 22048628130235505084175127)
        ·
          refine ⟨33072942195353257626262691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22048628130235505084175127 33072942195353257626262691)
          ·
            refine ⟨49609413293029886439394037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33072942195353257626262691 49609413293029886439394037)
            ·
              refine ⟨4650882496221551853693191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49609413293029886439394037 4650882496221551853693191)
              ·
                refine ⟨6976323744332327780539787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4650882496221551853693191 6976323744332327780539787)
                ·
                  refine ⟨10464485616498491670809681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6976323744332327780539787 10464485616498491670809681)
                  ·
                    refine ⟨7848364212373868753107261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10464485616498491670809681 7848364212373868753107261)
                    ·
                      refine ⟨2943136579640200782415223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7848364212373868753107261 2943136579640200782415223)
                      ·
                        rfl

theorem cell23_5731738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_5731738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731738 prefixEnd_5731738 := by exact prefixLift 5731738
  have htrace : WordTrace (prefixWord ++ tailWord_5731738) baseStart_5731738 baseEnd_5731738 := by
    simpa [prefixWord, tailWord_5731738, baseEnd_5731738] using wordTrace_append hprefix tailTrace_5731738
  have hstable : (prefixWord ++ tailWord_5731738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731738).length < 2 ^ (prefixWord ++ tailWord_5731738).sum := by decide
  have hdescent : baseEnd_5731738 < baseStart_5731738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731761 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 5, 3, 2]
def baseStart_5731761 : Nat := 118140960795 + 5731761 * 2 ^ 59
def prefixEnd_5731761 : Nat := 4983230072969 + 3 ^ 40 * 5731761 * 2
def baseEnd_5731761 : Nat := 2943148389695254192427617

theorem tailTrace_5731761 : CollatzResearch.WordTrace tailWord_5731761 prefixEnd_5731761 2943148389695254192427617 := by
  unfold tailWord_5731761
  simp only [CollatzResearch.WordTrace]
  refine ⟨209054498187816278689155137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139369665458544185792770091 209054498187816278689155137)
  ·
    refine ⟨156790873640862209016866353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209054498187816278689155137 156790873640862209016866353)
    ·
      refine ⟨117593155230646656762649765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156790873640862209016866353 117593155230646656762649765)
      ·
        refine ⟨22048716605746248142996831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117593155230646656762649765 22048716605746248142996831)
        ·
          refine ⟨33073074908619372214495247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22048716605746248142996831 33073074908619372214495247)
          ·
            refine ⟨49609612362929058321742871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33073074908619372214495247 49609612362929058321742871)
            ·
              refine ⟨74414418544393587482614307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49609612362929058321742871 74414418544393587482614307)
              ·
                refine ⟨111621627816590381223921461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74414418544393587482614307 111621627816590381223921461)
                ·
                  refine ⟨10464527607805348239742637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111621627816590381223921461 10464527607805348239742637)
                  ·
                    refine ⟨3924197852927005589903489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10464527607805348239742637 3924197852927005589903489)
                    ·
                      refine ⟨2943148389695254192427617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924197852927005589903489 2943148389695254192427617)
                      ·
                        rfl

theorem cell23_5731761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_5731761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731761 prefixEnd_5731761 := by exact prefixLift 5731761
  have htrace : WordTrace (prefixWord ++ tailWord_5731761) baseStart_5731761 baseEnd_5731761 := by
    simpa [prefixWord, tailWord_5731761, baseEnd_5731761] using wordTrace_append hprefix tailTrace_5731761
  have hstable : (prefixWord ++ tailWord_5731761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731761).length < 2 ^ (prefixWord ++ tailWord_5731761).sum := by decide
  have hdescent : baseEnd_5731761 < baseStart_5731761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731774 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_5731774 : Nat := 118140960795 + 5731774 * 2 ^ 59
def prefixEnd_5731774 : Nat := 4983230072969 + 3 ^ 40 * 5731774 * 2
def baseEnd_5731774 : Nat := 2943155064943762641565057

theorem tailTrace_5731774 : CollatzResearch.WordTrace tailWord_5731774 prefixEnd_5731774 2943155064943762641565057 := by
  unfold tailWord_5731774
  simp only [CollatzResearch.WordTrace]
  refine ⟨26131871542096147738672297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139369981557846121272918917 26131871542096147738672297)
  ·
    refine ⟨19598903656572110804004223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26131871542096147738672297 19598903656572110804004223)
    ·
      refine ⟨29398355484858166206006335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19598903656572110804004223 29398355484858166206006335)
      ·
        refine ⟨44097533227287249309009503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29398355484858166206006335 44097533227287249309009503)
        ·
          refine ⟨66146299840930873963514255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44097533227287249309009503 66146299840930873963514255)
          ·
            refine ⟨99219449761396310945271383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66146299840930873963514255 99219449761396310945271383)
            ·
              refine ⟨148829174642094466417907075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99219449761396310945271383 148829174642094466417907075)
              ·
                refine ⟨223243761963141699626860613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148829174642094466417907075 223243761963141699626860613)
                ·
                  refine ⟨41858205368089068680036365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223243761963141699626860613 41858205368089068680036365)
                  ·
                    refine ⟨15696827013033400755013637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41858205368089068680036365 15696827013033400755013637)
                    ·
                      refine ⟨2943155064943762641565057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15696827013033400755013637 2943155064943762641565057)
                      ·
                        rfl

theorem cell23_5731774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_5731774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731774 prefixEnd_5731774 := by exact prefixLift 5731774
  have htrace : WordTrace (prefixWord ++ tailWord_5731774) baseStart_5731774 baseEnd_5731774 := by
    simpa [prefixWord, tailWord_5731774, baseEnd_5731774] using wordTrace_append hprefix tailTrace_5731774
  have hstable : (prefixWord ++ tailWord_5731774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731774).length < 2 ^ (prefixWord ++ tailWord_5731774).sum := by decide
  have hdescent : baseEnd_5731774 < baseStart_5731774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731791 : List Nat := [1, 1, 2, 1, 1, 4, 4, 2, 1, 4, 2]
def baseStart_5731791 : Nat := 118140960795 + 5731791 * 2 ^ 59
def prefixEnd_5731791 : Nat := 4983230072969 + 3 ^ 40 * 5731791 * 2
def baseEnd_5731791 : Nat := 2943163794114889075052479

theorem tailTrace_5731791 : CollatzResearch.WordTrace tailWord_5731791 prefixEnd_5731791 2943163794114889075052479 := by
  unfold tailWord_5731791
  simp only [CollatzResearch.WordTrace]
  refine ⟨209055592377707593812747227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139370394918471729208498151 209055592377707593812747227)
  ·
    refine ⟨313583388566561390719120841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209055592377707593812747227 313583388566561390719120841)
    ·
      refine ⟨235187541424921043039340631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313583388566561390719120841 235187541424921043039340631)
      ·
        refine ⟨352781312137381564559010947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235187541424921043039340631 352781312137381564559010947)
        ·
          refine ⟨529171968206072346838516421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352781312137381564559010947 529171968206072346838516421)
          ·
            refine ⟨99219744038638565032221829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 529171968206072346838516421 99219744038638565032221829)
            ·
              refine ⟨18603702007244730943541593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99219744038638565032221829 18603702007244730943541593)
              ·
                refine ⟨13952776505433548207656195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18603702007244730943541593 13952776505433548207656195)
                ·
                  refine ⟨20929164758150322311484293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13952776505433548207656195 20929164758150322311484293)
                  ·
                    refine ⟨3924218392153185433403305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20929164758150322311484293 3924218392153185433403305)
                    ·
                      refine ⟨2943163794114889075052479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924218392153185433403305 2943163794114889075052479)
                      ·
                        rfl

theorem cell23_5731791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 4, 2].length) (baseStart_5731791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731791 prefixEnd_5731791 := by exact prefixLift 5731791
  have htrace : WordTrace (prefixWord ++ tailWord_5731791) baseStart_5731791 baseEnd_5731791 := by
    simpa [prefixWord, tailWord_5731791, baseEnd_5731791] using wordTrace_append hprefix tailTrace_5731791
  have hstable : (prefixWord ++ tailWord_5731791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731791).length < 2 ^ (prefixWord ++ tailWord_5731791).sum := by decide
  have hdescent : baseEnd_5731791 < baseStart_5731791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731808 : List Nat := [2, 1, 1, 3, 1, 1, 2, 6, 2, 2, 2]
def baseStart_5731808 : Nat := 118140960795 + 5731808 * 2 ^ 59
def prefixEnd_5731808 : Nat := 4983230072969 + 3 ^ 40 * 5731808 * 2
def baseEnd_5731808 : Nat := 2943172523286015508539901

theorem tailTrace_5731808 : CollatzResearch.WordTrace tailWord_5731808 prefixEnd_5731808 2943172523286015508539901 := by
  unfold tailWord_5731808
  simp only [CollatzResearch.WordTrace]
  refine ⟨104528106209323002858058039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139370808279097337144077385 104528106209323002858058039)
  ·
    refine ⟨156792159313984504287087059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104528106209323002858058039 156792159313984504287087059)
    ·
      refine ⟨235188238970976756430630589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156792159313984504287087059 235188238970976756430630589)
      ·
        refine ⟨88195589614116283661486471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235188238970976756430630589 88195589614116283661486471)
        ·
          refine ⟨132293384421174425492229707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88195589614116283661486471 132293384421174425492229707)
          ·
            refine ⟨198440076631761638238344561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132293384421174425492229707 198440076631761638238344561)
            ·
              refine ⟨148830057473821228678758421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198440076631761638238344561 148830057473821228678758421)
              ·
                refine ⟨6976408944085370094316801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148830057473821228678758421 6976408944085370094316801)
                ·
                  refine ⟨5232306708064027570737601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6976408944085370094316801 5232306708064027570737601)
                  ·
                    refine ⟨3924230031048020678053201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5232306708064027570737601 3924230031048020678053201)
                    ·
                      refine ⟨2943172523286015508539901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924230031048020678053201 2943172523286015508539901)
                      ·
                        rfl

theorem cell23_5731808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_5731808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731808 prefixEnd_5731808 := by exact prefixLift 5731808
  have htrace : WordTrace (prefixWord ++ tailWord_5731808) baseStart_5731808 baseEnd_5731808 := by
    simpa [prefixWord, tailWord_5731808, baseEnd_5731808] using wordTrace_append hprefix tailTrace_5731808
  have hstable : (prefixWord ++ tailWord_5731808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731808).length < 2 ^ (prefixWord ++ tailWord_5731808).sum := by decide
  have hdescent : baseEnd_5731808 < baseStart_5731808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731861 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 2, 5]
def baseStart_5731861 : Nat := 118140960795 + 5731861 * 2 ^ 59
def prefixEnd_5731861 : Nat := 4983230072969 + 3 ^ 40 * 5731861 * 2
def baseEnd_5731861 : Nat := 981066579253567933725719

theorem tailTrace_5731861 : CollatzResearch.WordTrace tailWord_5731861 prefixEnd_5731861 981066579253567933725719 := by
  unfold tailWord_5731861
  simp only [CollatzResearch.WordTrace]
  refine ⟨209058145487453995767795437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139372096991635997178530291 209058145487453995767795437)
  ·
    refine ⟨78396804557795248412923289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209058145487453995767795437 78396804557795248412923289)
    ·
      refine ⟨58797603418346436309692467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78396804557795248412923289 58797603418346436309692467)
      ·
        refine ⟨88196405127519654464538701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58797603418346436309692467 88196405127519654464538701)
        ·
          refine ⟨33073651922819870424202013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88196405127519654464538701 33073651922819870424202013)
          ·
            refine ⟨12402619471057451409075755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33073651922819870424202013 12402619471057451409075755)
            ·
              refine ⟨18603929206586177113613633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12402619471057451409075755 18603929206586177113613633)
              ·
                refine ⟨13952946904939632835210225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18603929206586177113613633 13952946904939632835210225)
                ·
                  refine ⟨10464710178704724626407669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13952946904939632835210225 10464710178704724626407669)
                  ·
                    refine ⟨981066579253567933725719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10464710178704724626407669 981066579253567933725719)
                    ·
                      rfl

theorem cell23_5731861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_5731861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731861 prefixEnd_5731861 := by exact prefixLift 5731861
  have htrace : WordTrace (prefixWord ++ tailWord_5731861) baseStart_5731861 baseEnd_5731861 := by
    simpa [prefixWord, tailWord_5731861, baseEnd_5731861] using wordTrace_append hprefix tailTrace_5731861
  have hstable : (prefixWord ++ tailWord_5731861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731861).length < 2 ^ (prefixWord ++ tailWord_5731861).sum := by decide
  have hdescent : baseEnd_5731861 < baseStart_5731861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731921 : List Nat := [1, 2, 2, 1, 3, 2, 4, 2, 6]
def baseStart_5731921 : Nat := 118140960795 + 5731921 * 2 ^ 59
def prefixEnd_5731921 : Nat := 4983230072969 + 3 ^ 40 * 5731921 * 2
def baseEnd_5731921 : Nat := 327025616288885951825209

theorem tailTrace_5731921 : CollatzResearch.WordTrace tailWord_5731921 prefixEnd_5731921 327025616288885951825209 := by
  unfold tailWord_5731921
  simp only [CollatzResearch.WordTrace]
  refine ⟨209060333867236626014979617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139373555911491084009986411 209060333867236626014979617)
  ·
    refine ⟨156795250400427469511234713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209060333867236626014979617 156795250400427469511234713)
    ·
      refine ⟨117596437800320602133426035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156795250400427469511234713 117596437800320602133426035)
      ·
        refine ⟨176394656700480903200139053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117596437800320602133426035 176394656700480903200139053)
        ·
          refine ⟨66147996262680338700052145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176394656700480903200139053 66147996262680338700052145)
          ·
            refine ⟨49610997197010254025039109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66147996262680338700052145 49610997197010254025039109)
            ·
              refine ⟨9302061974439422629694833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49610997197010254025039109 9302061974439422629694833)
              ·
                refine ⟨6976546480829566972271125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9302061974439422629694833 6976546480829566972271125)
                ·
                  refine ⟨327025616288885951825209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6976546480829566972271125 327025616288885951825209)
                  ·
                    rfl

theorem cell23_5731921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 2, 6].length) (baseStart_5731921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731921 prefixEnd_5731921 := by exact prefixLift 5731921
  have htrace : WordTrace (prefixWord ++ tailWord_5731921) baseStart_5731921 baseEnd_5731921 := by
    simpa [prefixWord, tailWord_5731921, baseEnd_5731921] using wordTrace_append hprefix tailTrace_5731921
  have hstable : (prefixWord ++ tailWord_5731921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731921).length < 2 ^ (prefixWord ++ tailWord_5731921).sum := by decide
  have hdescent : baseEnd_5731921 < baseStart_5731921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731951 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 1, 5]
def baseStart_5731951 : Nat := 118140960795 + 5731951 * 2 ^ 59
def prefixEnd_5731951 : Nat := 4983230072969 + 3 ^ 40 * 5731951 * 2
def baseEnd_5731951 : Nat := 981081983673202816350581

theorem tailTrace_5731951 : CollatzResearch.WordTrace tailWord_5731951 prefixEnd_5731951 981081983673202816350581 := by
  unfold tailWord_5731951
  simp only [CollatzResearch.WordTrace]
  refine ⟨209061428057127941138571707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139374285371418627425714471 209061428057127941138571707)
  ·
    refine ⟨313592142085691911707857561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209061428057127941138571707 313592142085691911707857561)
    ·
      refine ⟨235194106564268933780893171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313592142085691911707857561 235194106564268933780893171)
      ·
        refine ⟨352791159846403400671339757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235194106564268933780893171 352791159846403400671339757)
        ·
          refine ⟨132296684942401275251752409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352791159846403400671339757 132296684942401275251752409)
          ·
            refine ⟨99222513706800956438814307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132296684942401275251752409 99222513706800956438814307)
            ·
              refine ⟨148833770560201434658221461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99222513706800956438814307 148833770560201434658221461)
              ·
                refine ⟨6976582995009442249604131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148833770560201434658221461 6976582995009442249604131)
                ·
                  refine ⟨10464874492514163374406197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6976582995009442249604131 10464874492514163374406197)
                  ·
                    refine ⟨981081983673202816350581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10464874492514163374406197 981081983673202816350581)
                    ·
                      rfl

theorem cell23_5731951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 5].length) (baseStart_5731951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731951 prefixEnd_5731951 := by exact prefixLift 5731951
  have htrace : WordTrace (prefixWord ++ tailWord_5731951) baseStart_5731951 baseEnd_5731951 := by
    simpa [prefixWord, tailWord_5731951, baseEnd_5731951] using wordTrace_append hprefix tailTrace_5731951
  have hstable : (prefixWord ++ tailWord_5731951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731951).length < 2 ^ (prefixWord ++ tailWord_5731951).sum := by decide
  have hdescent : baseEnd_5731951 < baseStart_5731951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731982 : List Nat := [4, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3]
def baseStart_5731982 : Nat := 118140960795 + 5731982 * 2 ^ 59
def prefixEnd_5731982 : Nat := 4983230072969 + 3 ^ 40 * 5731982 * 2
def baseEnd_5731982 : Nat := 2943261868919897827764101

theorem tailTrace_5731982 : CollatzResearch.WordTrace tailWord_5731982 prefixEnd_5731982 2943261868919897827764101 := by
  unfold tailWord_5731982
  simp only [CollatzResearch.WordTrace]
  refine ⟨26132819840001954179118775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139375039146677088955300133 26132819840001954179118775)
  ·
    refine ⟨39199229760002931268678163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26132819840001954179118775 39199229760002931268678163)
    ·
      refine ⟨58798844640004396903017245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39199229760002931268678163 58798844640004396903017245)
      ·
        refine ⟨22049566740001648838631467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58798844640004396903017245 22049566740001648838631467)
        ·
          refine ⟨33074350110002473257947201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22049566740001648838631467 33074350110002473257947201)
          ·
            refine ⟨24805762582501854943460401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33074350110002473257947201 24805762582501854943460401)
            ·
              refine ⟨18604321936876391207595301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24805762582501854943460401 18604321936876391207595301)
              ·
                refine ⟨3488310363164323351424119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18604321936876391207595301 3488310363164323351424119)
                ·
                  refine ⟨5232465544746485027136179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3488310363164323351424119 5232465544746485027136179)
                  ·
                    refine ⟨7848698317119727540704269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5232465544746485027136179 7848698317119727540704269)
                    ·
                      refine ⟨2943261868919897827764101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7848698317119727540704269 2943261868919897827764101)
                      ·
                        rfl

theorem cell23_5731982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_5731982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731982 prefixEnd_5731982 := by exact prefixLift 5731982
  have htrace : WordTrace (prefixWord ++ tailWord_5731982) baseStart_5731982 baseEnd_5731982 := by
    simpa [prefixWord, tailWord_5731982, baseEnd_5731982] using wordTrace_append hprefix tailTrace_5731982
  have hstable : (prefixWord ++ tailWord_5731982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731982).length < 2 ^ (prefixWord ++ tailWord_5731982).sum := by decide
  have hdescent : baseEnd_5731982 < baseStart_5731982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5731991 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_5731991 : Nat := 118140960795 + 5731991 * 2 ^ 59
def prefixEnd_5731991 : Nat := 4983230072969 + 3 ^ 40 * 5731991 * 2
def baseEnd_5731991 : Nat := 2943266490245788292551559

theorem tailTrace_5731991 : CollatzResearch.WordTrace tailWord_5731991 prefixEnd_5731991 2943266490245788292551559 := by
  unfold tailWord_5731991
  simp only [CollatzResearch.WordTrace]
  refine ⟨209062886976983027970027827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139375257984655351980018551 209062886976983027970027827)
  ·
    refine ⟨313594330465474541955041741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209062886976983027970027827 313594330465474541955041741)
    ·
      refine ⟨117597873924552953233140653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313594330465474541955041741 117597873924552953233140653)
      ·
        refine ⟨44099202721707357462427745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117597873924552953233140653 44099202721707357462427745)
        ·
          refine ⟨33074402041280518096820809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44099202721707357462427745 33074402041280518096820809)
          ·
            refine ⟨24805801530960388572615607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33074402041280518096820809 24805801530960388572615607)
            ·
              refine ⟨37208702296440582858923411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24805801530960388572615607 37208702296440582858923411)
              ·
                refine ⟨55813053444660874288385117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37208702296440582858923411 55813053444660874288385117)
                ·
                  refine ⟨20929895041747827858144419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55813053444660874288385117 20929895041747827858144419)
                  ·
                    refine ⟨31394842562621741787216629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20929895041747827858144419 31394842562621741787216629)
                    ·
                      refine ⟨2943266490245788292551559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31394842562621741787216629 2943266490245788292551559)
                      ·
                        rfl

theorem cell23_5731991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_5731991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5731991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5731991 prefixEnd_5731991 := by exact prefixLift 5731991
  have htrace : WordTrace (prefixWord ++ tailWord_5731991) baseStart_5731991 baseEnd_5731991 := by
    simpa [prefixWord, tailWord_5731991, baseEnd_5731991] using wordTrace_append hprefix tailTrace_5731991
  have hstable : (prefixWord ++ tailWord_5731991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5731991).length < 2 ^ (prefixWord ++ tailWord_5731991).sum := by decide
  have hdescent : baseEnd_5731991 < baseStart_5731991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5731991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732002 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_5732002 : Nat := 118140960795 + 5732002 * 2 ^ 59
def prefixEnd_5732002 : Nat := 4983230072969 + 3 ^ 40 * 5732002 * 2
def baseEnd_5732002 : Nat := 981090712844329249838003

theorem tailTrace_5732002 : CollatzResearch.WordTrace tailWord_5732002 prefixEnd_5732002 981090712844329249838003 := by
  unfold tailWord_5732002
  simp only [CollatzResearch.WordTrace]
  refine ⟨52265822044985794212169565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139375525453295451232452173 52265822044985794212169565)
  ·
    refine ⟨19599683266869672829563587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52265822044985794212169565 19599683266869672829563587)
    ·
      refine ⟨29399524900304509244345381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19599683266869672829563587 29399524900304509244345381)
      ·
        refine ⟨5512410918807095483314759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29399524900304509244345381 5512410918807095483314759)
        ·
          refine ⟨8268616378210643224972139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5512410918807095483314759 8268616378210643224972139)
          ·
            refine ⟨12402924567315964837458209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8268616378210643224972139 12402924567315964837458209)
            ·
              refine ⟨9302193425486973628093657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12402924567315964837458209 9302193425486973628093657)
              ·
                refine ⟨6976645069115230221070243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9302193425486973628093657 6976645069115230221070243)
                ·
                  refine ⟨10464967603672845331605365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6976645069115230221070243 10464967603672845331605365)
                  ·
                    refine ⟨981090712844329249838003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10464967603672845331605365 981090712844329249838003)
                    ·
                      rfl

theorem cell23_5732002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_5732002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732002 prefixEnd_5732002 := by exact prefixLift 5732002
  have htrace : WordTrace (prefixWord ++ tailWord_5732002) baseStart_5732002 baseEnd_5732002 := by
    simpa [prefixWord, tailWord_5732002, baseEnd_5732002] using wordTrace_append hprefix tailTrace_5732002
  have hstable : (prefixWord ++ tailWord_5732002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732002).length < 2 ^ (prefixWord ++ tailWord_5732002).sum := by decide
  have hdescent : baseEnd_5732002 < baseStart_5732002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732005 : List Nat := [1, 3, 1, 2, 1, 2, 4, 2, 3, 2, 2]
def baseStart_5732005 : Nat := 118140960795 + 5732005 * 2 ^ 59
def prefixEnd_5732005 : Nat := 4983230072969 + 3 ^ 40 * 5732005 * 2
def baseEnd_5732005 : Nat := 2943273678974951237776495

theorem tailTrace_5732005 : CollatzResearch.WordTrace tailWord_5732005 prefixEnd_5732005 2943273678974951237776495 := by
  unfold tailWord_5732005
  simp only [CollatzResearch.WordTrace]
  refine ⟨209063397598932308361037469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139375598399288205574024979 209063397598932308361037469)
  ·
    refine ⟨78398774099599615635389051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209063397598932308361037469 78398774099599615635389051)
    ·
      refine ⟨117598161149399423453083577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78398774099599615635389051 117598161149399423453083577)
      ·
        refine ⟨88198620862049567589812683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117598161149399423453083577 88198620862049567589812683)
        ·
          refine ⟨132297931293074351384719025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88198620862049567589812683 132297931293074351384719025)
          ·
            refine ⟨99223448469805763538539269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132297931293074351384719025 99223448469805763538539269)
            ·
              refine ⟨18604396588088580663476113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99223448469805763538539269 18604396588088580663476113)
              ·
                refine ⟨13953297441066435497607085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18604396588088580663476113 13953297441066435497607085)
                ·
                  refine ⟨5232486540399913311602657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13953297441066435497607085 5232486540399913311602657)
                  ·
                    refine ⟨3924364905299934983701993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5232486540399913311602657 3924364905299934983701993)
                    ·
                      refine ⟨2943273678974951237776495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924364905299934983701993 2943273678974951237776495)
                      ·
                        rfl

theorem cell23_5732005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_5732005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732005 prefixEnd_5732005 := by exact prefixLift 5732005
  have htrace : WordTrace (prefixWord ++ tailWord_5732005) baseStart_5732005 baseEnd_5732005 := by
    simpa [prefixWord, tailWord_5732005, baseEnd_5732005] using wordTrace_append hprefix tailTrace_5732005
  have hstable : (prefixWord ++ tailWord_5732005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732005).length < 2 ^ (prefixWord ++ tailWord_5732005).sum := by decide
  have hdescent : baseEnd_5732005 < baseStart_5732005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732022 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_5732022 : Nat := 118140960795 + 5732022 * 2 ^ 59
def prefixEnd_5732022 : Nat := 4983230072969 + 3 ^ 40 * 5732022 * 2
def baseEnd_5732022 : Nat := 2943282408146077671263917

theorem tailTrace_5732022 : CollatzResearch.WordTrace tailWord_5732022 prefixEnd_5732022 2943282408146077671263917 := by
  unfold tailWord_5732022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13066501102491920016525395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139376011759913813509604213 13066501102491920016525395)
  ·
    refine ⟨19599751653737880024788093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13066501102491920016525395 19599751653737880024788093)
    ·
      refine ⟨7349906870151705009295535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19599751653737880024788093 7349906870151705009295535)
      ·
        refine ⟨11024860305227557513943303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7349906870151705009295535 11024860305227557513943303)
        ·
          refine ⟨16537290457841336270914955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11024860305227557513943303 16537290457841336270914955)
          ·
            refine ⟨24805935686762004406372433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16537290457841336270914955 24805935686762004406372433)
            ·
              refine ⟨18604451765071503304779325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24805935686762004406372433 18604451765071503304779325)
              ·
                refine ⟨6976669411901813739292247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18604451765071503304779325 6976669411901813739292247)
                ·
                  refine ⟨10465004117852720608938371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6976669411901813739292247 10465004117852720608938371)
                  ·
                    refine ⟨15697506176779080913407557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10465004117852720608938371 15697506176779080913407557)
                    ·
                      refine ⟨2943282408146077671263917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15697506176779080913407557 2943282408146077671263917)
                      ·
                        rfl

theorem cell23_5732022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_5732022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732022 prefixEnd_5732022 := by exact prefixLift 5732022
  have htrace : WordTrace (prefixWord ++ tailWord_5732022) baseStart_5732022 baseEnd_5732022 := by
    simpa [prefixWord, tailWord_5732022, baseEnd_5732022] using wordTrace_append hprefix tailTrace_5732022
  have hstable : (prefixWord ++ tailWord_5732022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732022).length < 2 ^ (prefixWord ++ tailWord_5732022).sum := by decide
  have hdescent : baseEnd_5732022 < baseStart_5732022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732039 : List Nat := [1, 1, 4, 1, 1, 1, 7, 2, 1, 2, 2]
def baseStart_5732039 : Nat := 118140960795 + 5732039 * 2 ^ 59
def prefixEnd_5732039 : Nat := 4983230072969 + 3 ^ 40 * 5732039 * 2
def baseEnd_5732039 : Nat := 2943291137317204104751339

theorem tailTrace_5732039 : CollatzResearch.WordTrace tailWord_5732039 prefixEnd_5732039 2943291137317204104751339 := by
  unfold tailWord_5732039
  simp only [CollatzResearch.WordTrace]
  refine ⟨209064637680809132167775171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139376425120539421445183447 209064637680809132167775171)
  ·
    refine ⟨313596956521213698251662757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209064637680809132167775171 313596956521213698251662757)
    ·
      refine ⟨58799429347727568422186767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313596956521213698251662757 58799429347727568422186767)
      ·
        refine ⟨88199144021591352633280151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58799429347727568422186767 88199144021591352633280151)
        ·
          refine ⟨132298716032387028949920227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88199144021591352633280151 132298716032387028949920227)
          ·
            refine ⟨198448074048580543424880341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132298716032387028949920227 198448074048580543424880341)
            ·
              refine ⟨4651126735513606486520633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 198448074048580543424880341 4651126735513606486520633)
              ·
                refine ⟨3488345051635204864890475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4651126735513606486520633 3488345051635204864890475)
                ·
                  refine ⟨5232517577452807297335713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3488345051635204864890475 5232517577452807297335713)
                  ·
                    refine ⟨3924388183089605473001785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5232517577452807297335713 3924388183089605473001785)
                    ·
                      refine ⟨2943291137317204104751339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924388183089605473001785 2943291137317204104751339)
                      ·
                        rfl

theorem cell23_5732039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_5732039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732039 prefixEnd_5732039 := by exact prefixLift 5732039
  have htrace : WordTrace (prefixWord ++ tailWord_5732039) baseStart_5732039 baseEnd_5732039 := by
    simpa [prefixWord, tailWord_5732039, baseEnd_5732039] using wordTrace_append hprefix tailTrace_5732039
  have hstable : (prefixWord ++ tailWord_5732039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732039).length < 2 ^ (prefixWord ++ tailWord_5732039).sum := by decide
  have hdescent : baseEnd_5732039 < baseStart_5732039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732045 : List Nat := [1, 6, 2, 1, 1, 2, 2, 8]
def baseStart_5732045 : Nat := 118140960795 + 5732045 * 2 ^ 59
def prefixEnd_5732045 : Nat := 4983230072969 + 3 ^ 40 * 5732045 * 2
def baseEnd_5732045 : Nat := 109010896970412262269493

theorem tailTrace_5732045 : CollatzResearch.WordTrace tailWord_5732045 prefixEnd_5732045 109010896970412262269493 := by
  unfold tailWord_5732045
  simp only [CollatzResearch.WordTrace]
  refine ⟨209064856518787395192493589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139376571012524930128329059 209064856518787395192493589)
  ·
    refine ⟨9799915149318159149648137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 209064856518787395192493589 9799915149318159149648137)
    ·
      refine ⟨7349936361988619362236103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9799915149318159149648137 7349936361988619362236103)
      ·
        refine ⟨11024904542982929043354155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7349936361988619362236103 11024904542982929043354155)
        ·
          refine ⟨16537356814474393565031233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11024904542982929043354155 16537356814474393565031233)
          ·
            refine ⟨12403017610855795173773425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16537356814474393565031233 12403017610855795173773425)
            ·
              refine ⟨9302263208141846380330069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12403017610855795173773425 9302263208141846380330069)
              ·
                refine ⟨109010896970412262269493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9302263208141846380330069 109010896970412262269493)
                ·
                  rfl

theorem cell23_5732045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 8].length) (baseStart_5732045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732045 prefixEnd_5732045 := by exact prefixLift 5732045
  have htrace : WordTrace (prefixWord ++ tailWord_5732045) baseStart_5732045 baseEnd_5732045 := by
    simpa [prefixWord, tailWord_5732045, baseEnd_5732045] using wordTrace_append hprefix tailTrace_5732045
  have hstable : (prefixWord ++ tailWord_5732045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732045).length < 2 ^ (prefixWord ++ tailWord_5732045).sum := by decide
  have hdescent : baseEnd_5732045 < baseStart_5732045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732055 : List Nat := [1, 1, 3, 2, 1, 3, 3, 3, 2, 1, 3]
def baseStart_5732055 : Nat := 118140960795 + 5732055 * 2 ^ 59
def prefixEnd_5732055 : Nat := 4983230072969 + 3 ^ 40 * 5732055 * 2
def baseEnd_5732055 : Nat := 2943299353007676042151265

theorem tailTrace_5732055 : CollatzResearch.WordTrace tailWord_5732055 prefixEnd_5732055 2943299353007676042151265 := by
  unfold tailWord_5732055
  simp only [CollatzResearch.WordTrace]
  refine ⟨209065221248751166900357619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139376814165834111266905079 209065221248751166900357619)
  ·
    refine ⟨313597831873126750350536429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209065221248751166900357619 313597831873126750350536429)
    ·
      refine ⟨117599186952422531381451161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313597831873126750350536429 117599186952422531381451161)
      ·
        refine ⟨88199390214316898536088371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117599186952422531381451161 88199390214316898536088371)
        ·
          refine ⟨132299085321475347804132557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88199390214316898536088371 132299085321475347804132557)
          ·
            refine ⟨49612156995553255426549709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132299085321475347804132557 49612156995553255426549709)
            ·
              refine ⟨18604558873332470784956141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49612156995553255426549709 18604558873332470784956141)
              ·
                refine ⟨6976709577499676544358553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18604558873332470784956141 6976709577499676544358553)
                ·
                  refine ⟨5232532183124757408268915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6976709577499676544358553 5232532183124757408268915)
                  ·
                    refine ⟨7848798274687136112403373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5232532183124757408268915 7848798274687136112403373)
                    ·
                      refine ⟨2943299353007676042151265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7848798274687136112403373 2943299353007676042151265)
                      ·
                        rfl

theorem cell23_5732055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_5732055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732055 prefixEnd_5732055 := by exact prefixLift 5732055
  have htrace : WordTrace (prefixWord ++ tailWord_5732055) baseStart_5732055 baseEnd_5732055 := by
    simpa [prefixWord, tailWord_5732055, baseEnd_5732055] using wordTrace_append hprefix tailTrace_5732055
  have hstable : (prefixWord ++ tailWord_5732055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732055).length < 2 ^ (prefixWord ++ tailWord_5732055).sum := by decide
  have hdescent : baseEnd_5732055 < baseStart_5732055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732095 : List Nat := [1, 1, 2, 2, 1, 3, 2, 3, 4, 2, 2]
def baseStart_5732095 : Nat := 118140960795 + 5732095 * 2 ^ 59
def prefixEnd_5732095 : Nat := 4983230072969 + 3 ^ 40 * 5732095 * 2
def baseEnd_5732095 : Nat := 2943319892233855885651081

theorem tailTrace_5732095 : CollatzResearch.WordTrace tailWord_5732095 prefixEnd_5732095 2943319892233855885651081 := by
  unfold tailWord_5732095
  simp only [CollatzResearch.WordTrace]
  refine ⟨209066680168606253731813739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139377786779070835821209159 209066680168606253731813739)
  ·
    refine ⟨313600020252909380597720609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209066680168606253731813739 313600020252909380597720609)
    ·
      refine ⟨235200015189682035448290457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313600020252909380597720609 235200015189682035448290457)
      ·
        refine ⟨176400011392261526586217843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235200015189682035448290457 176400011392261526586217843)
        ·
          refine ⟨264600017088392289879326765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176400011392261526586217843 264600017088392289879326765)
          ·
            refine ⟨99225006408147108704747537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264600017088392289879326765 99225006408147108704747537)
            ·
              refine ⟨74418754806110331528560653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99225006408147108704747537 74418754806110331528560653)
              ·
                refine ⟨27907033052291374323210245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74418754806110331528560653 27907033052291374323210245)
                ·
                  refine ⟨5232568697304632685601921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27907033052291374323210245 5232568697304632685601921)
                  ·
                    refine ⟨3924426522978474514201441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5232568697304632685601921 3924426522978474514201441)
                    ·
                      refine ⟨2943319892233855885651081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924426522978474514201441 2943319892233855885651081)
                      ·
                        rfl

theorem cell23_5732095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 3, 4, 2, 2].length) (baseStart_5732095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732095 prefixEnd_5732095 := by exact prefixLift 5732095
  have htrace : WordTrace (prefixWord ++ tailWord_5732095) baseStart_5732095 baseEnd_5732095 := by
    simpa [prefixWord, tailWord_5732095, baseEnd_5732095] using wordTrace_append hprefix tailTrace_5732095
  have hstable : (prefixWord ++ tailWord_5732095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732095).length < 2 ^ (prefixWord ++ tailWord_5732095).sum := by decide
  have hdescent : baseEnd_5732095 < baseStart_5732095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732128 : List Nat := [2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 3]
def baseStart_5732128 : Nat := 118140960795 + 5732128 * 2 ^ 59
def prefixEnd_5732128 : Nat := 4983230072969 + 3 ^ 40 * 5732128 * 2
def baseEnd_5732128 : Nat := 2943336837095454256538429

theorem tailTrace_5732128 : CollatzResearch.WordTrace tailWord_5732128 prefixEnd_5732128 2943336837095454256538429 := by
  unfold tailWord_5732128
  simp only [CollatzResearch.WordTrace]
  refine ⟨104533941888743350183882519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139378589184991133578510025 104533941888743350183882519)
  ·
    refine ⟨156800912833115025275823779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104533941888743350183882519 156800912833115025275823779)
    ·
      refine ⟨235201369249672537913735669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156800912833115025275823779 235201369249672537913735669)
      ·
        refine ⟨22050128367156800429412719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235201369249672537913735669 22050128367156800429412719)
        ·
          refine ⟨33075192550735200644119079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22050128367156800429412719 33075192550735200644119079)
          ·
            refine ⟨49612788826102800966178619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33075192550735200644119079 49612788826102800966178619)
            ·
              refine ⟨74419183239154201449267929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49612788826102800966178619 74419183239154201449267929)
              ·
                refine ⟨55814387429365651086950947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74419183239154201449267929 55814387429365651086950947)
                ·
                  refine ⟨83721581144048476630426421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55814387429365651086950947 83721581144048476630426421)
                  ·
                    refine ⟨7848898232254544684102477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83721581144048476630426421 7848898232254544684102477)
                    ·
                      refine ⟨2943336837095454256538429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7848898232254544684102477 2943336837095454256538429)
                      ·
                        rfl

theorem cell23_5732128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_5732128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732128 prefixEnd_5732128 := by exact prefixLift 5732128
  have htrace : WordTrace (prefixWord ++ tailWord_5732128) baseStart_5732128 baseEnd_5732128 := by
    simpa [prefixWord, tailWord_5732128, baseEnd_5732128] using wordTrace_append hprefix tailTrace_5732128
  have hstable : (prefixWord ++ tailWord_5732128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732128).length < 2 ^ (prefixWord ++ tailWord_5732128).sum := by decide
  have hdescent : baseEnd_5732128 < baseStart_5732128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732168 : List Nat := [2, 1, 3, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_5732168 : Nat := 118140960795 + 5732168 * 2 ^ 59
def prefixEnd_5732168 : Nat := 4983230072969 + 3 ^ 40 * 5732168 * 2
def baseEnd_5732168 : Nat := 2943357376321634100038245

theorem tailTrace_5732168 : CollatzResearch.WordTrace tailWord_5732168 prefixEnd_5732168 2943357376321634100038245 := by
  unfold tailWord_5732168
  simp only [CollatzResearch.WordTrace]
  refine ⟨104534671348670893599610579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139379561798227858132814105 104534671348670893599610579)
  ·
    refine ⟨156802007023006340399415869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104534671348670893599610579 156802007023006340399415869)
    ·
      refine ⟨58800752633627377649780951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156802007023006340399415869 58800752633627377649780951)
      ·
        refine ⟨88201128950441066474671427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58800752633627377649780951 88201128950441066474671427)
        ·
          refine ⟨132301693425661599712007141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88201128950441066474671427 132301693425661599712007141)
          ·
            refine ⟨24806567517311549946001339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132301693425661599712007141 24806567517311549946001339)
            ·
              refine ⟨37209851275967324919002009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24806567517311549946001339 37209851275967324919002009)
              ·
                refine ⟨27907388456975493689251507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37209851275967324919002009 27907388456975493689251507)
                ·
                  refine ⟨41861082685463240533877261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27907388456975493689251507 41861082685463240533877261)
                  ·
                    refine ⟨15697906007048715200203973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41861082685463240533877261 15697906007048715200203973)
                    ·
                      refine ⟨2943357376321634100038245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15697906007048715200203973 2943357376321634100038245)
                      ·
                        rfl

theorem cell23_5732168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_5732168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732168 prefixEnd_5732168 := by exact prefixLift 5732168
  have htrace : WordTrace (prefixWord ++ tailWord_5732168) baseStart_5732168 baseEnd_5732168 := by
    simpa [prefixWord, tailWord_5732168, baseEnd_5732168] using wordTrace_append hprefix tailTrace_5732168
  have hstable : (prefixWord ++ tailWord_5732168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732168).length < 2 ^ (prefixWord ++ tailWord_5732168).sum := by decide
  have hdescent : baseEnd_5732168 < baseStart_5732168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732205 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_5732205 : Nat := 118140960795 + 5732205 * 2 ^ 59
def prefixEnd_5732205 : Nat := 4983230072969 + 3 ^ 40 * 5732205 * 2
def baseEnd_5732205 : Nat := 2943376375105850455275575

theorem tailTrace_5732205 : CollatzResearch.WordTrace tailWord_5732205 prefixEnd_5732205 2943376375105850455275575 := by
  unfold tailWord_5732205
  simp only [CollatzResearch.WordTrace]
  refine ⟨209070692198207742518318069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139380461465471828345545379 209070692198207742518318069)
  ·
    refine ⟨19600377393581975861092319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209070692198207742518318069 19600377393581975861092319)
    ·
      refine ⟨29400566090372963791638479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19600377393581975861092319 29400566090372963791638479)
      ·
        refine ⟨44100849135559445687457719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29400566090372963791638479 44100849135559445687457719)
        ·
          refine ⟨66151273703339168531186579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44100849135559445687457719 66151273703339168531186579)
          ·
            refine ⟨99226910555008752796779869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66151273703339168531186579 99226910555008752796779869)
            ·
              refine ⟨37210091458128282298792451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99226910555008752796779869 37210091458128282298792451)
              ·
                refine ⟨55815137187192423448188677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37210091458128282298792451 55815137187192423448188677)
                ·
                  refine ⟨10465338222598579396535377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55815137187192423448188677 10465338222598579396535377)
                  ·
                    refine ⟨7849003666948934547401533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10465338222598579396535377 7849003666948934547401533)
                    ·
                      refine ⟨2943376375105850455275575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7849003666948934547401533 2943376375105850455275575)
                      ·
                        rfl

theorem cell23_5732205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_5732205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732205 prefixEnd_5732205 := by exact prefixLift 5732205
  have htrace : WordTrace (prefixWord ++ tailWord_5732205) baseStart_5732205 baseEnd_5732205 := by
    simpa [prefixWord, tailWord_5732205, baseEnd_5732205] using wordTrace_append hprefix tailTrace_5732205
  have hstable : (prefixWord ++ tailWord_5732205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732205).length < 2 ^ (prefixWord ++ tailWord_5732205).sum := by decide
  have hdescent : baseEnd_5732205 < baseStart_5732205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732208 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 6]
def baseStart_5732208 : Nat := 118140960795 + 5732208 * 2 ^ 59
def prefixEnd_5732208 : Nat := 4983230072969 + 3 ^ 40 * 5732208 * 2
def baseEnd_5732208 : Nat := 327041990616423771504229

theorem tailTrace_5732208 : CollatzResearch.WordTrace tailWord_5732208 prefixEnd_5732208 327041990616423771504229 := by
  unfold tailWord_5732208
  simp only [CollatzResearch.WordTrace]
  refine ⟨104535400808598437015338639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139380534411464582687118185 104535400808598437015338639)
  ·
    refine ⟨156803101212897655523007959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104535400808598437015338639 156803101212897655523007959)
    ·
      refine ⟨235204651819346483284511939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156803101212897655523007959 235204651819346483284511939)
      ·
        refine ⟨352806977729019724926767909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235204651819346483284511939 352806977729019724926767909)
        ·
          refine ⟨66151308324191198423768983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 352806977729019724926767909 66151308324191198423768983)
          ·
            refine ⟨99226962486286797635653475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66151308324191198423768983 99226962486286797635653475)
            ·
              refine ⟨148840443729430196453480213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99226962486286797635653475 148840443729430196453480213)
              ·
                refine ⟨6976895799817040458756885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148840443729430196453480213 6976895799817040458756885)
                ·
                  refine ⟨327041990616423771504229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6976895799817040458756885 327041990616423771504229)
                  ·
                    rfl

theorem cell23_5732208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 6].length) (baseStart_5732208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732208 prefixEnd_5732208 := by exact prefixLift 5732208
  have htrace : WordTrace (prefixWord ++ tailWord_5732208) baseStart_5732208 baseEnd_5732208 := by
    simpa [prefixWord, tailWord_5732208, baseEnd_5732208] using wordTrace_append hprefix tailTrace_5732208
  have hstable : (prefixWord ++ tailWord_5732208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732208).length < 2 ^ (prefixWord ++ tailWord_5732208).sum := by decide
  have hdescent : baseEnd_5732208 < baseStart_5732208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732228 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 1, 2, 6]
def baseStart_5732228 : Nat := 118140960795 + 5732228 * 2 ^ 59
def prefixEnd_5732228 : Nat := 4983230072969 + 3 ^ 40 * 5732228 * 2
def baseEnd_5732228 : Nat := 2943388185160903865287969

theorem tailTrace_5732228 : CollatzResearch.WordTrace tailWord_5732228 prefixEnd_5732228 2943388185160903865287969 := by
  unfold tailWord_5732228
  simp only [CollatzResearch.WordTrace]
  refine ⟨104535765538562208723202669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139381020718082944964270225 104535765538562208723202669)
  ·
    refine ⟨39200912076960828271201001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104535765538562208723202669 39200912076960828271201001)
    ·
      refine ⟨29400684057720621203400751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39200912076960828271201001 29400684057720621203400751)
      ·
        refine ⟨44101026086580931805101127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29400684057720621203400751 44101026086580931805101127)
        ·
          refine ⟨66151539129871397707651691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44101026086580931805101127 66151539129871397707651691)
          ·
            refine ⟨99227308694807096561477537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66151539129871397707651691 99227308694807096561477537)
            ·
              refine ⟨74420481521105322421108153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99227308694807096561477537 74420481521105322421108153)
              ·
                refine ⟨55815361140828991815831115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74420481521105322421108153 55815361140828991815831115)
                ·
                  refine ⟨83723041711243487723746673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55815361140828991815831115 83723041711243487723746673)
                  ·
                    refine ⟨62792281283432615792810005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83723041711243487723746673 62792281283432615792810005)
                    ·
                      refine ⟨2943388185160903865287969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62792281283432615792810005 2943388185160903865287969)
                      ·
                        rfl

theorem cell23_5732228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_5732228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732228 prefixEnd_5732228 := by exact prefixLift 5732228
  have htrace : WordTrace (prefixWord ++ tailWord_5732228) baseStart_5732228 baseEnd_5732228 := by
    simpa [prefixWord, tailWord_5732228, baseEnd_5732228] using wordTrace_append hprefix tailTrace_5732228
  have hstable : (prefixWord ++ tailWord_5732228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732228).length < 2 ^ (prefixWord ++ tailWord_5732228).sum := by decide
  have hdescent : baseEnd_5732228 < baseStart_5732228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732235 : List Nat := [1, 1, 1, 1, 4, 2, 1, 3, 5, 1, 3]
def baseStart_5732235 : Nat := 118140960795 + 5732235 * 2 ^ 59
def prefixEnd_5732235 : Nat := 4983230072969 + 3 ^ 40 * 5732235 * 2
def baseEnd_5732235 : Nat := 2943391779525485337900437

theorem tailTrace_5732235 : CollatzResearch.WordTrace tailWord_5732235 prefixEnd_5732235 2943391779525485337900437 := by
  unfold tailWord_5732235
  simp only [CollatzResearch.WordTrace]
  refine ⟨209071786388099057641910159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139381190925399371761273439 209071786388099057641910159)
  ·
    refine ⟨313607679582148586462865239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209071786388099057641910159 313607679582148586462865239)
    ·
      refine ⟨470411519373222879694297859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313607679582148586462865239 470411519373222879694297859)
      ·
        refine ⟨705617279059834319541446789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470411519373222879694297859 705617279059834319541446789)
        ·
          refine ⟨132303239823718934914021273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 705617279059834319541446789 132303239823718934914021273)
          ·
            refine ⟨99227429867789201185515955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132303239823718934914021273 99227429867789201185515955)
            ·
              refine ⟨148841144801683801778273933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99227429867789201185515955 148841144801683801778273933)
              ·
                refine ⟨55815429300631425666852725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148841144801683801778273933 55815429300631425666852725)
                ·
                  refine ⟨5232696496934196156267443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55815429300631425666852725 5232696496934196156267443)
                  ·
                    refine ⟨7849044745401294234401165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5232696496934196156267443 7849044745401294234401165)
                    ·
                      refine ⟨2943391779525485337900437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7849044745401294234401165 2943391779525485337900437)
                      ·
                        rfl

theorem cell23_5732235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 5, 1, 3].length) (baseStart_5732235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732235 prefixEnd_5732235 := by exact prefixLift 5732235
  have htrace : WordTrace (prefixWord ++ tailWord_5732235) baseStart_5732235 baseEnd_5732235 := by
    simpa [prefixWord, tailWord_5732235, baseEnd_5732235] using wordTrace_append hprefix tailTrace_5732235
  have hstable : (prefixWord ++ tailWord_5732235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732235).length < 2 ^ (prefixWord ++ tailWord_5732235).sum := by decide
  have hdescent : baseEnd_5732235 < baseStart_5732235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732285 : List Nat := [1, 4, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_5732285 : Nat := 118140960795 + 5732285 * 2 ^ 59
def prefixEnd_5732285 : Nat := 4983230072969 + 3 ^ 40 * 5732285 * 2
def baseEnd_5732285 : Nat := 981139151186070047425069

theorem tailTrace_5732285 : CollatzResearch.WordTrace tailWord_5732285 prefixEnd_5732285 981139151186070047425069 := by
  unfold tailWord_5732285
  simp only [CollatzResearch.WordTrace]
  refine ⟨209073610037917916181230309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139382406691945277454153539 209073610037917916181230309)
  ·
    refine ⟨39201301882109609283980683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209073610037917916181230309 39201301882109609283980683)
    ·
      refine ⟨58801952823164413925971025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39201301882109609283980683 58801952823164413925971025)
      ·
        refine ⟨44101464617373310444478269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58801952823164413925971025 44101464617373310444478269)
        ·
          refine ⟨16538049231514991416679351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44101464617373310444478269 16538049231514991416679351)
          ·
            refine ⟨24807073847272487125019027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16538049231514991416679351 24807073847272487125019027)
            ·
              refine ⟨37210610770908730687528541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24807073847272487125019027 37210610770908730687528541)
              ·
                refine ⟨13953979039090774007823203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37210610770908730687528541 13953979039090774007823203)
                ·
                  refine ⟨20930968558636161011734805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13953979039090774007823203 20930968558636161011734805)
                  ·
                    refine ⟨981139151186070047425069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20930968558636161011734805 981139151186070047425069)
                    ·
                      rfl

theorem cell23_5732285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_5732285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732285 prefixEnd_5732285 := by exact prefixLift 5732285
  have htrace : WordTrace (prefixWord ++ tailWord_5732285) baseStart_5732285 baseEnd_5732285 := by
    simpa [prefixWord, tailWord_5732285, baseEnd_5732285] using wordTrace_append hprefix tailTrace_5732285
  have hstable : (prefixWord ++ tailWord_5732285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732285).length < 2 ^ (prefixWord ++ tailWord_5732285).sum := by decide
  have hdescent : baseEnd_5732285 < baseStart_5732285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732298 : List Nat := [3, 1, 2, 1, 2, 1, 2, 11]
def baseStart_5732298 : Nat := 118140960795 + 5732298 * 2 ^ 59
def prefixEnd_5732298 : Nat := 4983230072969 + 3 ^ 40 * 5732298 * 2
def baseEnd_5732298 : Nat := 109015708474322910793061

theorem tailTrace_5732298 : CollatzResearch.WordTrace tailWord_5732298 prefixEnd_5732298 109015708474322910793061 := by
  unfold tailWord_5732298
  simp only [CollatzResearch.WordTrace]
  refine ⟨52268521046717704850363387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139382722791247212934302365 52268521046717704850363387)
  ·
    refine ⟨78402781570076557275545081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52268521046717704850363387 78402781570076557275545081)
    ·
      refine ⟨58802086177557417956658811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78402781570076557275545081 58802086177557417956658811)
      ·
        refine ⟨88203129266336126934988217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58802086177557417956658811 88203129266336126934988217)
        ·
          refine ⟨66152346949752095201241163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88203129266336126934988217 66152346949752095201241163)
          ·
            refine ⟨99228520424628142801861745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66152346949752095201241163 99228520424628142801861745)
            ·
              refine ⟨74421390318471107101396309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99228520424628142801861745 74421390318471107101396309)
              ·
                refine ⟨109015708474322910793061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 74421390318471107101396309 109015708474322910793061)
                ·
                  rfl

theorem cell23_5732298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 11].length) (baseStart_5732298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732298 prefixEnd_5732298 := by exact prefixLift 5732298
  have htrace : WordTrace (prefixWord ++ tailWord_5732298) baseStart_5732298 baseEnd_5732298 := by
    simpa [prefixWord, tailWord_5732298, baseEnd_5732298] using wordTrace_append hprefix tailTrace_5732298
  have hstable : (prefixWord ++ tailWord_5732298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732298).length < 2 ^ (prefixWord ++ tailWord_5732298).sum := by decide
  have hdescent : baseEnd_5732298 < baseStart_5732298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732306 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_5732306 : Nat := 118140960795 + 5732306 * 2 ^ 59
def prefixEnd_5732306 : Nat := 4983230072969 + 3 ^ 40 * 5732306 * 2
def baseEnd_5732306 : Nat := 981142745550651520037537

theorem tailTrace_5732306 : CollatzResearch.WordTrace tailWord_5732306 prefixEnd_5732306 981142745550651520037537 := by
  unfold tailWord_5732306
  simp only [CollatzResearch.WordTrace]
  refine ⟨52268593992710459191936193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139382917313894557845163181 52268593992710459191936193)
  ·
    refine ⟨39201445494532844393952145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52268593992710459191936193 39201445494532844393952145)
    ·
      refine ⟨29401084120899633295464109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39201445494532844393952145 29401084120899633295464109)
      ·
        refine ⟨11025406545337362485799041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29401084120899633295464109 11025406545337362485799041)
        ·
          refine ⟨8269054909003021864349281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11025406545337362485799041 8269054909003021864349281)
          ·
            refine ⟨6201791181752266398261961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8269054909003021864349281 6201791181752266398261961)
            ·
              refine ⟨4651343386314199798696471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6201791181752266398261961 4651343386314199798696471)
              ·
                refine ⟨6977015079471299698044707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651343386314199798696471 6977015079471299698044707)
                ·
                  refine ⟨10465522619206949547067061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6977015079471299698044707 10465522619206949547067061)
                  ·
                    refine ⟨981142745550651520037537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10465522619206949547067061 981142745550651520037537)
                    ·
                      rfl

theorem cell23_5732306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_5732306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732306 prefixEnd_5732306 := by exact prefixLift 5732306
  have htrace : WordTrace (prefixWord ++ tailWord_5732306) baseStart_5732306 baseEnd_5732306 := by
    simpa [prefixWord, tailWord_5732306, baseEnd_5732306] using wordTrace_append hprefix tailTrace_5732306
  have hstable : (prefixWord ++ tailWord_5732306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732306).length < 2 ^ (prefixWord ++ tailWord_5732306).sum := by decide
  have hdescent : baseEnd_5732306 < baseStart_5732306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732309 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 1, 1, 4]
def baseStart_5732309 : Nat := 118140960795 + 5732309 * 2 ^ 59
def prefixEnd_5732309 : Nat := 4983230072969 + 3 ^ 40 * 5732309 * 2
def baseEnd_5732309 : Nat := 2943429777093918048375097

theorem tailTrace_5732309 : CollatzResearch.WordTrace tailWord_5732309 prefixEnd_5732309 2943429777093918048375097 := by
  unfold tailWord_5732309
  simp only [CollatzResearch.WordTrace]
  refine ⟨209074485389830968280103981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139382990259887312186735987 209074485389830968280103981)
  ·
    refine ⟨78402932021186613105038993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209074485389830968280103981 78402932021186613105038993)
    ·
      refine ⟨58802199015889959828779245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78402932021186613105038993 58802199015889959828779245)
      ·
        refine ⟨22050824630958734935792217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58802199015889959828779245 22050824630958734935792217)
        ·
          refine ⟨16538118473219051201844163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22050824630958734935792217 16538118473219051201844163)
          ·
            refine ⟨24807177709828576802766245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16538118473219051201844163 24807177709828576802766245)
            ·
              refine ⟨4651345820592858150518671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24807177709828576802766245 4651345820592858150518671)
              ·
                refine ⟨6977018730889287225778007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651345820592858150518671 6977018730889287225778007)
                ·
                  refine ⟨10465528096333930838667011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6977018730889287225778007 10465528096333930838667011)
                  ·
                    refine ⟨15698292144500896258000517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10465528096333930838667011 15698292144500896258000517)
                    ·
                      refine ⟨2943429777093918048375097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15698292144500896258000517 2943429777093918048375097)
                      ·
                        rfl

theorem cell23_5732309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_5732309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732309 prefixEnd_5732309 := by exact prefixLift 5732309
  have htrace : WordTrace (prefixWord ++ tailWord_5732309) baseStart_5732309 baseEnd_5732309 := by
    simpa [prefixWord, tailWord_5732309, baseEnd_5732309] using wordTrace_append hprefix tailTrace_5732309
  have hstable : (prefixWord ++ tailWord_5732309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732309).length < 2 ^ (prefixWord ++ tailWord_5732309).sum := by decide
  have hdescent : baseEnd_5732309 < baseStart_5732309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732312 : List Nat := [2, 1, 2, 2, 2, 2, 3, 3, 1, 2, 3]
def baseStart_5732312 : Nat := 118140960795 + 5732312 * 2 ^ 59
def prefixEnd_5732312 : Nat := 4983230072969 + 3 ^ 40 * 5732312 * 2
def baseEnd_5732312 : Nat := 2943431317535881536637583

theorem tailTrace_5732312 : CollatzResearch.WordTrace tailWord_5732312 prefixEnd_5732312 2943431317535881536637583 := by
  unfold tailWord_5732312
  simp only [CollatzResearch.WordTrace]
  refine ⟨104537297404410049896231595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139383063205880066528308793 104537297404410049896231595)
  ·
    refine ⟨156805946106615074844347393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104537297404410049896231595 156805946106615074844347393)
    ·
      refine ⟨117604459579961306133260545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156805946106615074844347393 117604459579961306133260545)
      ·
        refine ⟨88203344684970979599945409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117604459579961306133260545 88203344684970979599945409)
        ·
          refine ⟨66152508513728234699959057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88203344684970979599945409 66152508513728234699959057)
          ·
            refine ⟨49614381385296176024969293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66152508513728234699959057 49614381385296176024969293)
            ·
              refine ⟨18605393019486066009363485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49614381385296176024969293 18605393019486066009363485)
              ·
                refine ⟨6977022382307274753511307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18605393019486066009363485 6977022382307274753511307)
                ·
                  refine ⟨10465533573460912130266961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6977022382307274753511307 10465533573460912130266961)
                  ·
                    refine ⟨7849150180095684097700221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10465533573460912130266961 7849150180095684097700221)
                    ·
                      refine ⟨2943431317535881536637583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7849150180095684097700221 2943431317535881536637583)
                      ·
                        rfl

theorem cell23_5732312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_5732312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732312 prefixEnd_5732312 := by exact prefixLift 5732312
  have htrace : WordTrace (prefixWord ++ tailWord_5732312) baseStart_5732312 baseEnd_5732312 := by
    simpa [prefixWord, tailWord_5732312, baseEnd_5732312] using wordTrace_append hprefix tailTrace_5732312
  have hstable : (prefixWord ++ tailWord_5732312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732312).length < 2 ^ (prefixWord ++ tailWord_5732312).sum := by decide
  have hdescent : baseEnd_5732312 < baseStart_5732312 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732319 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 2, 4]
def baseStart_5732319 : Nat := 118140960795 + 5732319 * 2 ^ 59
def prefixEnd_5732319 : Nat := 4983230072969 + 3 ^ 40 * 5732319 * 2
def baseEnd_5732319 : Nat := 981144970633487669750017

theorem tailTrace_5732319 : CollatzResearch.WordTrace tailWord_5732319 prefixEnd_5732319 981144970633487669750017 := by
  unfold tailWord_5732319
  simp only [CollatzResearch.WordTrace]
  refine ⟨209074850119794739987968011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139383233413196493325312007 209074850119794739987968011)
  ·
    refine ⟨313612275179692109981952017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209074850119794739987968011 313612275179692109981952017)
    ·
      refine ⟨235209206384769082486464013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313612275179692109981952017 235209206384769082486464013)
      ·
        refine ⟨88203452394288405932424005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235209206384769082486464013 88203452394288405932424005)
        ·
          refine ⟨16538147323929076112329501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88203452394288405932424005 16538147323929076112329501)
          ·
            refine ⟨6201805246473403542123563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16538147323929076112329501 6201805246473403542123563)
            ·
              refine ⟨9302707869710105313185345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6201805246473403542123563 9302707869710105313185345)
              ·
                refine ⟨6977030902282578984889009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9302707869710105313185345 6977030902282578984889009)
                ·
                  refine ⟨5232773176711934238666757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6977030902282578984889009 5232773176711934238666757)
                  ·
                    refine ⟨981144970633487669750017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5232773176711934238666757 981144970633487669750017)
                    ·
                      rfl

theorem cell23_5732319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 4].length) (baseStart_5732319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732319 prefixEnd_5732319 := by exact prefixLift 5732319
  have htrace : WordTrace (prefixWord ++ tailWord_5732319) baseStart_5732319 baseEnd_5732319 := by
    simpa [prefixWord, tailWord_5732319, baseEnd_5732319] using wordTrace_append hprefix tailTrace_5732319
  have hstable : (prefixWord ++ tailWord_5732319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732319).length < 2 ^ (prefixWord ++ tailWord_5732319).sum := by decide
  have hdescent : baseEnd_5732319 < baseStart_5732319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732405 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 7]
def baseStart_5732405 : Nat := 118140960795 + 5732405 * 2 ^ 59
def prefixEnd_5732405 : Nat := 4983230072969 + 3 ^ 40 * 5732405 * 2
def baseEnd_5732405 : Nat := 327053230137416630308295

theorem tailTrace_5732405 : CollatzResearch.WordTrace tailWord_5732405 prefixEnd_5732405 327053230137416630308295 := by
  unfold tailWord_5732405
  simp only [CollatzResearch.WordTrace]
  refine ⟨209077986797483176675598669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139385324531655451117065779 209077986797483176675598669)
  ·
    refine ⟨78404245049056191253349501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209077986797483176675598669 78404245049056191253349501)
    ·
      refine ⟨29401591893396071720006063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78404245049056191253349501 29401591893396071720006063)
      ·
        refine ⟨44102387840094107580009095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29401591893396071720006063 44102387840094107580009095)
        ·
          refine ⟨66153581760141161370013643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44102387840094107580009095 66153581760141161370013643)
          ·
            refine ⟨99230372640211742055020465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66153581760141161370013643 99230372640211742055020465)
            ·
              refine ⟨74422779480158806541265349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99230372640211742055020465 74422779480158806541265349)
              ·
                refine ⟨13954271152529776226487253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74422779480158806541265349 13954271152529776226487253)
                ·
                  refine ⟨327053230137416630308295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13954271152529776226487253 327053230137416630308295)
                  ·
                    rfl

theorem cell23_5732405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_5732405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732405 prefixEnd_5732405 := by exact prefixLift 5732405
  have htrace : WordTrace (prefixWord ++ tailWord_5732405) baseStart_5732405 baseEnd_5732405 := by
    simpa [prefixWord, tailWord_5732405, baseEnd_5732405] using wordTrace_append hprefix tailTrace_5732405
  have hstable : (prefixWord ++ tailWord_5732405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732405).length < 2 ^ (prefixWord ++ tailWord_5732405).sum := by decide
  have hdescent : baseEnd_5732405 < baseStart_5732405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732439 : List Nat := [1, 1, 3, 2, 2, 1, 6, 2, 5]
def baseStart_5732439 : Nat := 118140960795 + 5732439 * 2 ^ 59
def prefixEnd_5732439 : Nat := 4983230072969 + 3 ^ 40 * 5732439 * 2
def baseEnd_5732439 : Nat := 327055169953222504416611

theorem tailTrace_5732439 : CollatzResearch.WordTrace tailWord_5732439 prefixEnd_5732439 327055169953222504416611 := by
  unfold tailWord_5732439
  simp only [CollatzResearch.WordTrace]
  refine ⟨209079226879360000482336371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139386151252906666988224247 209079226879360000482336371)
  ·
    refine ⟨313618840319040000723504557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209079226879360000482336371 313618840319040000723504557)
    ·
      refine ⟨117607065119640000271314209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313618840319040000723504557 117607065119640000271314209)
      ·
        refine ⟨88205298839730000203485657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117607065119640000271314209 88205298839730000203485657)
        ·
          refine ⟨66153974129797500152614243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88205298839730000203485657 66153974129797500152614243)
          ·
            refine ⟨99230961194696250228921365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66153974129797500152614243 99230961194696250228921365)
            ·
              refine ⟨4651451306001386729480689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99230961194696250228921365 4651451306001386729480689)
              ·
                refine ⟨3488588479501040047110517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4651451306001386729480689 3488588479501040047110517)
                ·
                  refine ⟨327055169953222504416611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3488588479501040047110517 327055169953222504416611)
                  ·
                    rfl

theorem cell23_5732439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 5].length) (baseStart_5732439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732439 prefixEnd_5732439 := by exact prefixLift 5732439
  have htrace : WordTrace (prefixWord ++ tailWord_5732439) baseStart_5732439 baseEnd_5732439 := by
    simpa [prefixWord, tailWord_5732439, baseEnd_5732439] using wordTrace_append hprefix tailTrace_5732439
  have hstable : (prefixWord ++ tailWord_5732439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732439).length < 2 ^ (prefixWord ++ tailWord_5732439).sum := by decide
  have hdescent : baseEnd_5732439 < baseStart_5732439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732442 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2]
def baseStart_5732442 : Nat := 118140960795 + 5732442 * 2 ^ 59
def prefixEnd_5732442 : Nat := 4983230072969 + 3 ^ 40 * 5732442 * 2
def baseEnd_5732442 : Nat := 2943498070020966028011985

theorem tailTrace_5732442 : CollatzResearch.WordTrace tailWord_5732442 prefixEnd_5732442 2943498070020966028011985 := by
  unfold tailWord_5732442
  simp only [CollatzResearch.WordTrace]
  refine ⟨52269834074587282998673895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139386224198899421329797053 52269834074587282998673895)
  ·
    refine ⟨78404751111880924498010843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52269834074587282998673895 78404751111880924498010843)
    ·
      refine ⟨117607126667821386747016265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78404751111880924498010843 117607126667821386747016265)
      ·
        refine ⟨88205345000866040060262199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117607126667821386747016265 88205345000866040060262199)
        ·
          refine ⟨132308017501299060090393299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88205345000866040060262199 132308017501299060090393299)
          ·
            refine ⟨198462026251948590135589949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132308017501299060090393299 198462026251948590135589949)
            ·
              refine ⟨74423259844480721300846231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198462026251948590135589949 74423259844480721300846231)
              ·
                refine ⟨111634889766721081951269347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74423259844480721300846231 111634889766721081951269347)
                ·
                  refine ⟨167452334650081622926904021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111634889766721081951269347 167452334650081622926904021)
                  ·
                    refine ⟨3924664093361288037349313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 167452334650081622926904021 3924664093361288037349313)
                    ·
                      refine ⟨2943498070020966028011985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924664093361288037349313 2943498070020966028011985)
                      ·
                        rfl

theorem cell23_5732442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_5732442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732442 prefixEnd_5732442 := by exact prefixLift 5732442
  have htrace : WordTrace (prefixWord ++ tailWord_5732442) baseStart_5732442 baseEnd_5732442 := by
    simpa [prefixWord, tailWord_5732442, baseEnd_5732442] using wordTrace_append hprefix tailTrace_5732442
  have hstable : (prefixWord ++ tailWord_5732442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732442).length < 2 ^ (prefixWord ++ tailWord_5732442).sum := by decide
  have hdescent : baseEnd_5732442 < baseStart_5732442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732472 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 3, 6, 2]
def baseStart_5732472 : Nat := 118140960795 + 5732472 * 2 ^ 59
def prefixEnd_5732472 : Nat := 4983230072969 + 3 ^ 40 * 5732472 * 2
def baseEnd_5732472 : Nat := 2943513474440600910636847

theorem tailTrace_5732472 : CollatzResearch.WordTrace tailWord_5732472 prefixEnd_5732472 2943513474440600910636847 := by
  unfold tailWord_5732472
  simp only [CollatzResearch.WordTrace]
  refine ⟨104540215244120223559143835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139386953658826964745525113 104540215244120223559143835)
  ·
    refine ⟨156810322866180335338715753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104540215244120223559143835 156810322866180335338715753)
    ·
      refine ⟨117607742149635251504036815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156810322866180335338715753 117607742149635251504036815)
      ·
        refine ⟨176411613224452877256055223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117607742149635251504036815 176411613224452877256055223)
        ·
          refine ⟨264617419836679315884082835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176411613224452877256055223 264617419836679315884082835)
          ·
            refine ⟨396926129755018973826124253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264617419836679315884082835 396926129755018973826124253)
            ·
              refine ⟨148847298658132115184796595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 396926129755018973826124253 148847298658132115184796595)
              ·
                refine ⟨223270947987198172777194893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148847298658132115184796595 223270947987198172777194893)
                ·
                  refine ⟨83726605495199314791448085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223270947987198172777194893 83726605495199314791448085)
                  ·
                    refine ⟨3924684632587467880849129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83726605495199314791448085 3924684632587467880849129)
                    ·
                      refine ⟨2943513474440600910636847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924684632587467880849129 2943513474440600910636847)
                      ·
                        rfl

theorem cell23_5732472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 3, 6, 2].length) (baseStart_5732472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732472 prefixEnd_5732472 := by exact prefixLift 5732472
  have htrace : WordTrace (prefixWord ++ tailWord_5732472) baseStart_5732472 baseEnd_5732472 := by
    simpa [prefixWord, tailWord_5732472, baseEnd_5732472] using wordTrace_append hprefix tailTrace_5732472
  have hstable : (prefixWord ++ tailWord_5732472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732472).length < 2 ^ (prefixWord ++ tailWord_5732472).sum := by decide
  have hdescent : baseEnd_5732472 < baseStart_5732472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732546 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 8]
def baseStart_5732546 : Nat := 118140960795 + 5732546 * 2 ^ 59
def prefixEnd_5732546 : Nat := 4983230072969 + 3 ^ 40 * 5732546 * 2
def baseEnd_5732546 : Nat := 327061274667670402345723

theorem tailTrace_5732546 : CollatzResearch.WordTrace tailWord_5732546 prefixEnd_5732546 327061274667670402345723 := by
  unfold tailWord_5732546
  simp only [CollatzResearch.WordTrace]
  refine ⟨52270782372493089439120373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139388752993314905170987661 52270782372493089439120373)
  ·
    refine ⟨4900385847421227134917535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52270782372493089439120373 4900385847421227134917535)
    ·
      refine ⟨7350578771131840702376303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4900385847421227134917535 7350578771131840702376303)
      ·
        refine ⟨11025868156697761053564455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7350578771131840702376303 11025868156697761053564455)
        ·
          refine ⟨16538802235046641580346683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11025868156697761053564455 16538802235046641580346683)
          ·
            refine ⟨24808203352569962370520025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16538802235046641580346683 24808203352569962370520025)
            ·
              refine ⟨18606152514427471777890019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24808203352569962370520025 18606152514427471777890019)
              ·
                refine ⟨27909228771641207666835029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18606152514427471777890019 27909228771641207666835029)
                ·
                  refine ⟨327061274667670402345723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27909228771641207666835029 327061274667670402345723)
                  ·
                    rfl

theorem cell23_5732546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_5732546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732546 prefixEnd_5732546 := by exact prefixLift 5732546
  have htrace : WordTrace (prefixWord ++ tailWord_5732546) baseStart_5732546 baseEnd_5732546 := by
    simpa [prefixWord, tailWord_5732546, baseEnd_5732546] using wordTrace_append hprefix tailTrace_5732546
  have hstable : (prefixWord ++ tailWord_5732546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732546).length < 2 ^ (prefixWord ++ tailWord_5732546).sum := by decide
  have hdescent : baseEnd_5732546 < baseStart_5732546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732549 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 4, 3, 2]
def baseStart_5732549 : Nat := 118140960795 + 5732549 * 2 ^ 59
def prefixEnd_5732549 : Nat := 4983230072969 + 3 ^ 40 * 5732549 * 2
def baseEnd_5732549 : Nat := 2943553012450997109373993

theorem tailTrace_5732549 : CollatzResearch.WordTrace tailWord_5732549 prefixEnd_5732549 2943553012450997109373993 := by
  unfold tailWord_5732549
  simp only [CollatzResearch.WordTrace]
  refine ⟨209083238908961489268840701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139388825939307659512560467 209083238908961489268840701)
  ·
    refine ⟨78406214590860558475815263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209083238908961489268840701 78406214590860558475815263)
    ·
      refine ⟨117609321886290837713722895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78406214590860558475815263 117609321886290837713722895)
      ·
        refine ⟨176413982829436256570584343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117609321886290837713722895 176413982829436256570584343)
        ·
          refine ⟨264620974244154384855876515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176413982829436256570584343 264620974244154384855876515)
          ·
            refine ⟨396931461366231577283814773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264620974244154384855876515 396931461366231577283814773)
            ·
              refine ⟨37212324503084210370357635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 396931461366231577283814773 37212324503084210370357635)
              ·
                refine ⟨55818486754626315555536453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37212324503084210370357635 55818486754626315555536453)
                ·
                  refine ⟨10465966266492434166663085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55818486754626315555536453 10465966266492434166663085)
                  ·
                    refine ⟨3924737349934662812498657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10465966266492434166663085 3924737349934662812498657)
                    ·
                      refine ⟨2943553012450997109373993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924737349934662812498657 2943553012450997109373993)
                      ·
                        rfl

theorem cell23_5732549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 3, 2].length) (baseStart_5732549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732549 prefixEnd_5732549 := by exact prefixLift 5732549
  have htrace : WordTrace (prefixWord ++ tailWord_5732549) baseStart_5732549 baseEnd_5732549 := by
    simpa [prefixWord, tailWord_5732549, baseEnd_5732549] using wordTrace_append hprefix tailTrace_5732549
  have hstable : (prefixWord ++ tailWord_5732549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732549).length < 2 ^ (prefixWord ++ tailWord_5732549).sum := by decide
  have hdescent : baseEnd_5732549 < baseStart_5732549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732583 : List Nat := [1, 1, 5, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5732583 : Nat := 118140960795 + 5732583 * 2 ^ 59
def prefixEnd_5732583 : Nat := 4983230072969 + 3 ^ 40 * 5732583 * 2
def baseEnd_5732583 : Nat := 2943570470793249976348837

theorem tailTrace_5732583 : CollatzResearch.WordTrace tailWord_5732583 prefixEnd_5732583 2943570470793249976348837 := by
  unfold tailWord_5732583
  simp only [CollatzResearch.WordTrace]
  refine ⟨209084478990838313075578403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139389652660558875383718935 209084478990838313075578403)
  ·
    refine ⟨313626718486257469613367605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209084478990838313075578403 313626718486257469613367605)
    ·
      refine ⟨29402504858086637776253213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 313626718486257469613367605 29402504858086637776253213)
      ·
        refine ⟨11025939321782489166094955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29402504858086637776253213 11025939321782489166094955)
        ·
          refine ⟨16538908982673733749142433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11025939321782489166094955 16538908982673733749142433)
          ·
            refine ⟨12404181737005300311856825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16538908982673733749142433 12404181737005300311856825)
            ·
              refine ⟨9303136302753975233892619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12404181737005300311856825 9303136302753975233892619)
              ·
                refine ⟨13954704454130962850838929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9303136302753975233892619 13954704454130962850838929)
                ·
                  refine ⟨10466028340598222138129197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13954704454130962850838929 10466028340598222138129197)
                  ·
                    refine ⟨3924760627724333301798449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10466028340598222138129197 3924760627724333301798449)
                    ·
                      refine ⟨2943570470793249976348837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924760627724333301798449 2943570470793249976348837)
                      ·
                        rfl

theorem cell23_5732583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5732583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732583 prefixEnd_5732583 := by exact prefixLift 5732583
  have htrace : WordTrace (prefixWord ++ tailWord_5732583) baseStart_5732583 baseEnd_5732583 := by
    simpa [prefixWord, tailWord_5732583, baseEnd_5732583] using wordTrace_append hprefix tailTrace_5732583
  have hstable : (prefixWord ++ tailWord_5732583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732583).length < 2 ^ (prefixWord ++ tailWord_5732583).sum := by decide
  have hdescent : baseEnd_5732583 < baseStart_5732583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732629 : List Nat := [1, 3, 2, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_5732629 : Nat := 118140960795 + 5732629 * 2 ^ 59
def prefixEnd_5732629 : Nat := 4983230072969 + 3 ^ 40 * 5732629 * 2
def baseEnd_5732629 : Nat := 2943594090903356796373625

theorem tailTrace_5732629 : CollatzResearch.WordTrace tailWord_5732629 prefixEnd_5732629 2943594090903356796373625 := by
  unfold tailWord_5732629
  simp only [CollatzResearch.WordTrace]
  refine ⟨209086156748671662931752941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139390771165781108621168627 209086156748671662931752941)
  ·
    refine ⟨78407308780751873599407353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209086156748671662931752941 78407308780751873599407353)
    ·
      refine ⟨58805481585563905199555515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78407308780751873599407353 58805481585563905199555515)
      ·
        refine ⟨88208222378345857799333273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58805481585563905199555515 88208222378345857799333273)
        ·
          refine ⟨66156166783759393349499955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88208222378345857799333273 66156166783759393349499955)
          ·
            refine ⟨99234250175639090024249933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66156166783759393349499955 99234250175639090024249933)
            ·
              refine ⟨37212843815864658759093725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99234250175639090024249933 37212843815864658759093725)
              ·
                refine ⟨13954816430949247034660147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37212843815864658759093725 13954816430949247034660147)
                ·
                  refine ⟨20932224646423870551990221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13954816430949247034660147 20932224646423870551990221)
                  ·
                    refine ⟨7849584242408951456996333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20932224646423870551990221 7849584242408951456996333)
                    ·
                      refine ⟨2943594090903356796373625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7849584242408951456996333 2943594090903356796373625)
                      ·
                        rfl

theorem cell23_5732629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_5732629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732629 prefixEnd_5732629 := by exact prefixLift 5732629
  have htrace : WordTrace (prefixWord ++ tailWord_5732629) baseStart_5732629 baseEnd_5732629 := by
    simpa [prefixWord, tailWord_5732629, baseEnd_5732629] using wordTrace_append hprefix tailTrace_5732629
  have hstable : (prefixWord ++ tailWord_5732629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732629).length < 2 ^ (prefixWord ++ tailWord_5732629).sum := by decide
  have hdescent : baseEnd_5732629 < baseStart_5732629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732632 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 2, 7]
def baseStart_5732632 : Nat := 118140960795 + 5732632 * 2 ^ 59
def prefixEnd_5732632 : Nat := 4983230072969 + 3 ^ 40 * 5732632 * 2
def baseEnd_5732632 : Nat := 981198543781773428212037

theorem tailTrace_5732632 : CollatzResearch.WordTrace tailWord_5732632 prefixEnd_5732632 981198543781773428212037 := by
  unfold tailWord_5732632
  simp only [CollatzResearch.WordTrace]
  refine ⟨104543133083830397222056075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139390844111773862962741433 104543133083830397222056075)
  ·
    refine ⟨156814699625745595833084113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104543133083830397222056075 156814699625745595833084113)
    ·
      refine ⟨117611024719309196874813085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156814699625745595833084113 117611024719309196874813085)
      ·
        refine ⟨44104134269740948828054907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117611024719309196874813085 44104134269740948828054907)
        ·
          refine ⟨66156201404611423242082361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44104134269740948828054907 66156201404611423242082361)
          ·
            refine ⟨49617151053458567431561771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66156201404611423242082361 49617151053458567431561771)
            ·
              refine ⟨74425726580187851147342657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49617151053458567431561771 74425726580187851147342657)
              ·
                refine ⟨55819294935140888360506993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74425726580187851147342657 55819294935140888360506993)
                ·
                  refine ⟨41864471201355666270380245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55819294935140888360506993 41864471201355666270380245)
                  ·
                    refine ⟨981198543781773428212037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41864471201355666270380245 981198543781773428212037)
                    ·
                      rfl

theorem cell23_5732632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_5732632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732632 prefixEnd_5732632 := by exact prefixLift 5732632
  have htrace : WordTrace (prefixWord ++ tailWord_5732632) baseStart_5732632 baseEnd_5732632 := by
    simpa [prefixWord, tailWord_5732632, baseEnd_5732632] using wordTrace_append hprefix tailTrace_5732632
  have hstable : (prefixWord ++ tailWord_5732632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732632).length < 2 ^ (prefixWord ++ tailWord_5732632).sum := by decide
  have hdescent : baseEnd_5732632 < baseStart_5732632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732672 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 5]
def baseStart_5732672 : Nat := 118140960795 + 5732672 * 2 ^ 59
def prefixEnd_5732672 : Nat := 4983230072969 + 3 ^ 40 * 5732672 * 2
def baseEnd_5732672 : Nat := 2943616170571500128135927

theorem tailTrace_5732672 : CollatzResearch.WordTrace tailWord_5732672 prefixEnd_5732672 2943616170571500128135927 := by
  unfold tailWord_5732672
  simp only [CollatzResearch.WordTrace]
  refine ⟨104543862543757940637784135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139391816725010587517045513 104543862543757940637784135)
  ·
    refine ⟨156815793815636910956676203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104543862543757940637784135 156815793815636910956676203)
    ·
      refine ⟨235223690723455366435014305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156815793815636910956676203 235223690723455366435014305)
      ·
        refine ⟨176417768042591524826260729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235223690723455366435014305 176417768042591524826260729)
        ·
          refine ⟨132313326031943643619695547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176417768042591524826260729 132313326031943643619695547)
          ·
            refine ⟨198469989047915465429543321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132313326031943643619695547 198469989047915465429543321)
            ·
              refine ⟨148852491785936599072157491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198469989047915465429543321 148852491785936599072157491)
              ·
                refine ⟨223278737678904898608236237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148852491785936599072157491 223278737678904898608236237)
                ·
                  refine ⟨83729526629589336978088589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223278737678904898608236237 83729526629589336978088589)
                  ·
                    refine ⟨31398572486096001366783221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83729526629589336978088589 31398572486096001366783221)
                    ·
                      refine ⟨2943616170571500128135927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31398572486096001366783221 2943616170571500128135927)
                      ·
                        rfl

theorem cell23_5732672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_5732672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732672 prefixEnd_5732672 := by exact prefixLift 5732672
  have htrace : WordTrace (prefixWord ++ tailWord_5732672) baseStart_5732672 baseEnd_5732672 := by
    simpa [prefixWord, tailWord_5732672, baseEnd_5732672] using wordTrace_append hprefix tailTrace_5732672
  have hstable : (prefixWord ++ tailWord_5732672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732672).length < 2 ^ (prefixWord ++ tailWord_5732672).sum := by decide
  have hdescent : baseEnd_5732672 < baseStart_5732672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732686 : List Nat := [4, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2]
def baseStart_5732686 : Nat := 118140960795 + 5732686 * 2 ^ 59
def prefixEnd_5732686 : Nat := 4983230072969 + 3 ^ 40 * 5732686 * 2
def baseEnd_5732686 : Nat := 2943623359300663073360863

theorem tailTrace_5732686 : CollatzResearch.WordTrace tailWord_5732686 prefixEnd_5732686 2943623359300663073360863 := by
  unfold tailWord_5732686
  simp only [CollatzResearch.WordTrace]
  refine ⟨26136029463683145208322239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139392157139643441111051941 26136029463683145208322239)
  ·
    refine ⟨39204044195524717812483359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26136029463683145208322239 39204044195524717812483359)
    ·
      refine ⟨58806066293287076718725039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39204044195524717812483359 58806066293287076718725039)
      ·
        refine ⟨88209099439930615078087559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58806066293287076718725039 88209099439930615078087559)
        ·
          refine ⟨132313649159895922617131339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88209099439930615078087559 132313649159895922617131339)
          ·
            refine ⟨198470473739843883925697009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132313649159895922617131339 198470473739843883925697009)
            ·
              refine ⟨148852855304882912944272757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198470473739843883925697009 148852855304882912944272757)
              ·
                refine ⟨13954955184832773088525571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148852855304882912944272757 13954955184832773088525571)
                ·
                  refine ⟨20932432777249159632788357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13954955184832773088525571 20932432777249159632788357)
                  ·
                    refine ⟨3924831145734217431147817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20932432777249159632788357 3924831145734217431147817)
                    ·
                      refine ⟨2943623359300663073360863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924831145734217431147817 2943623359300663073360863)
                      ·
                        rfl

theorem cell23_5732686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2].length) (baseStart_5732686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732686 prefixEnd_5732686 := by exact prefixLift 5732686
  have htrace : WordTrace (prefixWord ++ tailWord_5732686) baseStart_5732686 baseEnd_5732686 := by
    simpa [prefixWord, tailWord_5732686, baseEnd_5732686] using wordTrace_append hprefix tailTrace_5732686
  have hstable : (prefixWord ++ tailWord_5732686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732686).length < 2 ^ (prefixWord ++ tailWord_5732686).sum := by decide
  have hdescent : baseEnd_5732686 < baseStart_5732686 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732706 : List Nat := [3, 3, 2, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_5732706 : Nat := 118140960795 + 5732706 * 2 ^ 59
def prefixEnd_5732706 : Nat := 4983230072969 + 3 ^ 40 * 5732706 * 2
def baseEnd_5732706 : Nat := 2943633628913752995110771

theorem tailTrace_5732706 : CollatzResearch.WordTrace tailWord_5732706 prefixEnd_5732706 2943633628913752995110771 := by
  unfold tailWord_5732706
  simp only [CollatzResearch.WordTrace]
  refine ⟨52272241292348176270576493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139392643446261803388203981 52272241292348176270576493)
  ·
    refine ⟨19602090484630566101466185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52272241292348176270576493 19602090484630566101466185)
    ·
      refine ⟨14701567863472924576099639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19602090484630566101466185 14701567863472924576099639)
      ·
        refine ⟨22052351795209386864149459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14701567863472924576099639 22052351795209386864149459)
        ·
          refine ⟨33078527692814080296224189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22052351795209386864149459 33078527692814080296224189)
          ·
            refine ⟨12404447884805280111084071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33078527692814080296224189 12404447884805280111084071)
            ·
              refine ⟨18606671827207920166626107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12404447884805280111084071 18606671827207920166626107)
              ·
                refine ⟨27910007740811880249939161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18606671827207920166626107 27910007740811880249939161)
                ·
                  refine ⟨20932505805608910187454371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27910007740811880249939161 20932505805608910187454371)
                  ·
                    refine ⟨31398758708413365281181557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20932505805608910187454371 31398758708413365281181557)
                    ·
                      refine ⟨2943633628913752995110771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31398758708413365281181557 2943633628913752995110771)
                      ·
                        rfl

theorem cell23_5732706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_5732706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732706 prefixEnd_5732706 := by exact prefixLift 5732706
  have htrace : WordTrace (prefixWord ++ tailWord_5732706) baseStart_5732706 baseEnd_5732706 := by
    simpa [prefixWord, tailWord_5732706, baseEnd_5732706] using wordTrace_append hprefix tailTrace_5732706
  have hstable : (prefixWord ++ tailWord_5732706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732706).length < 2 ^ (prefixWord ++ tailWord_5732706).sum := by decide
  have hdescent : baseEnd_5732706 < baseStart_5732706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732719 : List Nat := [1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 3]
def baseStart_5732719 : Nat := 118140960795 + 5732719 * 2 ^ 59
def prefixEnd_5732719 : Nat := 4983230072969 + 3 ^ 40 * 5732719 * 2
def baseEnd_5732719 : Nat := 2943640304162261444248211

theorem tailTrace_5732719 : CollatzResearch.WordTrace tailWord_5732719 prefixEnd_5732719 2943640304162261444248211 := by
  unfold tailWord_5732719
  simp only [CollatzResearch.WordTrace]
  refine ⟨209089439318345608302529211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139392959545563738868352807 209089439318345608302529211)
  ·
    refine ⟨313634158977518412453793817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209089439318345608302529211 313634158977518412453793817)
    ·
      refine ⟨235225619233138809340345363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313634158977518412453793817 235225619233138809340345363)
      ·
        refine ⟨352838428849708214010518045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235225619233138809340345363 352838428849708214010518045)
        ·
          refine ⟨132314410818640580253944267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352838428849708214010518045 132314410818640580253944267)
          ·
            refine ⟨198471616227960870380916401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132314410818640580253944267 198471616227960870380916401)
            ·
              refine ⟨148853712170970652785687301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198471616227960870380916401 148853712170970652785687301)
              ·
                refine ⟨27910071032056997397316369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148853712170970652785687301 27910071032056997397316369)
                ·
                  refine ⟨20932553274042748047987277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27910071032056997397316369 20932553274042748047987277)
                  ·
                    refine ⟨7849707477766030517995229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20932553274042748047987277 7849707477766030517995229)
                    ·
                      refine ⟨2943640304162261444248211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7849707477766030517995229 2943640304162261444248211)
                      ·
                        rfl

theorem cell23_5732719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 3].length) (baseStart_5732719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732719 prefixEnd_5732719 := by exact prefixLift 5732719
  have htrace : WordTrace (prefixWord ++ tailWord_5732719) baseStart_5732719 baseEnd_5732719 := by
    simpa [prefixWord, tailWord_5732719, baseEnd_5732719] using wordTrace_append hprefix tailTrace_5732719
  have hstable : (prefixWord ++ tailWord_5732719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732719).length < 2 ^ (prefixWord ++ tailWord_5732719).sum := by decide
  have hdescent : baseEnd_5732719 < baseStart_5732719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732737 : List Nat := [1, 2, 4, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_5732737 : Nat := 118140960795 + 5732737 * 2 ^ 59
def prefixEnd_5732737 : Nat := 4983230072969 + 3 ^ 40 * 5732737 * 2
def baseEnd_5732737 : Nat := 2943649546814042373823129

theorem tailTrace_5732737 : CollatzResearch.WordTrace tailWord_5732737 prefixEnd_5732737 2943649546814042373823129 := by
  unfold tailWord_5732737
  simp only [CollatzResearch.WordTrace]
  refine ⟨209090095832280397376684465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139393397221520264917789643 209090095832280397376684465)
  ·
    refine ⟨156817571874210298032513349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209090095832280397376684465 156817571874210298032513349)
    ·
      refine ⟨29403294726414430881096253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156817571874210298032513349 29403294726414430881096253)
      ·
        refine ⟨11026235522405411580411095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29403294726414430881096253 11026235522405411580411095)
        ·
          refine ⟨16539353283608117370616643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11026235522405411580411095 16539353283608117370616643)
          ·
            refine ⟨24809029925412176055924965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16539353283608117370616643 24809029925412176055924965)
            ·
              refine ⟨4651693111014783010485931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24809029925412176055924965 4651693111014783010485931)
              ·
                refine ⟨6977539666522174515728897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651693111014783010485931 6977539666522174515728897)
                ·
                  refine ⟨5233154749891630886796673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6977539666522174515728897 5233154749891630886796673)
                  ·
                    refine ⟨3924866062418723165097505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5233154749891630886796673 3924866062418723165097505)
                    ·
                      refine ⟨2943649546814042373823129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924866062418723165097505 2943649546814042373823129)
                      ·
                        rfl

theorem cell23_5732737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_5732737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732737 prefixEnd_5732737 := by exact prefixLift 5732737
  have htrace : WordTrace (prefixWord ++ tailWord_5732737) baseStart_5732737 baseEnd_5732737 := by
    simpa [prefixWord, tailWord_5732737, baseEnd_5732737] using wordTrace_append hprefix tailTrace_5732737
  have hstable : (prefixWord ++ tailWord_5732737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732737).length < 2 ^ (prefixWord ++ tailWord_5732737).sum := by decide
  have hdescent : baseEnd_5732737 < baseStart_5732737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732759 : List Nat := [1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_5732759 : Nat := 118140960795 + 5732759 * 2 ^ 59
def prefixEnd_5732759 : Nat := 4983230072969 + 3 ^ 40 * 5732759 * 2
def baseEnd_5732759 : Nat := 2943660843388441287748027

theorem tailTrace_5732759 : CollatzResearch.WordTrace tailWord_5732759 prefixEnd_5732759 2943660843388441287748027 := by
  unfold tailWord_5732759
  simp only [CollatzResearch.WordTrace]
  refine ⟨209090898238200695133985331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139393932158800463422656887 209090898238200695133985331)
  ·
    refine ⟨313636347357301042700977997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209090898238200695133985331 313636347357301042700977997)
    ·
      refine ⟨117613630258987891012866749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313636347357301042700977997 117613630258987891012866749)
      ·
        refine ⟨44105111347120459129825031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117613630258987891012866749 44105111347120459129825031)
        ·
          refine ⟨66157667020680688694737547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44105111347120459129825031 66157667020680688694737547)
          ·
            refine ⟨99236500531021033042106321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66157667020680688694737547 99236500531021033042106321)
            ·
              refine ⟨74427375398265774781579741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99236500531021033042106321 74427375398265774781579741)
              ·
                refine ⟨27910265774349665543092403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74427375398265774781579741 27910265774349665543092403)
                ·
                  refine ⟨41865398661524498314638605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27910265774349665543092403 41865398661524498314638605)
                  ·
                    refine ⟨15699524498071686867989477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41865398661524498314638605 15699524498071686867989477)
                    ·
                      refine ⟨2943660843388441287748027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15699524498071686867989477 2943660843388441287748027)
                      ·
                        rfl

theorem cell23_5732759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_5732759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732759 prefixEnd_5732759 := by exact prefixLift 5732759
  have htrace : WordTrace (prefixWord ++ tailWord_5732759) baseStart_5732759 baseEnd_5732759 := by
    simpa [prefixWord, tailWord_5732759, baseEnd_5732759] using wordTrace_append hprefix tailTrace_5732759
  have hstable : (prefixWord ++ tailWord_5732759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732759).length < 2 ^ (prefixWord ++ tailWord_5732759).sum := by decide
  have hdescent : baseEnd_5732759 < baseStart_5732759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732786 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_5732786 : Nat := 118140960795 + 5732786 * 2 ^ 59
def prefixEnd_5732786 : Nat := 4983230072969 + 3 ^ 40 * 5732786 * 2
def baseEnd_5732786 : Nat := 981224902455370894036801

theorem tailTrace_5732786 : CollatzResearch.WordTrace tailWord_5732786 prefixEnd_5732786 981224902455370894036801 := by
  unfold tailWord_5732786
  simp only [CollatzResearch.WordTrace]
  refine ⟨52272970752275719686304553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139394588672735252496812141 52272970752275719686304553)
  ·
    refine ⟨39204728064206789764728415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52272970752275719686304553 39204728064206789764728415)
    ·
      refine ⟨58807092096310184647092623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39204728064206789764728415 58807092096310184647092623)
      ·
        refine ⟨88210638144465276970638935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58807092096310184647092623 88210638144465276970638935)
        ·
          refine ⟨132315957216697915455958403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88210638144465276970638935 132315957216697915455958403)
          ·
            refine ⟨198473935825046873183937605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132315957216697915455958403 198473935825046873183937605)
            ·
              refine ⟨37213862967196288721988301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198473935825046873183937605 37213862967196288721988301)
              ·
                refine ⟨13955198612698608270745613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37213862967196288721988301 13955198612698608270745613)
                ·
                  refine ⟨5233199479761978101529605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13955198612698608270745613 5233199479761978101529605)
                  ·
                    refine ⟨981224902455370894036801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5233199479761978101529605 981224902455370894036801)
                    ·
                      rfl

theorem cell23_5732786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_5732786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732786 prefixEnd_5732786 := by exact prefixLift 5732786
  have htrace : WordTrace (prefixWord ++ tailWord_5732786) baseStart_5732786 baseEnd_5732786 := by
    simpa [prefixWord, tailWord_5732786, baseEnd_5732786] using wordTrace_append hprefix tailTrace_5732786
  have hstable : (prefixWord ++ tailWord_5732786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732786).length < 2 ^ (prefixWord ++ tailWord_5732786).sum := by decide
  have hdescent : baseEnd_5732786 < baseStart_5732786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732793 : List Nat := [1, 2, 1, 4, 3, 2, 1, 1, 2, 4, 2]
def baseStart_5732793 : Nat := 118140960795 + 5732793 * 2 ^ 59
def prefixEnd_5732793 : Nat := 4983230072969 + 3 ^ 40 * 5732793 * 2
def baseEnd_5732793 : Nat := 2943678301730694154722871

theorem tailTrace_5732793 : CollatzResearch.WordTrace tailWord_5732793 prefixEnd_5732793 2943678301730694154722871 := by
  unfold tailWord_5732793
  simp only [CollatzResearch.WordTrace]
  refine ⟨209092138320077518940723033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139394758880051679293815355 209092138320077518940723033)
  ·
    refine ⟨156819103740058139205542275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209092138320077518940723033 156819103740058139205542275)
    ·
      refine ⟨235228655610087208808313413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156819103740058139205542275 235228655610087208808313413)
      ·
        refine ⟨44105372926891351651558765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235228655610087208808313413 44105372926891351651558765)
        ·
          refine ⟨16539514847584256869334537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44105372926891351651558765 16539514847584256869334537)
          ·
            refine ⟨12404636135688192652000903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16539514847584256869334537 12404636135688192652000903)
            ·
              refine ⟨18606954203532288978001355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12404636135688192652000903 18606954203532288978001355)
              ·
                refine ⟨27910431305298433467002033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18606954203532288978001355 27910431305298433467002033)
                ·
                  refine ⟨20932823478973825100251525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27910431305298433467002033 20932823478973825100251525)
                  ·
                    refine ⟨3924904402307592206297161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20932823478973825100251525 3924904402307592206297161)
                    ·
                      refine ⟨2943678301730694154722871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924904402307592206297161 2943678301730694154722871)
                      ·
                        rfl

theorem cell23_5732793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_5732793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732793 prefixEnd_5732793 := by exact prefixLift 5732793
  have htrace : WordTrace (prefixWord ++ tailWord_5732793) baseStart_5732793 baseEnd_5732793 := by
    simpa [prefixWord, tailWord_5732793, baseEnd_5732793] using wordTrace_append hprefix tailTrace_5732793
  have hstable : (prefixWord ++ tailWord_5732793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732793).length < 2 ^ (prefixWord ++ tailWord_5732793).sum := by decide
  have hdescent : baseEnd_5732793 < baseStart_5732793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732820 : List Nat := [2, 4, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_5732820 : Nat := 118140960795 + 5732820 * 2 ^ 59
def prefixEnd_5732820 : Nat := 4983230072969 + 3 ^ 40 * 5732820 * 2
def baseEnd_5732820 : Nat := 981230721902788516361749

theorem tailTrace_5732820 : CollatzResearch.WordTrace tailWord_5732820 prefixEnd_5732820 981230721902788516361749 := by
  unfold tailWord_5732820
  simp only [CollatzResearch.WordTrace]
  refine ⟨104546561545489851275977957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139395415393986468367970609 104546561545489851275977957)
  ·
    refine ⟨19602480289779347114245867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104546561545489851275977957 19602480289779347114245867)
    ·
      refine ⟨29403720434669020671368801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19602480289779347114245867 29403720434669020671368801)
      ·
        refine ⟨22052790326001765503526601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29403720434669020671368801 22052790326001765503526601)
        ·
          refine ⟨16539592744501324127644951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22052790326001765503526601 16539592744501324127644951)
          ·
            refine ⟨24809389116751986191467427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16539592744501324127644951 24809389116751986191467427)
            ·
              refine ⟨37214083675127979287201141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24809389116751986191467427 37214083675127979287201141)
              ·
                refine ⟨3488820344543248058175107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37214083675127979287201141 3488820344543248058175107)
                ·
                  refine ⟨5233230516814872087262661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3488820344543248058175107 5233230516814872087262661)
                  ·
                    refine ⟨981230721902788516361749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5233230516814872087262661 981230721902788516361749)
                    ·
                      rfl

theorem cell23_5732820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_5732820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732820 prefixEnd_5732820 := by exact prefixLift 5732820
  have htrace : WordTrace (prefixWord ++ tailWord_5732820) baseStart_5732820 baseEnd_5732820 := by
    simpa [prefixWord, tailWord_5732820, baseEnd_5732820] using wordTrace_append hprefix tailTrace_5732820
  have hstable : (prefixWord ++ tailWord_5732820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732820).length < 2 ^ (prefixWord ++ tailWord_5732820).sum := by decide
  have hdescent : baseEnd_5732820 < baseStart_5732820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732843 : List Nat := [1, 1, 1, 1, 2, 3, 6, 1, 3, 1, 3]
def baseStart_5732843 : Nat := 118140960795 + 5732843 * 2 ^ 59
def prefixEnd_5732843 : Nat := 4983230072969 + 3 ^ 40 * 5732843 * 2
def baseEnd_5732843 : Nat := 2943703975763418959097641

theorem tailTrace_5732843 : CollatzResearch.WordTrace tailWord_5732843 prefixEnd_5732843 2943703975763418959097641 := by
  unfold tailWord_5732843
  simp only [CollatzResearch.WordTrace]
  refine ⟨209093961969896377480043183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139395974646597584986695455 209093961969896377480043183)
  ·
    refine ⟨313640942954844566220064775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209093961969896377480043183 313640942954844566220064775)
    ·
      refine ⟨470461414432266849330097163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313640942954844566220064775 470461414432266849330097163)
      ·
        refine ⟨705692121648400273995145745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470461414432266849330097163 705692121648400273995145745)
        ·
          refine ⟨529269091236300205496359309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705692121648400273995145745 529269091236300205496359309)
          ·
            refine ⟨198475909213612577061134741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 529269091236300205496359309 198475909213612577061134741)
            ·
              refine ⟨9303558244388089549740691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 198475909213612577061134741 9303558244388089549740691)
              ·
                refine ⟨13955337366582134324611037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9303558244388089549740691 13955337366582134324611037)
                ·
                  refine ⟨5233251512468300371729139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13955337366582134324611037 5233251512468300371729139)
                  ·
                    refine ⟨7849877268702450557593709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5233251512468300371729139 7849877268702450557593709)
                    ·
                      refine ⟨2943703975763418959097641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7849877268702450557593709 2943703975763418959097641)
                      ·
                        rfl

theorem cell23_5732843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 1, 3].length) (baseStart_5732843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732843 prefixEnd_5732843 := by exact prefixLift 5732843
  have htrace : WordTrace (prefixWord ++ tailWord_5732843) baseStart_5732843 baseEnd_5732843 := by
    simpa [prefixWord, tailWord_5732843, baseEnd_5732843] using wordTrace_append hprefix tailTrace_5732843
  have hstable : (prefixWord ++ tailWord_5732843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732843).length < 2 ^ (prefixWord ++ tailWord_5732843).sum := by decide
  have hdescent : baseEnd_5732843 < baseStart_5732843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732850 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 6]
def baseStart_5732850 : Nat := 118140960795 + 5732850 * 2 ^ 59
def prefixEnd_5732850 : Nat := 4983230072969 + 3 ^ 40 * 5732850 * 2
def baseEnd_5732850 : Nat := 327078618903111159078901

theorem tailTrace_5732850 : CollatzResearch.WordTrace tailWord_5732850 prefixEnd_5732850 327078618903111159078901 := by
  unfold tailWord_5732850
  simp only [CollatzResearch.WordTrace]
  refine ⟨52273554320217754418887001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139396144853914011783698669 52273554320217754418887001)
  ·
    refine ⟨39205165740163315814165251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52273554320217754418887001 39205165740163315814165251)
    ·
      refine ⟨58807748610244973721247877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39205165740163315814165251 58807748610244973721247877)
      ·
        refine ⟨11026452864420932572733977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58807748610244973721247877 11026452864420932572733977)
        ·
          refine ⟨8269839648315699429550483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11026452864420932572733977 8269839648315699429550483)
          ·
            refine ⟨12404759472473549144325725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8269839648315699429550483 12404759472473549144325725)
            ·
              refine ⟨4651784802177580929122147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12404759472473549144325725 4651784802177580929122147)
              ·
                refine ⟨6977677203266371393683221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651784802177580929122147 6977677203266371393683221)
                ·
                  refine ⟨327078618903111159078901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6977677203266371393683221 327078618903111159078901)
                  ·
                    rfl

theorem cell23_5732850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_5732850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732850 prefixEnd_5732850 := by exact prefixLift 5732850
  have htrace : WordTrace (prefixWord ++ tailWord_5732850) baseStart_5732850 baseEnd_5732850 := by
    simpa [prefixWord, tailWord_5732850, baseEnd_5732850] using wordTrace_append hprefix tailTrace_5732850
  have hstable : (prefixWord ++ tailWord_5732850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732850).length < 2 ^ (prefixWord ++ tailWord_5732850).sum := by decide
  have hdescent : baseEnd_5732850 < baseStart_5732850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732879 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_5732879 : Nat := 118140960795 + 5732879 * 2 ^ 59
def prefixEnd_5732879 : Nat := 4983230072969 + 3 ^ 40 * 5732879 * 2
def baseEnd_5732879 : Nat := 2943722461066980818247475

theorem tailTrace_5732879 : CollatzResearch.WordTrace tailWord_5732879 prefixEnd_5732879 2943722461066980818247475 := by
  unfold tailWord_5732879
  simp only [CollatzResearch.WordTrace]
  refine ⟨209095274997765955628353691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139396849998510637085569127 209095274997765955628353691)
  ·
    refine ⟨313642912496648933442530537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209095274997765955628353691 313642912496648933442530537)
    ·
      refine ⟨235232184372486700081897903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313642912496648933442530537 235232184372486700081897903)
      ·
        refine ⟨352848276558730050122846855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235232184372486700081897903 352848276558730050122846855)
        ·
          refine ⟨529272414838095075184270283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352848276558730050122846855 529272414838095075184270283)
          ·
            refine ⟨793908622257142612776405425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529272414838095075184270283 793908622257142612776405425)
            ·
              refine ⟨595431466692856959582304069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793908622257142612776405425 595431466692856959582304069)
              ·
                refine ⟨111643400004910679921682013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 595431466692856959582304069 111643400004910679921682013)
                ·
                  refine ⟨41866275001841504970630755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111643400004910679921682013 41866275001841504970630755)
                  ·
                    refine ⟨62799412502762257455946133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41866275001841504970630755 62799412502762257455946133)
                    ·
                      refine ⟨2943722461066980818247475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62799412502762257455946133 2943722461066980818247475)
                      ·
                        rfl

theorem cell23_5732879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_5732879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732879 prefixEnd_5732879 := by exact prefixLift 5732879
  have htrace : WordTrace (prefixWord ++ tailWord_5732879) baseStart_5732879 baseEnd_5732879 := by
    simpa [prefixWord, tailWord_5732879, baseEnd_5732879] using wordTrace_append hprefix tailTrace_5732879
  have hstable : (prefixWord ++ tailWord_5732879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732879).length < 2 ^ (prefixWord ++ tailWord_5732879).sum := by decide
  have hdescent : baseEnd_5732879 < baseStart_5732879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732887 : List Nat := [1, 1, 3, 6, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5732887 : Nat := 118140960795 + 5732887 * 2 ^ 59
def prefixEnd_5732887 : Nat := 4983230072969 + 3 ^ 40 * 5732887 * 2
def baseEnd_5732887 : Nat := 2943726568912216786947439

theorem tailTrace_5732887 : CollatzResearch.WordTrace tailWord_5732887 prefixEnd_5732887 2943726568912216786947439 := by
  unfold tailWord_5732887
  simp only [CollatzResearch.WordTrace]
  refine ⟨209095566781736972994644915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139397044521157981996429943 209095566781736972994644915)
  ·
    refine ⟨313643350172605459491967373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209095566781736972994644915 313643350172605459491967373)
    ·
      refine ⟨117616256314727047309487765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313643350172605459491967373 117616256314727047309487765)
      ·
        refine ⟨5513262014752830342632239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117616256314727047309487765 5513262014752830342632239)
        ·
          refine ⟨8269893022129245513948359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5513262014752830342632239 8269893022129245513948359)
          ·
            refine ⟨12404839533193868270922539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8269893022129245513948359 12404839533193868270922539)
            ·
              refine ⟨18607259299790802406383809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12404839533193868270922539 18607259299790802406383809)
              ·
                refine ⟨13955444474843101804787857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18607259299790802406383809 13955444474843101804787857)
                ·
                  refine ⟨10466583356132326353590893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13955444474843101804787857 10466583356132326353590893)
                  ·
                    refine ⟨3924968758549622382596585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10466583356132326353590893 3924968758549622382596585)
                    ·
                      refine ⟨2943726568912216786947439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3924968758549622382596585 2943726568912216786947439)
                      ·
                        rfl

theorem cell23_5732887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5732887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732887 prefixEnd_5732887 := by exact prefixLift 5732887
  have htrace : WordTrace (prefixWord ++ tailWord_5732887) baseStart_5732887 baseEnd_5732887 := by
    simpa [prefixWord, tailWord_5732887, baseEnd_5732887] using wordTrace_append hprefix tailTrace_5732887
  have hstable : (prefixWord ++ tailWord_5732887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732887).length < 2 ^ (prefixWord ++ tailWord_5732887).sum := by decide
  have hdescent : baseEnd_5732887 < baseStart_5732887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732893 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_5732893 : Nat := 118140960795 + 5732893 * 2 ^ 59
def prefixEnd_5732893 : Nat := 4983230072969 + 3 ^ 40 * 5732893 * 2
def baseEnd_5732893 : Nat := 981243216598714587824137

theorem tailTrace_5732893 : CollatzResearch.WordTrace tailWord_5732893 prefixEnd_5732893 981243216598714587824137 := by
  unfold tailWord_5732893
  simp only [CollatzResearch.WordTrace]
  refine ⟨209095785619715236019363333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139397190413143490679575555 209095785619715236019363333)
  ·
    refine ⟨39205459803696606753630625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209095785619715236019363333 39205459803696606753630625)
    ·
      refine ⟨29404094852772455065222969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39205459803696606753630625 29404094852772455065222969)
      ·
        refine ⟨22053071139579341298917227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29404094852772455065222969 22053071139579341298917227)
        ·
          refine ⟨33079606709369011948375841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22053071139579341298917227 33079606709369011948375841)
          ·
            refine ⟨24809705032026758961281881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33079606709369011948375841 24809705032026758961281881)
            ·
              refine ⟨18607278774020069220961411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24809705032026758961281881 18607278774020069220961411)
              ·
                refine ⟨27910918161030103831442117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18607278774020069220961411 27910918161030103831442117)
                ·
                  refine ⟨5233297155193144468395397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27910918161030103831442117 5233297155193144468395397)
                  ·
                    refine ⟨981243216598714587824137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5233297155193144468395397 981243216598714587824137)
                    ·
                      rfl

theorem cell23_5732893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_5732893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732893 prefixEnd_5732893 := by exact prefixLift 5732893
  have htrace : WordTrace (prefixWord ++ tailWord_5732893) baseStart_5732893 baseEnd_5732893 := by
    simpa [prefixWord, tailWord_5732893, baseEnd_5732893] using wordTrace_append hprefix tailTrace_5732893
  have hstable : (prefixWord ++ tailWord_5732893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732893).length < 2 ^ (prefixWord ++ tailWord_5732893).sum := by decide
  have hdescent : baseEnd_5732893 < baseStart_5732893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732906 : List Nat := [3, 1, 4, 1, 1, 2, 1, 10]
def baseStart_5732906 : Nat := 118140960795 + 5732906 * 2 ^ 59
def prefixEnd_5732906 : Nat := 4983230072969 + 3 ^ 40 * 5732906 * 2
def baseEnd_5732906 : Nat := 109027271297950081948513

theorem tailTrace_5732906 : CollatzResearch.WordTrace tailWord_5732906 prefixEnd_5732906 109027271297950081948513 := by
  unfold tailWord_5732906
  simp only [CollatzResearch.WordTrace]
  refine ⟨52274064942167034809896643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139397506512445426159724381 52274064942167034809896643)
  ·
    refine ⟨78411097413250552214844965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52274064942167034809896643 78411097413250552214844965)
    ·
      refine ⟨14702080764984478540283431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78411097413250552214844965 14702080764984478540283431)
      ·
        refine ⟨22053121147476717810425147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14702080764984478540283431 22053121147476717810425147)
        ·
          refine ⟨33079681721215076715637721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22053121147476717810425147 33079681721215076715637721)
          ·
            refine ⟨24809761290911307536728291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33079681721215076715637721 24809761290911307536728291)
            ·
              refine ⟨37214641936366961305092437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24809761290911307536728291 37214641936366961305092437)
              ·
                refine ⟨109027271297950081948513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37214641936366961305092437 109027271297950081948513)
                ·
                  rfl

theorem cell23_5732906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 10].length) (baseStart_5732906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732906 prefixEnd_5732906 := by exact prefixLift 5732906
  have htrace : WordTrace (prefixWord ++ tailWord_5732906) baseStart_5732906 baseEnd_5732906 := by
    simpa [prefixWord, tailWord_5732906, baseEnd_5732906] using wordTrace_append hprefix tailTrace_5732906
  have hstable : (prefixWord ++ tailWord_5732906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732906).length < 2 ^ (prefixWord ++ tailWord_5732906).sum := by decide
  have hdescent : baseEnd_5732906 < baseStart_5732906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732933 : List Nat := [1, 3, 1, 1, 1, 6, 1, 2, 1, 3, 3]
def baseStart_5732933 : Nat := 118140960795 + 5732933 * 2 ^ 59
def prefixEnd_5732933 : Nat := 4983230072969 + 3 ^ 40 * 5732933 * 2
def baseEnd_5732933 : Nat := 2943750189022323606972227

theorem tailTrace_5732933 : CollatzResearch.WordTrace tailWord_5732933 prefixEnd_5732933 2943750189022323606972227 := by
  unfold tailWord_5732933
  simp only [CollatzResearch.WordTrace]
  refine ⟨209097244539570322850819453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139398163026380215233879635 209097244539570322850819453)
  ·
    refine ⟨78411466702338871069057295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209097244539570322850819453 78411466702338871069057295)
    ·
      refine ⟨117617200053508306603585943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78411466702338871069057295 117617200053508306603585943)
      ·
        refine ⟨176425800080262459905378915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117617200053508306603585943 176425800080262459905378915)
        ·
          refine ⟨264638700120393689858068373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176425800080262459905378915 264638700120393689858068373)
          ·
            refine ⟨12404939068143454212096955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 264638700120393689858068373 12404939068143454212096955)
            ·
              refine ⟨18607408602215181318145433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12404939068143454212096955 18607408602215181318145433)
              ·
                refine ⟨13955556451661385988609075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18607408602215181318145433 13955556451661385988609075)
                ·
                  refine ⟨20933334677492078982913613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13955556451661385988609075 20933334677492078982913613)
                  ·
                    refine ⟨7850000504059529618592605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20933334677492078982913613 7850000504059529618592605)
                    ·
                      refine ⟨2943750189022323606972227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7850000504059529618592605 2943750189022323606972227)
                      ·
                        rfl

theorem cell23_5732933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_5732933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732933 prefixEnd_5732933 := by exact prefixLift 5732933
  have htrace : WordTrace (prefixWord ++ tailWord_5732933) baseStart_5732933 baseEnd_5732933 := by
    simpa [prefixWord, tailWord_5732933, baseEnd_5732933] using wordTrace_append hprefix tailTrace_5732933
  have hstable : (prefixWord ++ tailWord_5732933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732933).length < 2 ^ (prefixWord ++ tailWord_5732933).sum := by decide
  have hdescent : baseEnd_5732933 < baseStart_5732933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5732934 : List Nat := [6, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_5732934 : Nat := 118140960795 + 5732934 * 2 ^ 59
def prefixEnd_5732934 : Nat := 4983230072969 + 3 ^ 40 * 5732934 * 2
def baseEnd_5732934 : Nat := 2943750702502978103059723

theorem tailTrace_5732934 : CollatzResearch.WordTrace tailWord_5732934 prefixEnd_5732934 2943750702502978103059723 := by
  unfold tailWord_5732934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6534290031642709375675183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139398187341711133347737237 6534290031642709375675183)
  ·
    refine ⟨9801435047464064063512775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6534290031642709375675183 9801435047464064063512775)
    ·
      refine ⟨14702152571196096095269163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9801435047464064063512775 14702152571196096095269163)
      ·
        refine ⟨22053228856794144142903745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14702152571196096095269163 22053228856794144142903745)
        ·
          refine ⟨16539921642595608107177809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22053228856794144142903745 16539921642595608107177809)
          ·
            refine ⟨12404941231946706080383357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16539921642595608107177809 12404941231946706080383357)
            ·
              refine ⟨4651852961980014780143759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12404941231946706080383357 4651852961980014780143759)
              ·
                refine ⟨6977779442970022170215639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4651852961980014780143759 6977779442970022170215639)
                ·
                  refine ⟨10466669164455033255323459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6977779442970022170215639 10466669164455033255323459)
                  ·
                    refine ⟨15700003746682549882985189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10466669164455033255323459 15700003746682549882985189)
                    ·
                      refine ⟨2943750702502978103059723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15700003746682549882985189 2943750702502978103059723)
                      ·
                        rfl

theorem cell23_5732934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_5732934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5732934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5732934 prefixEnd_5732934 := by exact prefixLift 5732934
  have htrace : WordTrace (prefixWord ++ tailWord_5732934) baseStart_5732934 baseEnd_5732934 := by
    simpa [prefixWord, tailWord_5732934, baseEnd_5732934] using wordTrace_append hprefix tailTrace_5732934
  have hstable : (prefixWord ++ tailWord_5732934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5732934).length < 2 ^ (prefixWord ++ tailWord_5732934).sum := by decide
  have hdescent : baseEnd_5732934 < baseStart_5732934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5732934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733024 : List Nat := [2, 1, 1, 4, 5, 1, 1, 1, 1, 4, 2]
def baseStart_5733024 : Nat := 118140960795 + 5733024 * 2 ^ 59
def prefixEnd_5733024 : Nat := 4983230072969 + 3 ^ 40 * 5733024 * 2
def baseEnd_5733024 : Nat := 2943796915761882750934309

theorem tailTrace_5733024 : CollatzResearch.WordTrace tailWord_5733024 prefixEnd_5733024 2943796915761882750934309 := by
  unfold tailWord_5733024
  simp only [CollatzResearch.WordTrace]
  refine ⟨104550281791120322696191063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139400375721493763594921417 104550281791120322696191063)
  ·
    refine ⟨156825422686680484044286595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104550281791120322696191063 156825422686680484044286595)
    ·
      refine ⟨235238134030020726066429893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156825422686680484044286595 235238134030020726066429893)
      ·
        refine ⟨44107150130628886137455605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235238134030020726066429893 44107150130628886137455605)
        ·
          refine ⟨4135045324746458075386463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44107150130628886137455605 4135045324746458075386463)
          ·
            refine ⟨6202567987119687113079695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135045324746458075386463 6202567987119687113079695)
            ·
              refine ⟨9303851980679530669619543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6202567987119687113079695 9303851980679530669619543)
              ·
                refine ⟨13955777971019296004429315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9303851980679530669619543 13955777971019296004429315)
                ·
                  refine ⟨20933666956528944006643973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13955777971019296004429315 20933666956528944006643973)
                  ·
                    refine ⟨3925062554349177001245745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20933666956528944006643973 3925062554349177001245745)
                    ·
                      refine ⟨2943796915761882750934309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3925062554349177001245745 2943796915761882750934309)
                      ·
                        rfl

theorem cell23_5733024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_5733024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733024 prefixEnd_5733024 := by exact prefixLift 5733024
  have htrace : WordTrace (prefixWord ++ tailWord_5733024) baseStart_5733024 baseEnd_5733024 := by
    simpa [prefixWord, tailWord_5733024, baseEnd_5733024] using wordTrace_append hprefix tailTrace_5733024
  have hstable : (prefixWord ++ tailWord_5733024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733024).length < 2 ^ (prefixWord ++ tailWord_5733024).sum := by decide
  have hdescent : baseEnd_5733024 < baseStart_5733024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733033 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 4, 5, 2]
def baseStart_5733033 : Nat := 118140960795 + 5733033 * 2 ^ 59
def prefixEnd_5733033 : Nat := 4983230072969 + 3 ^ 40 * 5733033 * 2
def baseEnd_5733033 : Nat := 2943801537087773215721767

theorem tailTrace_5733033 : CollatzResearch.WordTrace tailWord_5733033 prefixEnd_5733033 2943801537087773215721767 := by
  unfold tailWord_5733033
  simp only [CollatzResearch.WordTrace]
  refine ⟨209100891839208039929459753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139400594559472026619639835 209100891839208039929459753)
  ·
    refine ⟨156825668879406029947094815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209100891839208039929459753 156825668879406029947094815)
    ·
      refine ⟨235238503319109044920642223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156825668879406029947094815 235238503319109044920642223)
      ·
        refine ⟨352857754978663567380963335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235238503319109044920642223 352857754978663567380963335)
        ·
          refine ⟨529286632467995351071445003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352857754978663567380963335 529286632467995351071445003)
          ·
            refine ⟨793929948701993026607167505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529286632467995351071445003 793929948701993026607167505)
            ·
              refine ⟨595447461526494769955375629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 793929948701993026607167505 595447461526494769955375629)
              ·
                refine ⟨223292798072435538733265861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 595447461526494769955375629 223292798072435538733265861)
                ·
                  refine ⟨41867399638581663512487349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223292798072435538733265861 41867399638581663512487349)
                  ·
                    refine ⟨3925068716117030954295689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41867399638581663512487349 3925068716117030954295689)
                    ·
                      refine ⟨2943801537087773215721767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3925068716117030954295689 2943801537087773215721767)
                      ·
                        rfl

theorem cell23_5733033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 5, 2].length) (baseStart_5733033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733033 prefixEnd_5733033 := by exact prefixLift 5733033
  have htrace : WordTrace (prefixWord ++ tailWord_5733033) baseStart_5733033 baseEnd_5733033 := by
    simpa [prefixWord, tailWord_5733033, baseEnd_5733033] using wordTrace_append hprefix tailTrace_5733033
  have hstable : (prefixWord ++ tailWord_5733033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733033).length < 2 ^ (prefixWord ++ tailWord_5733033).sum := by decide
  have hdescent : baseEnd_5733033 < baseStart_5733033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733047 : List Nat := [1, 1, 3, 1, 6, 2, 1, 3, 5]
def baseStart_5733047 : Nat := 118140960795 + 5733047 * 2 ^ 59
def prefixEnd_5733047 : Nat := 4983230072969 + 3 ^ 40 * 5733047 * 2
def baseEnd_5733047 : Nat := 327089858424104017882967

theorem tailTrace_5733047 : CollatzResearch.WordTrace tailWord_5733047 prefixEnd_5733047 327089858424104017882967 := by
  unfold tailWord_5733047
  simp only [CollatzResearch.WordTrace]
  refine ⟨209101402461157320320469395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139400934974104880213646263 209101402461157320320469395)
  ·
    refine ⟨313652103691735980480704093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209101402461157320320469395 313652103691735980480704093)
    ·
      refine ⟨117619538884400992680264035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313652103691735980480704093 117619538884400992680264035)
      ·
        refine ⟨176429308326601489020396053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117619538884400992680264035 176429308326601489020396053)
        ·
          refine ⟨8270123827809444797831065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 176429308326601489020396053 8270123827809444797831065)
          ·
            refine ⟨6202592870857083598373299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8270123827809444797831065 6202592870857083598373299)
            ·
              refine ⟨9303889306285625397559949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6202592870857083598373299 9303889306285625397559949)
              ·
                refine ⟨3488958489857109524084981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9303889306285625397559949 3488958489857109524084981)
                ·
                  refine ⟨327089858424104017882967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3488958489857109524084981 327089858424104017882967)
                  ·
                    rfl

theorem cell23_5733047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 3, 5].length) (baseStart_5733047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733047 prefixEnd_5733047 := by exact prefixLift 5733047
  have htrace : WordTrace (prefixWord ++ tailWord_5733047) baseStart_5733047 baseEnd_5733047 := by
    simpa [prefixWord, tailWord_5733047, baseEnd_5733047] using wordTrace_append hprefix tailTrace_5733047
  have hstable : (prefixWord ++ tailWord_5733047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733047).length < 2 ^ (prefixWord ++ tailWord_5733047).sum := by decide
  have hdescent : baseEnd_5733047 < baseStart_5733047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733060 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 2, 5]
def baseStart_5733060 : Nat := 118140960795 + 5733060 * 2 ^ 59
def prefixEnd_5733060 : Nat := 4983230072969 + 3 ^ 40 * 5733060 * 2
def baseEnd_5733060 : Nat := 981271800355148203361381

theorem tailTrace_5733060 : CollatzResearch.WordTrace tailWord_5733060 prefixEnd_5733060 981271800355148203361381 := by
  unfold tailWord_5733060
  simp only [CollatzResearch.WordTrace]
  refine ⟨104550938305055111770346317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139401251073406815693795089 104550938305055111770346317)
  ·
    refine ⟨39206601864395666913879869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104550938305055111770346317 39206601864395666913879869)
    ·
      refine ⟨14702475699148375092704951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39206601864395666913879869 14702475699148375092704951)
      ·
        refine ⟨22053713548722562639057427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14702475699148375092704951 22053713548722562639057427)
        ·
          refine ⟨33080570323083843958586141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22053713548722562639057427 33080570323083843958586141)
          ·
            refine ⟨12405213871156441484469803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33080570323083843958586141 12405213871156441484469803)
            ·
              refine ⟨18607820806734662226704705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12405213871156441484469803 18607820806734662226704705)
              ·
                refine ⟨13955865605050996670028529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18607820806734662226704705 13955865605050996670028529)
                ·
                  refine ⟨10466899203788247502521397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13955865605050996670028529 10466899203788247502521397)
                  ·
                    refine ⟨981271800355148203361381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10466899203788247502521397 981271800355148203361381)
                    ·
                      rfl

theorem cell23_5733060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_5733060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733060 prefixEnd_5733060 := by exact prefixLift 5733060
  have htrace : WordTrace (prefixWord ++ tailWord_5733060) baseStart_5733060 baseEnd_5733060 := by
    simpa [prefixWord, tailWord_5733060, baseEnd_5733060] using wordTrace_append hprefix tailTrace_5733060
  have hstable : (prefixWord ++ tailWord_5733060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733060).length < 2 ^ (prefixWord ++ tailWord_5733060).sum := by decide
  have hdescent : baseEnd_5733060 < baseStart_5733060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733164 : List Nat := [2, 2, 1, 1, 1, 4, 4, 3, 1, 1, 3]
def baseStart_5733164 : Nat := 118140960795 + 5733164 * 2 ^ 59
def prefixEnd_5733164 : Nat := 4983230072969 + 3 ^ 40 * 5733164 * 2
def baseEnd_5733164 : Nat := 2943868803053512203183665

theorem tailTrace_5733164 : CollatzResearch.WordTrace tailWord_5733164 prefixEnd_5733164 2943868803053512203183665 := by
  unfold tailWord_5733164
  simp only [CollatzResearch.WordTrace]
  refine ⟨104552834900866724651239273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139403779867822299534985697 104552834900866724651239273)
  ·
    refine ⟨78414626175650043488429455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104552834900866724651239273 78414626175650043488429455)
    ·
      refine ⟨117621939263475065232644183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78414626175650043488429455 117621939263475065232644183)
      ·
        refine ⟨176432908895212597848966275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117621939263475065232644183 176432908895212597848966275)
        ·
          refine ⟨264649363342818896773449413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176432908895212597848966275 264649363342818896773449413)
          ·
            refine ⟨49621755626778543145021765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264649363342818896773449413 49621755626778543145021765)
            ·
              refine ⟨9304079180020976839691581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49621755626778543145021765 9304079180020976839691581)
              ·
                refine ⟨3489029692507866314884343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9304079180020976839691581 3489029692507866314884343)
                ·
                  refine ⟨5233544538761799472326515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3489029692507866314884343 5233544538761799472326515)
                  ·
                    refine ⟨7850316808142699208489773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5233544538761799472326515 7850316808142699208489773)
                    ·
                      refine ⟨2943868803053512203183665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7850316808142699208489773 2943868803053512203183665)
                      ·
                        rfl

theorem cell23_5733164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 1, 1, 3].length) (baseStart_5733164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733164 prefixEnd_5733164 := by exact prefixLift 5733164
  have htrace : WordTrace (prefixWord ++ tailWord_5733164) baseStart_5733164 baseEnd_5733164 := by
    simpa [prefixWord, tailWord_5733164, baseEnd_5733164] using wordTrace_append hprefix tailTrace_5733164
  have hstable : (prefixWord ++ tailWord_5733164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733164).length < 2 ^ (prefixWord ++ tailWord_5733164).sum := by decide
  have hdescent : baseEnd_5733164 < baseStart_5733164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733200 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 4]
def baseStart_5733200 : Nat := 118140960795 + 5733200 * 2 ^ 59
def prefixEnd_5733200 : Nat := 4983230072969 + 3 ^ 40 * 5733200 * 2
def baseEnd_5733200 : Nat := 2943887288357074062333499

theorem tailTrace_5733200 : CollatzResearch.WordTrace tailWord_5733200 prefixEnd_5733200 2943887288357074062333499 := by
  unfold tailWord_5733200
  simp only [CollatzResearch.WordTrace]
  refine ⟨104553491414801513725394527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139404655219735351633859369 104553491414801513725394527)
  ·
    refine ⟨156830237122202270588091791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104553491414801513725394527 156830237122202270588091791)
    ·
      refine ⟨235245355683303405882137687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156830237122202270588091791 235245355683303405882137687)
      ·
        refine ⟨352868033524955108823206531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235245355683303405882137687 352868033524955108823206531)
        ·
          refine ⟨529302050287432663234809797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352868033524955108823206531 529302050287432663234809797)
          ·
            refine ⟨99244134428893624356526837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 529302050287432663234809797 99244134428893624356526837)
            ·
              refine ⟨9304137602708777283424391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99244134428893624356526837 9304137602708777283424391)
              ·
                refine ⟨13956206404063165925136587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9304137602708777283424391 13956206404063165925136587)
                ·
                  refine ⟨20934309606094748887704881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13956206404063165925136587 20934309606094748887704881)
                  ·
                    refine ⟨15700732204571061665778661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20934309606094748887704881 15700732204571061665778661)
                    ·
                      refine ⟨2943887288357074062333499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15700732204571061665778661 2943887288357074062333499)
                      ·
                        rfl

theorem cell23_5733200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 4].length) (baseStart_5733200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733200 prefixEnd_5733200 := by exact prefixLift 5733200
  have htrace : WordTrace (prefixWord ++ tailWord_5733200) baseStart_5733200 baseEnd_5733200 := by
    simpa [prefixWord, tailWord_5733200, baseEnd_5733200] using wordTrace_append hprefix tailTrace_5733200
  have hstable : (prefixWord ++ tailWord_5733200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733200).length < 2 ^ (prefixWord ++ tailWord_5733200).sum := by decide
  have hdescent : baseEnd_5733200 < baseStart_5733200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733204 : List Nat := [2, 4, 1, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_5733204 : Nat := 118140960795 + 5733204 * 2 ^ 59
def prefixEnd_5733204 : Nat := 4983230072969 + 3 ^ 40 * 5733204 * 2
def baseEnd_5733204 : Nat := 2943889342279692046683481

theorem tailTrace_5733204 : CollatzResearch.WordTrace tailWord_5733204 prefixEnd_5733204 2943889342279692046683481 := by
  unfold tailWord_5733204
  simp only [CollatzResearch.WordTrace]
  refine ⟨104553564360794268066967333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139404752481059024089289777 104553564360794268066967333)
  ·
    refine ⟨19603793317648925262556375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104553564360794268066967333 19603793317648925262556375)
    ·
      refine ⟨29405689976473387893834563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19603793317648925262556375 29405689976473387893834563)
      ·
        refine ⟨44108534964710081840751845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29405689976473387893834563 44108534964710081840751845)
        ·
          refine ⟨8270350305883140345140971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44108534964710081840751845 8270350305883140345140971)
          ·
            refine ⟨12405525458824710517711457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8270350305883140345140971 12405525458824710517711457)
            ·
              refine ⟨9304144094118532888283593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12405525458824710517711457 9304144094118532888283593)
              ·
                refine ⟨6978108070588899666212695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9304144094118532888283593 6978108070588899666212695)
                ·
                  refine ⟨10467162105883349499319043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6978108070588899666212695 10467162105883349499319043)
                  ·
                    refine ⟨15700743158825024248978565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10467162105883349499319043 15700743158825024248978565)
                    ·
                      refine ⟨2943889342279692046683481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15700743158825024248978565 2943889342279692046683481)
                      ·
                        rfl

theorem cell23_5733204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_5733204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733204 prefixEnd_5733204 := by exact prefixLift 5733204
  have htrace : WordTrace (prefixWord ++ tailWord_5733204) baseStart_5733204 baseEnd_5733204 := by
    simpa [prefixWord, tailWord_5733204, baseEnd_5733204] using wordTrace_append hprefix tailTrace_5733204
  have hstable : (prefixWord ++ tailWord_5733204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733204).length < 2 ^ (prefixWord ++ tailWord_5733204).sum := by decide
  have hdescent : baseEnd_5733204 < baseStart_5733204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733207 : List Nat := [1, 1, 3, 2, 4, 1, 1, 4, 1, 2, 3]
def baseStart_5733207 : Nat := 118140960795 + 5733207 * 2 ^ 59
def prefixEnd_5733207 : Nat := 4983230072969 + 3 ^ 40 * 5733207 * 2
def baseEnd_5733207 : Nat := 2943890882721655534945967

theorem tailTrace_5733207 : CollatzResearch.WordTrace tailWord_5733207 prefixEnd_5733207 2943890882721655534945967 := by
  unfold tailWord_5733207
  simp only [CollatzResearch.WordTrace]
  refine ⟨209107238140577667646293875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139404825427051778430862583 209107238140577667646293875)
  ·
    refine ⟨313660857210866501469440813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209107238140577667646293875 313660857210866501469440813)
    ·
      refine ⟨117622821454074938051040305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313660857210866501469440813 117622821454074938051040305)
      ·
        refine ⟨88217116090556203538280229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117622821454074938051040305 88217116090556203538280229)
        ·
          refine ⟨16540709266979288163427543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88217116090556203538280229 16540709266979288163427543)
          ·
            refine ⟨24811063900468932245141315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16540709266979288163427543 24811063900468932245141315)
            ·
              refine ⟨37216595850703398367711973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24811063900468932245141315 37216595850703398367711973)
              ·
                refine ⟨6978111722006887193945995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37216595850703398367711973 6978111722006887193945995)
                ·
                  refine ⟨10467167583010330790918993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6978111722006887193945995 10467167583010330790918993)
                  ·
                    refine ⟨7850375687257748093189245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10467167583010330790918993 7850375687257748093189245)
                    ·
                      refine ⟨2943890882721655534945967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7850375687257748093189245 2943890882721655534945967)
                      ·
                        rfl

theorem cell23_5733207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_5733207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733207 prefixEnd_5733207 := by exact prefixLift 5733207
  have htrace : WordTrace (prefixWord ++ tailWord_5733207) baseStart_5733207 baseEnd_5733207 := by
    simpa [prefixWord, tailWord_5733207, baseEnd_5733207] using wordTrace_append hprefix tailTrace_5733207
  have hstable : (prefixWord ++ tailWord_5733207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733207).length < 2 ^ (prefixWord ++ tailWord_5733207).sum := by decide
  have hdescent : baseEnd_5733207 < baseStart_5733207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733210 : List Nat := [3, 1, 1, 2, 1, 4, 4, 7]
def baseStart_5733210 : Nat := 118140960795 + 5733210 * 2 ^ 59
def prefixEnd_5733210 : Nat := 4983230072969 + 3 ^ 40 * 5733210 * 2
def baseEnd_5733210 : Nat := 109033052709763667526239

theorem tailTrace_5733210 : CollatzResearch.WordTrace tailWord_5733210 prefixEnd_5733210 109033052709763667526239 := by
  unfold tailWord_5733210
  simp only [CollatzResearch.WordTrace]
  refine ⟨52276836889891699789663271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139404898373044532772435389 52276836889891699789663271)
  ·
    refine ⟨78415255334837549684494907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52276836889891699789663271 78415255334837549684494907)
    ·
      refine ⟨117622883002256324526742361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78415255334837549684494907 117622883002256324526742361)
      ·
        refine ⟨88217162251692243395056771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117622883002256324526742361 88217162251692243395056771)
        ·
          refine ⟨132325743377538365092585157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88217162251692243395056771 132325743377538365092585157)
          ·
            refine ⟨24811076883288443454859717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132325743377538365092585157 24811076883288443454859717)
            ·
              refine ⟨4652076915616583147786197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24811076883288443454859717 4652076915616583147786197)
              ·
                refine ⟨109033052709763667526239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4652076915616583147786197 109033052709763667526239)
                ·
                  rfl

theorem cell23_5733210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 7].length) (baseStart_5733210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733210 prefixEnd_5733210 := by exact prefixLift 5733210
  have htrace : WordTrace (prefixWord ++ tailWord_5733210) baseStart_5733210 baseEnd_5733210 := by
    simpa [prefixWord, tailWord_5733210, baseEnd_5733210] using wordTrace_append hprefix tailTrace_5733210
  have hstable : (prefixWord ++ tailWord_5733210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733210).length < 2 ^ (prefixWord ++ tailWord_5733210).sum := by decide
  have hdescent : baseEnd_5733210 < baseStart_5733210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733221 : List Nat := [1, 3, 1, 3, 1, 1, 5, 3, 1, 2, 2]
def baseStart_5733221 : Nat := 118140960795 + 5733221 * 2 ^ 59
def prefixEnd_5733221 : Nat := 4983230072969 + 3 ^ 40 * 5733221 * 2
def baseEnd_5733221 : Nat := 2943898071450818480170903

theorem tailTrace_5733221 : CollatzResearch.WordTrace tailWord_5733221 prefixEnd_5733221 2943898071450818480170903 := by
  unfold tailWord_5733221
  simp only [CollatzResearch.WordTrace]
  refine ⟨209107748762526948037303517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139405165841684632024869011 209107748762526948037303517)
  ·
    refine ⟨78415405785947605513988819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209107748762526948037303517 78415405785947605513988819)
    ·
      refine ⟨117623108678921408270983229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78415405785947605513988819 117623108678921408270983229)
      ·
        refine ⟨44108665754595528101618711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117623108678921408270983229 44108665754595528101618711)
        ·
          refine ⟨66162998631893292152428067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44108665754595528101618711 66162998631893292152428067)
          ·
            refine ⟨99244497947839938228642101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66162998631893292152428067 99244497947839938228642101)
            ·
              refine ⟨9304171682609994208935197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 99244497947839938228642101 9304171682609994208935197)
              ·
                refine ⟨3489064380978747828350699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9304171682609994208935197 3489064380978747828350699)
                ·
                  refine ⟨5233596571468121742526049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3489064380978747828350699 5233596571468121742526049)
                  ·
                    refine ⟨3925197428601091306894537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5233596571468121742526049 3925197428601091306894537)
                    ·
                      refine ⟨2943898071450818480170903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3925197428601091306894537 2943898071450818480170903)
                      ·
                        rfl

theorem cell23_5733221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_5733221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733221 prefixEnd_5733221 := by exact prefixLift 5733221
  have htrace : WordTrace (prefixWord ++ tailWord_5733221) baseStart_5733221 baseEnd_5733221 := by
    simpa [prefixWord, tailWord_5733221, baseEnd_5733221] using wordTrace_append hprefix tailTrace_5733221
  have hstable : (prefixWord ++ tailWord_5733221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733221).length < 2 ^ (prefixWord ++ tailWord_5733221).sum := by decide
  have hdescent : baseEnd_5733221 < baseStart_5733221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733238 : List Nat := [5, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_5733238 : Nat := 118140960795 + 5733238 * 2 ^ 59
def prefixEnd_5733238 : Nat := 4983230072969 + 3 ^ 40 * 5733238 * 2
def baseEnd_5733238 : Nat := 2943906800621944913658325

theorem tailTrace_5733238 : CollatzResearch.WordTrace tailWord_5733238 prefixEnd_5733238 2943906800621944913658325 := by
  unfold tailWord_5733238
  simp only [CollatzResearch.WordTrace]
  refine ⟨13069273050216584996292023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139405579202310239960448245 13069273050216584996292023)
  ·
    refine ⟨19603909575324877494438035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13069273050216584996292023 19603909575324877494438035)
    ·
      refine ⟨29405864362987316241657053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19603909575324877494438035 29405864362987316241657053)
      ·
        refine ⟨11027199136120243590621395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29405864362987316241657053 11027199136120243590621395)
        ·
          refine ⟨16540798704180365385932093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11027199136120243590621395 16540798704180365385932093)
          ·
            refine ⟨6202799514067637019724535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16540798704180365385932093 6202799514067637019724535)
            ·
              refine ⟨9304199271101455529586803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6202799514067637019724535 9304199271101455529586803)
              ·
                refine ⟨13956298906652183294380205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9304199271101455529586803 13956298906652183294380205)
                ·
                  refine ⟨5233612089994568735392577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13956298906652183294380205 5233612089994568735392577)
                  ·
                    refine ⟨3925209067495926551544433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5233612089994568735392577 3925209067495926551544433)
                    ·
                      refine ⟨2943906800621944913658325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3925209067495926551544433 2943906800621944913658325)
                      ·
                        rfl

theorem cell23_5733238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_5733238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733238 prefixEnd_5733238 := by exact prefixLift 5733238
  have htrace : WordTrace (prefixWord ++ tailWord_5733238) baseStart_5733238 baseEnd_5733238 := by
    simpa [prefixWord, tailWord_5733238, baseEnd_5733238] using wordTrace_append hprefix tailTrace_5733238
  have hstable : (prefixWord ++ tailWord_5733238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733238).length < 2 ^ (prefixWord ++ tailWord_5733238).sum := by decide
  have hdescent : baseEnd_5733238 < baseStart_5733238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733263 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_5733263 : Nat := 118140960795 + 5733263 * 2 ^ 59
def prefixEnd_5733263 : Nat := 4983230072969 + 3 ^ 40 * 5733263 * 2
def baseEnd_5733263 : Nat := 2943919637638307315845709

theorem tailTrace_5733263 : CollatzResearch.WordTrace tailWord_5733263 prefixEnd_5733263 2943919637638307315845709 := by
  unfold tailWord_5733263
  simp only [CollatzResearch.WordTrace]
  refine ⟨209109280628374789210332443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139406187085583192806888295 209109280628374789210332443)
  ·
    refine ⟨313663920942562183815498665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209109280628374789210332443 313663920942562183815498665)
    ·
      refine ⟨235247940706921637861623999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313663920942562183815498665 235247940706921637861623999)
      ·
        refine ⟨352871911060382456792435999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235247940706921637861623999 352871911060382456792435999)
        ·
          refine ⟨529307866590573685188653999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352871911060382456792435999 529307866590573685188653999)
          ·
            refine ⟨793961799885860527782980999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529307866590573685188653999 793961799885860527782980999)
            ·
              refine ⟨1190942699828790791674471499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793961799885860527782980999 1190942699828790791674471499)
              ·
                refine ⟨1786414049743186187511707249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190942699828790791674471499 1786414049743186187511707249)
                ·
                  refine ⟨1339810537307389640633780437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1786414049743186187511707249 1339810537307389640633780437)
                  ·
                    refine ⟨31401809468141944702354229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1339810537307389640633780437 31401809468141944702354229)
                    ·
                      refine ⟨2943919637638307315845709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31401809468141944702354229 2943919637638307315845709)
                      ·
                        rfl

theorem cell23_5733263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_5733263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733263 prefixEnd_5733263 := by exact prefixLift 5733263
  have htrace : WordTrace (prefixWord ++ tailWord_5733263) baseStart_5733263 baseEnd_5733263 := by
    simpa [prefixWord, tailWord_5733263, baseEnd_5733263] using wordTrace_append hprefix tailTrace_5733263
  have hstable : (prefixWord ++ tailWord_5733263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733263).length < 2 ^ (prefixWord ++ tailWord_5733263).sum := by decide
  have hdescent : baseEnd_5733263 < baseStart_5733263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733280 : List Nat := [2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 5]
def baseStart_5733280 : Nat := 118140960795 + 5733280 * 2 ^ 59
def prefixEnd_5733280 : Nat := 4983230072969 + 3 ^ 40 * 5733280 * 2
def baseEnd_5733280 : Nat := 2943928366809433749333131

theorem tailTrace_5733280 : CollatzResearch.WordTrace tailWord_5733280 prefixEnd_5733280 2943928366809433749333131 := by
  unfold tailWord_5733280
  simp only [CollatzResearch.WordTrace]
  refine ⟨104554950334656600556850647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139406600446208800742467529 104554950334656600556850647)
  ·
    refine ⟨156832425501984900835275971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104554950334656600556850647 156832425501984900835275971)
    ·
      refine ⟨235248638252977351252913957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156832425501984900835275971 235248638252977351252913957)
      ·
        refine ⟨44109119672433253359921367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235248638252977351252913957 44109119672433253359921367)
        ·
          refine ⟨66163679508649880039882051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44109119672433253359921367 66163679508649880039882051)
          ·
            refine ⟨99245519262974820059823077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66163679508649880039882051 99245519262974820059823077)
            ·
              refine ⟨18608534861807778761216827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99245519262974820059823077 18608534861807778761216827)
              ·
                refine ⟨27912802292711668141825241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18608534861807778761216827 27912802292711668141825241)
                ·
                  refine ⟨20934601719533751106368931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27912802292711668141825241 20934601719533751106368931)
                  ·
                    refine ⟨31401902579300626659553397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20934601719533751106368931 31401902579300626659553397)
                    ·
                      refine ⟨2943928366809433749333131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31401902579300626659553397 2943928366809433749333131)
                      ·
                        rfl

theorem cell23_5733280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_5733280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733280 prefixEnd_5733280 := by exact prefixLift 5733280
  have htrace : WordTrace (prefixWord ++ tailWord_5733280) baseStart_5733280 baseEnd_5733280 := by
    simpa [prefixWord, tailWord_5733280, baseEnd_5733280] using wordTrace_append hprefix tailTrace_5733280
  have hstable : (prefixWord ++ tailWord_5733280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733280).length < 2 ^ (prefixWord ++ tailWord_5733280).sum := by decide
  have hdescent : baseEnd_5733280 < baseStart_5733280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733387 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 3]
def baseStart_5733387 : Nat := 118140960795 + 5733387 * 2 ^ 59
def prefixEnd_5733387 : Nat := 4983230072969 + 3 ^ 40 * 5733387 * 2
def baseEnd_5733387 : Nat := 2943983309239464830695139

theorem tailTrace_5733387 : CollatzResearch.WordTrace tailWord_5733387 prefixEnd_5733387 2943983309239464830695139 := by
  unfold tailWord_5733387
  simp only [CollatzResearch.WordTrace]
  refine ⟨209113803279925558387846415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139409202186617038925230943 209113803279925558387846415)
  ·
    refine ⟨313670704919888337581769623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209113803279925558387846415 313670704919888337581769623)
    ·
      refine ⟨470506057379832506372654435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313670704919888337581769623 470506057379832506372654435)
      ·
        refine ⟨705759086069748759558981653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470506057379832506372654435 705759086069748759558981653)
        ·
          refine ⟨33082457159519473104327265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 705759086069748759558981653 33082457159519473104327265)
          ·
            refine ⟨24811842869639604828245449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33082457159519473104327265 24811842869639604828245449)
            ·
              refine ⟨18608882152229703621184087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24811842869639604828245449 18608882152229703621184087)
              ·
                refine ⟨27913323228344555431776131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18608882152229703621184087 27913323228344555431776131)
                ·
                  refine ⟨41869984842516833147664197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27913323228344555431776131 41869984842516833147664197)
                  ·
                    refine ⟨7850622157971906215187037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41869984842516833147664197 7850622157971906215187037)
                    ·
                      refine ⟨2943983309239464830695139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7850622157971906215187037 2943983309239464830695139)
                      ·
                        rfl

theorem cell23_5733387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 3].length) (baseStart_5733387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733387 prefixEnd_5733387 := by exact prefixLift 5733387
  have htrace : WordTrace (prefixWord ++ tailWord_5733387) baseStart_5733387 baseEnd_5733387 := by
    simpa [prefixWord, tailWord_5733387, baseEnd_5733387] using wordTrace_append hprefix tailTrace_5733387
  have hstable : (prefixWord ++ tailWord_5733387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733387).length < 2 ^ (prefixWord ++ tailWord_5733387).sum := by decide
  have hdescent : baseEnd_5733387 < baseStart_5733387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733434 : List Nat := [3, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3]
def baseStart_5733434 : Nat := 118140960795 + 5733434 * 2 ^ 59
def prefixEnd_5733434 : Nat := 4983230072969 + 3 ^ 40 * 5733434 * 2
def baseEnd_5733434 : Nat := 2944007442830226146807423

theorem tailTrace_5733434 : CollatzResearch.WordTrace tailWord_5733434 prefixEnd_5733434 2944007442830226146807423 := by
  unfold tailWord_5733434
  simp only [CollatzResearch.WordTrace]
  refine ⟨52278879377688821353701839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139410345007170190276538237 52278879377688821353701839)
  ·
    refine ⟨78418319066533232030552759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52278879377688821353701839 78418319066533232030552759)
    ·
      refine ⟨117627478599799848045829139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78418319066533232030552759 117627478599799848045829139)
      ·
        refine ⟨176441217899699772068743709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117627478599799848045829139 176441217899699772068743709)
        ·
          refine ⟨66165456712387414525778891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176441217899699772068743709 66165456712387414525778891)
          ·
            refine ⟨99248185068581121788668337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66165456712387414525778891 99248185068581121788668337)
            ·
              refine ⟨74436138801435841341501253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99248185068581121788668337 74436138801435841341501253)
              ·
                refine ⟨13956776025269220251531485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74436138801435841341501253 13956776025269220251531485)
                ·
                  refine ⟨5233791009475957594324307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13956776025269220251531485 5233791009475957594324307)
                  ·
                    refine ⟨7850686514213936391486461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5233791009475957594324307 7850686514213936391486461)
                    ·
                      refine ⟨2944007442830226146807423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7850686514213936391486461 2944007442830226146807423)
                      ·
                        rfl

theorem cell23_5733434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_5733434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733434 prefixEnd_5733434 := by exact prefixLift 5733434
  have htrace : WordTrace (prefixWord ++ tailWord_5733434) baseStart_5733434 baseEnd_5733434 := by
    simpa [prefixWord, tailWord_5733434, baseEnd_5733434] using wordTrace_append hprefix tailTrace_5733434
  have hstable : (prefixWord ++ tailWord_5733434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733434).length < 2 ^ (prefixWord ++ tailWord_5733434).sum := by decide
  have hdescent : baseEnd_5733434 < baseStart_5733434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733468 : List Nat := [2, 2, 4, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_5733468 : Nat := 118140960795 + 5733468 * 2 ^ 59
def prefixEnd_5733468 : Nat := 4983230072969 + 3 ^ 40 * 5733468 * 2
def baseEnd_5733468 : Nat := 2944024901172479013782267

theorem tailTrace_5733468 : CollatzResearch.WordTrace tailWord_5733468 prefixEnd_5733468 2944024901172479013782267 := by
  unfold tailWord_5733468
  simp only [CollatzResearch.WordTrace]
  refine ⟨104558378796316054610772529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139411171728421406147696705 104558378796316054610772529)
  ·
    refine ⟨78418784097237040958079397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104558378796316054610772529 78418784097237040958079397)
    ·
      refine ⟨14703522018231945179639887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78418784097237040958079397 14703522018231945179639887)
      ·
        refine ⟨22055283027347917769459831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14703522018231945179639887 22055283027347917769459831)
        ·
          refine ⟨33082924541021876654189747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22055283027347917769459831 33082924541021876654189747)
          ·
            refine ⟨49624386811532814981284621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33082924541021876654189747 49624386811532814981284621)
            ·
              refine ⟨18609145054324805617981733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49624386811532814981284621 18609145054324805617981733)
              ·
                refine ⟨3489214697685901053371575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18609145054324805617981733 3489214697685901053371575)
                ·
                  refine ⟨5233822046528851580057363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3489214697685901053371575 5233822046528851580057363)
                  ·
                    refine ⟨7850733069793277370086045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5233822046528851580057363 7850733069793277370086045)
                    ·
                      refine ⟨2944024901172479013782267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7850733069793277370086045 2944024901172479013782267)
                      ·
                        rfl

theorem cell23_5733468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_5733468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733468 prefixEnd_5733468 := by exact prefixLift 5733468
  have htrace : WordTrace (prefixWord ++ tailWord_5733468) baseStart_5733468 baseEnd_5733468 := by
    simpa [prefixWord, tailWord_5733468, baseEnd_5733468] using wordTrace_append hprefix tailTrace_5733468
  have hstable : (prefixWord ++ tailWord_5733468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733468).length < 2 ^ (prefixWord ++ tailWord_5733468).sum := by decide
  have hdescent : baseEnd_5733468 < baseStart_5733468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733477 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_5733477 : Nat := 118140960795 + 5733477 * 2 ^ 59
def prefixEnd_5733477 : Nat := 4983230072969 + 3 ^ 40 * 5733477 * 2
def baseEnd_5733477 : Nat := 2944029522498369478569725

theorem tailTrace_5733477 : CollatzResearch.WordTrace tailWord_5733477 prefixEnd_5733477 2944029522498369478569725 := by
  unfold tailWord_5733477
  simp only [CollatzResearch.WordTrace]
  refine ⟨209117085849599503758622685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139411390566399669172415123 209117085849599503758622685)
  ·
    refine ⟨78418907193599813909483507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209117085849599503758622685 78418907193599813909483507)
    ·
      refine ⟨117628360790399720864225261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78418907193599813909483507 117628360790399720864225261)
      ·
        refine ⟨44110635296399895324084473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117628360790399720864225261 44110635296399895324084473)
        ·
          refine ⟨33082976472299921493063355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44110635296399895324084473 33082976472299921493063355)
          ·
            refine ⟨49624464708449882239595033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33082976472299921493063355 49624464708449882239595033)
            ·
              refine ⟨37218348531337411679696275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49624464708449882239595033 37218348531337411679696275)
              ·
                refine ⟨55827522797006117519544413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37218348531337411679696275 55827522797006117519544413)
                ·
                  refine ⟨20935321048877294069829155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55827522797006117519544413 20935321048877294069829155)
                  ·
                    refine ⟨31402981573315941104743733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20935321048877294069829155 31402981573315941104743733)
                    ·
                      refine ⟨2944029522498369478569725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31402981573315941104743733 2944029522498369478569725)
                      ·
                        rfl

theorem cell23_5733477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_5733477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733477 prefixEnd_5733477 := by exact prefixLift 5733477
  have htrace : WordTrace (prefixWord ++ tailWord_5733477) baseStart_5733477 baseEnd_5733477 := by
    simpa [prefixWord, tailWord_5733477, baseEnd_5733477] using wordTrace_append hprefix tailTrace_5733477
  have hstable : (prefixWord ++ tailWord_5733477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733477).length < 2 ^ (prefixWord ++ tailWord_5733477).sum := by decide
  have hdescent : baseEnd_5733477 < baseStart_5733477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733484 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 2, 4]
def baseStart_5733484 : Nat := 118140960795 + 5733484 * 2 ^ 59
def prefixEnd_5733484 : Nat := 4983230072969 + 3 ^ 40 * 5733484 * 2
def baseEnd_5733484 : Nat := 981344372287650317060731

theorem tailTrace_5733484 : CollatzResearch.WordTrace tailWord_5733484 prefixEnd_5733484 981344372287650317060731 := by
  unfold tailWord_5733484
  simp only [CollatzResearch.WordTrace]
  refine ⟨104558670580287071977063753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139411560773716095969418337 104558670580287071977063753)
  ·
    refine ⟨78419002935215303982797815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104558670580287071977063753 78419002935215303982797815)
    ·
      refine ⟨117628504402822955974196723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78419002935215303982797815 117628504402822955974196723)
      ·
        refine ⟨176442756604234433961295085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117628504402822955974196723 176442756604234433961295085)
        ·
          refine ⟨66166033726587912735485657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 176442756604234433961295085 66166033726587912735485657)
          ·
            refine ⟨49624525294940934551614243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66166033726587912735485657 49624525294940934551614243)
            ·
              refine ⟨74436787942411401827421365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49624525294940934551614243 74436787942411401827421365)
              ·
                refine ⟨6978448869601068921320753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74436787942411401827421365 6978448869601068921320753)
                ·
                  refine ⟨5233836652200801690990565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6978448869601068921320753 5233836652200801690990565)
                  ·
                    refine ⟨981344372287650317060731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5233836652200801690990565 981344372287650317060731)
                    ·
                      rfl

theorem cell23_5733484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_5733484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733484 prefixEnd_5733484 := by exact prefixLift 5733484
  have htrace : WordTrace (prefixWord ++ tailWord_5733484) baseStart_5733484 baseEnd_5733484 := by
    simpa [prefixWord, tailWord_5733484, baseEnd_5733484] using wordTrace_append hprefix tailTrace_5733484
  have hstable : (prefixWord ++ tailWord_5733484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733484).length < 2 ^ (prefixWord ++ tailWord_5733484).sum := by decide
  have hdescent : baseEnd_5733484 < baseStart_5733484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733508 : List Nat := [2, 3, 2, 1, 2, 4, 2, 1, 1, 1, 4]
def baseStart_5733508 : Nat := 118140960795 + 5733508 * 2 ^ 59
def prefixEnd_5733508 : Nat := 4983230072969 + 3 ^ 40 * 5733508 * 2
def baseEnd_5733508 : Nat := 2944045440398658857282083

theorem tailTrace_5733508 : CollatzResearch.WordTrace tailWord_5733508 prefixEnd_5733508 2944045440398658857282083 := by
  unfold tailWord_5733508
  simp only [CollatzResearch.WordTrace]
  refine ⟨104559108256243598026500589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139412144341658130702000785 104559108256243598026500589)
  ·
    refine ⟨39209665596091349259937721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104559108256243598026500589 39209665596091349259937721)
    ·
      refine ⟨29407249197068511944953291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39209665596091349259937721 29407249197068511944953291)
      ·
        refine ⟨44110873795602767917429937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29407249197068511944953291 44110873795602767917429937)
        ·
          refine ⟨33083155346702075938072453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44110873795602767917429937 33083155346702075938072453)
          ·
            refine ⟨6203091627506639238388585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33083155346702075938072453 6203091627506639238388585)
            ·
              refine ⟨4652318720629979428791439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6203091627506639238388585 4652318720629979428791439)
              ·
                refine ⟨6978478080944969143187159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4652318720629979428791439 6978478080944969143187159)
                ·
                  refine ⟨10467717121417453714780739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6978478080944969143187159 10467717121417453714780739)
                  ·
                    refine ⟨15701575682126180572171109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10467717121417453714780739 15701575682126180572171109)
                    ·
                      refine ⟨2944045440398658857282083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15701575682126180572171109 2944045440398658857282083)
                      ·
                        rfl

theorem cell23_5733508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_5733508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733508 prefixEnd_5733508 := by exact prefixLift 5733508
  have htrace : WordTrace (prefixWord ++ tailWord_5733508) baseStart_5733508 baseEnd_5733508 := by
    simpa [prefixWord, tailWord_5733508, baseEnd_5733508] using wordTrace_append hprefix tailTrace_5733508
  have hstable : (prefixWord ++ tailWord_5733508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733508).length < 2 ^ (prefixWord ++ tailWord_5733508).sum := by decide
  have hdescent : baseEnd_5733508 < baseStart_5733508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733518 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 2, 4]
def baseStart_5733518 : Nat := 118140960795 + 5733518 * 2 ^ 59
def prefixEnd_5733518 : Nat := 4983230072969 + 3 ^ 40 * 5733518 * 2
def baseEnd_5733518 : Nat := 981350191735067939385679

theorem tailTrace_5733518 : CollatzResearch.WordTrace tailWord_5733518 prefixEnd_5733518 981350191735067939385679 := by
  unfold tailWord_5733518
  simp only [CollatzResearch.WordTrace]
  refine ⟨26139822655306370970108151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139412387494967311840576805 26139822655306370970108151)
  ·
    refine ⟨39209733982959556455162227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26139822655306370970108151 39209733982959556455162227)
    ·
      refine ⟨58814600974439334682743341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39209733982959556455162227 58814600974439334682743341)
      ·
        refine ⟨22055475365414750506028753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58814600974439334682743341 22055475365414750506028753)
        ·
          refine ⟨16541606524061062879521565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22055475365414750506028753 16541606524061062879521565)
          ·
            refine ⟨6203102446522898579820587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16541606524061062879521565 6203102446522898579820587)
            ·
              refine ⟨9304653669784347869730881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6203102446522898579820587 9304653669784347869730881)
              ·
                refine ⟨6978490252338260902298161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9304653669784347869730881 6978490252338260902298161)
                ·
                  refine ⟨5233867689253695676723621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6978490252338260902298161 5233867689253695676723621)
                  ·
                    refine ⟨981350191735067939385679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5233867689253695676723621 981350191735067939385679)
                    ·
                      rfl

theorem cell23_5733518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_5733518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733518 prefixEnd_5733518 := by exact prefixLift 5733518
  have htrace : WordTrace (prefixWord ++ tailWord_5733518) baseStart_5733518 baseEnd_5733518 := by
    simpa [prefixWord, tailWord_5733518, baseEnd_5733518] using wordTrace_append hprefix tailTrace_5733518
  have hstable : (prefixWord ++ tailWord_5733518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733518).length < 2 ^ (prefixWord ++ tailWord_5733518).sum := by decide
  have hdescent : baseEnd_5733518 < baseStart_5733518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733538 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_5733538 : Nat := 118140960795 + 5733538 * 2 ^ 59
def prefixEnd_5733538 : Nat := 4983230072969 + 3 ^ 40 * 5733538 * 2
def baseEnd_5733538 : Nat := 2944060844818293739906945

theorem tailTrace_5733538 : CollatzResearch.WordTrace tailWord_5733538 prefixEnd_5733538 2944060844818293739906945 := by
  unfold tailWord_5733538
  simp only [CollatzResearch.WordTrace]
  refine ⟨52279827675594627794148317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139412873801585674117728845 52279827675594627794148317)
  ·
    refine ⟨19604935378347985422805619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52279827675594627794148317 19604935378347985422805619)
    ·
      refine ⟨29407403067521978134208429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19604935378347985422805619 29407403067521978134208429)
      ·
        refine ⟨11027776150320741800328161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29407403067521978134208429 11027776150320741800328161)
        ·
          refine ⟨8270832112740556350246121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11027776150320741800328161 8270832112740556350246121)
          ·
            refine ⟨6203124084555417262684591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8270832112740556350246121 6203124084555417262684591)
            ·
              refine ⟨9304686126833125894026887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6203124084555417262684591 9304686126833125894026887)
              ·
                refine ⟨13957029190249688841040331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9304686126833125894026887 13957029190249688841040331)
                ·
                  refine ⟨20935543785374533261560497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13957029190249688841040331 20935543785374533261560497)
                  ·
                    refine ⟨15701657839030899946170373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20935543785374533261560497 15701657839030899946170373)
                    ·
                      refine ⟨2944060844818293739906945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15701657839030899946170373 2944060844818293739906945)
                      ·
                        rfl

theorem cell23_5733538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_5733538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733538 prefixEnd_5733538 := by exact prefixLift 5733538
  have htrace : WordTrace (prefixWord ++ tailWord_5733538) baseStart_5733538 baseEnd_5733538 := by
    simpa [prefixWord, tailWord_5733538, baseEnd_5733538] using wordTrace_append hprefix tailTrace_5733538
  have hstable : (prefixWord ++ tailWord_5733538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733538).length < 2 ^ (prefixWord ++ tailWord_5733538).sum := by decide
  have hdescent : baseEnd_5733538 < baseStart_5733538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733541 : List Nat := [1, 3, 1, 2, 1, 6, 1, 1, 1, 3, 3]
def baseStart_5733541 : Nat := 118140960795 + 5733541 * 2 ^ 59
def prefixEnd_5733541 : Nat := 4983230072969 + 3 ^ 40 * 5733541 * 2
def baseEnd_5733541 : Nat := 2944062385260257228169431

theorem tailTrace_5733541 : CollatzResearch.WordTrace tailWord_5733541 prefixEnd_5733541 2944062385260257228169431 := by
  unfold tailWord_5733541
  simp only [CollatzResearch.WordTrace]
  refine ⟨209119420121367642688952477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139412946747578428459301651 209119420121367642688952477)
  ·
    refine ⟨78419782545512866008357179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209119420121367642688952477 78419782545512866008357179)
    ·
      refine ⟨117629673818269299012535769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78419782545512866008357179 117629673818269299012535769)
      ·
        refine ⟨88222255363701974259401827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117629673818269299012535769 88222255363701974259401827)
        ·
          refine ⟨132333383045552961389102741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88222255363701974259401827 132333383045552961389102741)
          ·
            refine ⟨6203127330260295065114191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 132333383045552961389102741 6203127330260295065114191)
            ·
              refine ⟨9304690995390442597671287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6203127330260295065114191 9304690995390442597671287)
              ·
                refine ⟨13957036493085663896506931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9304690995390442597671287 13957036493085663896506931)
                ·
                  refine ⟨20935554739628495844760397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13957036493085663896506931 20935554739628495844760397)
                  ·
                    refine ⟨7850833027360685941785149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20935554739628495844760397 7850833027360685941785149)
                    ·
                      refine ⟨2944062385260257228169431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7850833027360685941785149 2944062385260257228169431)
                      ·
                        rfl

theorem cell23_5733541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_5733541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733541 prefixEnd_5733541 := by exact prefixLift 5733541
  have htrace : WordTrace (prefixWord ++ tailWord_5733541) baseStart_5733541 baseEnd_5733541 := by
    simpa [prefixWord, tailWord_5733541, baseEnd_5733541] using wordTrace_append hprefix tailTrace_5733541
  have hstable : (prefixWord ++ tailWord_5733541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733541).length < 2 ^ (prefixWord ++ tailWord_5733541).sum := by decide
  have hdescent : baseEnd_5733541 < baseStart_5733541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733551 : List Nat := [1, 1, 2, 1, 2, 3, 3, 4, 1, 3, 2]
def baseStart_5733551 : Nat := 118140960795 + 5733551 * 2 ^ 59
def prefixEnd_5733551 : Nat := 4983230072969 + 3 ^ 40 * 5733551 * 2
def baseEnd_5733551 : Nat := 2944067520066802189044385

theorem tailTrace_5733551 : CollatzResearch.WordTrace tailWord_5733551 prefixEnd_5733551 2944067520066802189044385 := by
  unfold tailWord_5733551
  simp only [CollatzResearch.WordTrace]
  refine ⟨209119784851331414396816507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139413189900887609597877671 209119784851331414396816507)
  ·
    refine ⟨313679677276997121595224761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209119784851331414396816507 313679677276997121595224761)
    ·
      refine ⟨235259757957747841196418571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313679677276997121595224761 235259757957747841196418571)
      ·
        refine ⟨352889636936621761794627857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235259757957747841196418571 352889636936621761794627857)
        ·
          refine ⟨264667227702466321345970893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352889636936621761794627857 264667227702466321345970893)
          ·
            refine ⟨99250210388424870504739085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264667227702466321345970893 99250210388424870504739085)
            ·
              refine ⟨37218828895659326439277157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99250210388424870504739085 37218828895659326439277157)
              ·
                refine ⟨6978530417936123707364467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37218828895659326439277157 6978530417936123707364467)
                ·
                  refine ⟨10467795626904185561046701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6978530417936123707364467 10467795626904185561046701)
                  ·
                    refine ⟨3925423360089069585392513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10467795626904185561046701 3925423360089069585392513)
                    ·
                      refine ⟨2944067520066802189044385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3925423360089069585392513 2944067520066802189044385)
                      ·
                        rfl

theorem cell23_5733551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 3, 2].length) (baseStart_5733551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733551 prefixEnd_5733551 := by exact prefixLift 5733551
  have htrace : WordTrace (prefixWord ++ tailWord_5733551) baseStart_5733551 baseEnd_5733551 := by
    simpa [prefixWord, tailWord_5733551, baseEnd_5733551] using wordTrace_append hprefix tailTrace_5733551
  have hstable : (prefixWord ++ tailWord_5733551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733551).length < 2 ^ (prefixWord ++ tailWord_5733551).sum := by decide
  have hdescent : baseEnd_5733551 < baseStart_5733551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733567 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_5733567 : Nat := 118140960795 + 5733567 * 2 ^ 59
def prefixEnd_5733567 : Nat := 4983230072969 + 3 ^ 40 * 5733567 * 2
def baseEnd_5733567 : Nat := 2944075735757274126444311

theorem tailTrace_5733567 : CollatzResearch.WordTrace tailWord_5733567 prefixEnd_5733567 2944075735757274126444311 := by
  unfold tailWord_5733567
  simp only [CollatzResearch.WordTrace]
  refine ⟨209120368419273449129398955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139413578946182299419599303 209120368419273449129398955)
  ·
    refine ⟨313680552628910173694098433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209120368419273449129398955 313680552628910173694098433)
    ·
      refine ⟨235260414471682630270573825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313680552628910173694098433 235260414471682630270573825)
      ·
        refine ⟨176445310853761972702930369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235260414471682630270573825 176445310853761972702930369)
        ·
          refine ⟨132333983140321479527197777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176445310853761972702930369 132333983140321479527197777)
          ·
            refine ⟨99250487355241109645398333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132333983140321479527197777 99250487355241109645398333)
            ·
              refine ⟨37218932758215416117024375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99250487355241109645398333 37218932758215416117024375)
              ·
                refine ⟨55828399137323124175536563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37218932758215416117024375 55828399137323124175536563)
                ·
                  refine ⟨83742598705984686263304845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55828399137323124175536563 83742598705984686263304845)
                  ·
                    refine ⟨31403474514744257348739317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83742598705984686263304845 31403474514744257348739317)
                    ·
                      refine ⟨2944075735757274126444311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31403474514744257348739317 2944075735757274126444311)
                      ·
                        rfl

theorem cell23_5733567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_5733567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733567 prefixEnd_5733567 := by exact prefixLift 5733567
  have htrace : WordTrace (prefixWord ++ tailWord_5733567) baseStart_5733567 baseEnd_5733567 := by
    simpa [prefixWord, tailWord_5733567, baseEnd_5733567] using wordTrace_append hprefix tailTrace_5733567
  have hstable : (prefixWord ++ tailWord_5733567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733567).length < 2 ^ (prefixWord ++ tailWord_5733567).sum := by decide
  have hdescent : baseEnd_5733567 < baseStart_5733567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733592 : List Nat := [2, 1, 2, 2, 6, 1, 2, 1, 2, 1, 3]
def baseStart_5733592 : Nat := 118140960795 + 5733592 * 2 ^ 59
def prefixEnd_5733592 : Nat := 4983230072969 + 3 ^ 40 * 5733592 * 2
def baseEnd_5733592 : Nat := 2944088572773636528631697

theorem tailTrace_5733592 : CollatzResearch.WordTrace tailWord_5733592 prefixEnd_5733592 2944088572773636528631697 := by
  unfold tailWord_5733592
  simp only [CollatzResearch.WordTrace]
  refine ⟨104560640122091439199529515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139414186829455252266039353 104560640122091439199529515)
  ·
    refine ⟨156840960183137158799294273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104560640122091439199529515 156840960183137158799294273)
    ·
      refine ⟨117630720137352869099470705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156840960183137158799294273 117630720137352869099470705)
      ·
        refine ⟨88223040103014651824603029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117630720137352869099470705 88223040103014651824603029)
        ·
          refine ⟨4135455004828811804278267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88223040103014651824603029 4135455004828811804278267)
          ·
            refine ⟨6203182507243217706417401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135455004828811804278267 6203182507243217706417401)
            ·
              refine ⟨4652386880432413279813051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6203182507243217706417401 4652386880432413279813051)
              ·
                refine ⟨6978580320648619919719577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4652386880432413279813051 6978580320648619919719577)
                ·
                  refine ⟨5233935240486464939789683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6978580320648619919719577 5233935240486464939789683)
                  ·
                    refine ⟨7850902860729697409684525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5233935240486464939789683 7850902860729697409684525)
                    ·
                      refine ⟨2944088572773636528631697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7850902860729697409684525 2944088572773636528631697)
                      ·
                        rfl

theorem cell23_5733592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_5733592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733592 prefixEnd_5733592 := by exact prefixLift 5733592
  have htrace : WordTrace (prefixWord ++ tailWord_5733592) baseStart_5733592 baseEnd_5733592 := by
    simpa [prefixWord, tailWord_5733592, baseEnd_5733592] using wordTrace_append hprefix tailTrace_5733592
  have hstable : (prefixWord ++ tailWord_5733592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733592).length < 2 ^ (prefixWord ++ tailWord_5733592).sum := by decide
  have hdescent : baseEnd_5733592 < baseStart_5733592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733644 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_5733644 : Nat := 118140960795 + 5733644 * 2 ^ 59
def prefixEnd_5733644 : Nat := 4983230072969 + 3 ^ 40 * 5733644 * 2
def baseEnd_5733644 : Nat := 2944115273767670325181457

theorem tailTrace_5733644 : CollatzResearch.WordTrace tailWord_5733644 prefixEnd_5733644 2944115273767670325181457 := by
  unfold tailWord_5733644
  simp only [CollatzResearch.WordTrace]
  refine ⟨104561588419997245639975993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139415451226662994186634657 104561588419997245639975993)
  ·
    refine ⟨78421191314997934229981995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104561588419997245639975993 78421191314997934229981995)
    ·
      refine ⟨117631786972496901344972993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78421191314997934229981995 117631786972496901344972993)
      ·
        refine ⟨88223840229372676008729745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117631786972496901344972993 88223840229372676008729745)
        ·
          refine ⟨66167880172029507006547309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88223840229372676008729745 66167880172029507006547309)
          ·
            refine ⟨24812955064511065127455241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66167880172029507006547309 24812955064511065127455241)
            ·
              refine ⟨18609716298383298845591431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24812955064511065127455241 18609716298383298845591431)
              ·
                refine ⟨27914574447574948268387147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18609716298383298845591431 27914574447574948268387147)
                ·
                  refine ⟨41871861671362422402580721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27914574447574948268387147 41871861671362422402580721)
                  ·
                    refine ⟨31403896253521816801935541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41871861671362422402580721 31403896253521816801935541)
                    ·
                      refine ⟨2944115273767670325181457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31403896253521816801935541 2944115273767670325181457)
                      ·
                        rfl

theorem cell23_5733644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_5733644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733644 prefixEnd_5733644 := by exact prefixLift 5733644
  have htrace : WordTrace (prefixWord ++ tailWord_5733644) baseStart_5733644 baseEnd_5733644 := by
    simpa [prefixWord, tailWord_5733644, baseEnd_5733644] using wordTrace_append hprefix tailTrace_5733644
  have hstable : (prefixWord ++ tailWord_5733644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733644).length < 2 ^ (prefixWord ++ tailWord_5733644).sum := by decide
  have hdescent : baseEnd_5733644 < baseStart_5733644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733647 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 4, 8]
def baseStart_5733647 : Nat := 118140960795 + 5733647 * 2 ^ 59
def prefixEnd_5733647 : Nat := 4983230072969 + 3 ^ 40 * 5733647 * 2
def baseEnd_5733647 : Nat := 981372271403211271147981

theorem tailTrace_5733647 : CollatzResearch.WordTrace tailWord_5733647 prefixEnd_5733647 981372271403211271147981 := by
  unfold tailWord_5733647
  simp only [CollatzResearch.WordTrace]
  refine ⟨209123286258983622792311195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139415524172655748528207463 209123286258983622792311195)
  ·
    refine ⟨313684929388475434188466793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209123286258983622792311195 313684929388475434188466793)
    ·
      refine ⟨235263697041356575641350095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313684929388475434188466793 235263697041356575641350095)
      ·
        refine ⟨352895545562034863462025143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235263697041356575641350095 352895545562034863462025143)
        ·
          refine ⟨529343318343052295193037715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352895545562034863462025143 529343318343052295193037715)
          ·
            refine ⟨794014977514578442789556573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529343318343052295193037715 794014977514578442789556573)
            ·
              refine ⟨297755616567966916046083715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 794014977514578442789556573 297755616567966916046083715)
              ·
                refine ⟨446633424851950374069125573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297755616567966916046083715 446633424851950374069125573)
                ·
                  refine ⟨83743767159740695137961045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 446633424851950374069125573 83743767159740695137961045)
                  ·
                    refine ⟨981372271403211271147981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83743767159740695137961045 981372271403211271147981)
                    ·
                      rfl

theorem cell23_5733647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_5733647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733647 prefixEnd_5733647 := by exact prefixLift 5733647
  have htrace : WordTrace (prefixWord ++ tailWord_5733647) baseStart_5733647 baseEnd_5733647 := by
    simpa [prefixWord, tailWord_5733647, baseEnd_5733647] using wordTrace_append hprefix tailTrace_5733647
  have hstable : (prefixWord ++ tailWord_5733647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733647).length < 2 ^ (prefixWord ++ tailWord_5733647).sum := by decide
  have hdescent : baseEnd_5733647 < baseStart_5733647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733714 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_5733714 : Nat := 118140960795 + 5733714 * 2 ^ 59
def prefixEnd_5733714 : Nat := 4983230072969 + 3 ^ 40 * 5733714 * 2
def baseEnd_5733714 : Nat := 2944151217413485051306135

theorem tailTrace_5733714 : CollatzResearch.WordTrace tailWord_5733714 prefixEnd_5733714 2944151217413485051306135 := by
  unfold tailWord_5733714
  simp only [CollatzResearch.WordTrace]
  refine ⟨52281432487435223308750049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139417153299827262156666797 52281432487435223308750049)
  ·
    refine ⟨39211074365576417481562537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52281432487435223308750049 39211074365576417481562537)
    ·
      refine ⟨29408305774182313111171903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39211074365576417481562537 29408305774182313111171903)
      ·
        refine ⟨44112458661273469666757855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29408305774182313111171903 44112458661273469666757855)
        ·
          refine ⟨66168687991910204500136783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44112458661273469666757855 66168687991910204500136783)
          ·
            refine ⟨99253031987865306750205175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66168687991910204500136783 99253031987865306750205175)
            ·
              refine ⟨148879547981797960125307763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99253031987865306750205175 148879547981797960125307763)
              ·
                refine ⟨223319321972696940187961645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148879547981797960125307763 223319321972696940187961645)
                ·
                  refine ⟨83744745739761352570485617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223319321972696940187961645 83744745739761352570485617)
                  ·
                    refine ⟨62808559304821014427864213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83744745739761352570485617 62808559304821014427864213)
                    ·
                      refine ⟨2944151217413485051306135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62808559304821014427864213 2944151217413485051306135)
                      ·
                        rfl

theorem cell23_5733714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_5733714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733714 prefixEnd_5733714 := by exact prefixLift 5733714
  have htrace : WordTrace (prefixWord ++ tailWord_5733714) baseStart_5733714 baseEnd_5733714 := by
    simpa [prefixWord, tailWord_5733714, baseEnd_5733714] using wordTrace_append hprefix tailTrace_5733714
  have hstable : (prefixWord ++ tailWord_5733714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733714).length < 2 ^ (prefixWord ++ tailWord_5733714).sum := by decide
  have hdescent : baseEnd_5733714 < baseStart_5733714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733754 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_5733754 : Nat := 118140960795 + 5733754 * 2 ^ 59
def prefixEnd_5733754 : Nat := 4983230072969 + 3 ^ 40 * 5733754 * 2
def baseEnd_5733754 : Nat := 981390585546554964935317

theorem tailTrace_5733754 : CollatzResearch.WordTrace tailWord_5733754 prefixEnd_5733754 981390585546554964935317 := by
  unfold tailWord_5733754
  simp only [CollatzResearch.WordTrace]
  refine ⟨52281797217398995016614079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139418125913063986710970877 52281797217398995016614079)
  ·
    refine ⟨78422695826098492524921119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52281797217398995016614079 78422695826098492524921119)
    ·
      refine ⟨117634043739147738787381679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78422695826098492524921119 117634043739147738787381679)
      ·
        refine ⟨176451065608721608181072519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117634043739147738787381679 176451065608721608181072519)
        ·
          refine ⟨264676598413082412271608779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176451065608721608181072519 264676598413082412271608779)
          ·
            refine ⟨397014897619623618407413169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264676598413082412271608779 397014897619623618407413169)
            ·
              refine ⟨297761173214717713805559877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397014897619623618407413169 297761173214717713805559877)
              ·
                refine ⟨55830219977759571338542477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 297761173214717713805559877 55830219977759571338542477)
                ·
                  refine ⟨20936332491659839251953429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55830219977759571338542477 20936332491659839251953429)
                  ·
                    refine ⟨981390585546554964935317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20936332491659839251953429 981390585546554964935317)
                    ·
                      rfl

theorem cell23_5733754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_5733754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733754 prefixEnd_5733754 := by exact prefixLift 5733754
  have htrace : WordTrace (prefixWord ++ tailWord_5733754) baseStart_5733754 baseEnd_5733754 := by
    simpa [prefixWord, tailWord_5733754, baseEnd_5733754] using wordTrace_append hprefix tailTrace_5733754
  have hstable : (prefixWord ++ tailWord_5733754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733754).length < 2 ^ (prefixWord ++ tailWord_5733754).sum := by decide
  have hdescent : baseEnd_5733754 < baseStart_5733754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733762 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 6]
def baseStart_5733762 : Nat := 118140960795 + 5733762 * 2 ^ 59
def prefixEnd_5733762 : Nat := 4983230072969 + 3 ^ 40 * 5733762 * 2
def baseEnd_5733762 : Nat := 327130651609433429278435

theorem tailTrace_5733762 : CollatzResearch.WordTrace tailWord_5733762 prefixEnd_5733762 327130651609433429278435 := by
  unfold tailWord_5733762
  simp only [CollatzResearch.WordTrace]
  refine ⟨52281870163391749358186885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139418320435711331621831693 52281870163391749358186885)
  ·
    refine ⟨9802850655635953004660041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52281870163391749358186885 9802850655635953004660041)
    ·
      refine ⟨7352137991726964753495031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9802850655635953004660041 7352137991726964753495031)
      ·
        refine ⟨11028206987590447130242547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7352137991726964753495031 11028206987590447130242547)
        ·
          refine ⟨16542310481385670695363821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11028206987590447130242547 16542310481385670695363821)
          ·
            refine ⟨6203366430519626510761433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16542310481385670695363821 6203366430519626510761433)
            ·
              refine ⟨4652524822889719883071075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6203366430519626510761433 4652524822889719883071075)
              ·
                refine ⟨6978787234334579824606613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4652524822889719883071075 6978787234334579824606613)
                ·
                  refine ⟨327130651609433429278435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6978787234334579824606613 327130651609433429278435)
                  ·
                    rfl

theorem cell23_5733762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_5733762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733762 prefixEnd_5733762 := by exact prefixLift 5733762
  have htrace : WordTrace (prefixWord ++ tailWord_5733762) baseStart_5733762 baseEnd_5733762 := by
    simpa [prefixWord, tailWord_5733762, baseEnd_5733762] using wordTrace_append hprefix tailTrace_5733762
  have hstable : (prefixWord ++ tailWord_5733762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733762).length < 2 ^ (prefixWord ++ tailWord_5733762).sum := by decide
  have hdescent : baseEnd_5733762 < baseStart_5733762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733791 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 4]
def baseStart_5733791 : Nat := 118140960795 + 5733791 * 2 ^ 59
def prefixEnd_5733791 : Nat := 4983230072969 + 3 ^ 40 * 5733791 * 2
def baseEnd_5733791 : Nat := 2944190755423881250043281

theorem tailTrace_5733791 : CollatzResearch.WordTrace tailWord_5733791 prefixEnd_5733791 2944190755423881250043281 := by
  unfold tailWord_5733791
  simp only [CollatzResearch.WordTrace]
  refine ⟨209128538370461935385553227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139419025580307956923702151 209128538370461935385553227)
  ·
    refine ⟨313692807555692903078329841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209128538370461935385553227 313692807555692903078329841)
    ·
      refine ⟨235269605666769677308747381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313692807555692903078329841 235269605666769677308747381)
      ·
        refine ⟨22056525531259657247695067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 235269605666769677308747381 22056525531259657247695067)
        ·
          refine ⟨33084788296889485871542601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22056525531259657247695067 33084788296889485871542601)
          ·
            refine ⟨24813591222667114403656951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33084788296889485871542601 24813591222667114403656951)
            ·
              refine ⟨37220386834000671605485427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24813591222667114403656951 37220386834000671605485427)
              ·
                refine ⟨55830580251001007408228141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37220386834000671605485427 55830580251001007408228141)
                ·
                  refine ⟨20936467594125377778085553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55830580251001007408228141 20936467594125377778085553)
                  ·
                    refine ⟨15702350695594033333564165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20936467594125377778085553 15702350695594033333564165)
                    ·
                      refine ⟨2944190755423881250043281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15702350695594033333564165 2944190755423881250043281)
                      ·
                        rfl

theorem cell23_5733791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_5733791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733791 prefixEnd_5733791 := by exact prefixLift 5733791
  have htrace : WordTrace (prefixWord ++ tailWord_5733791) baseStart_5733791 baseEnd_5733791 := by
    simpa [prefixWord, tailWord_5733791, baseEnd_5733791] using wordTrace_append hprefix tailTrace_5733791
  have hstable : (prefixWord ++ tailWord_5733791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733791).length < 2 ^ (prefixWord ++ tailWord_5733791).sum := by decide
  have hdescent : baseEnd_5733791 < baseStart_5733791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733805 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_5733805 : Nat := 118140960795 + 5733805 * 2 ^ 59
def prefixEnd_5733805 : Nat := 4983230072969 + 3 ^ 40 * 5733805 * 2
def baseEnd_5733805 : Nat := 981399314717681398422739

theorem tailTrace_5733805 : CollatzResearch.WordTrace tailWord_5733805 prefixEnd_5733805 981399314717681398422739 := by
  unfold tailWord_5733805
  simp only [CollatzResearch.WordTrace]
  refine ⟨209129048992411215776562869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139419365994940810517708579 209129048992411215776562869)
  ·
    refine ⟨19605848343038551479052769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209129048992411215776562869 19605848343038551479052769)
    ·
      refine ⟨14704386257278913609289577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19605848343038551479052769 14704386257278913609289577)
      ·
        refine ⟨11028289692959185206967183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14704386257278913609289577 11028289692959185206967183)
        ·
          refine ⟨16542434539438777810450775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11028289692959185206967183 16542434539438777810450775)
          ·
            refine ⟨24813651809158166715676163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16542434539438777810450775 24813651809158166715676163)
            ·
              refine ⟨37220477713737250073514245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24813651809158166715676163 37220477713737250073514245)
              ·
                refine ⟨6978839571325734388783921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37220477713737250073514245 6978839571325734388783921)
                ·
                  refine ⟨5234129678494300791587941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6978839571325734388783921 5234129678494300791587941)
                  ·
                    refine ⟨981399314717681398422739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5234129678494300791587941 981399314717681398422739)
                    ·
                      rfl

theorem cell23_5733805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_5733805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733805 prefixEnd_5733805 := by exact prefixLift 5733805
  have htrace : WordTrace (prefixWord ++ tailWord_5733805) baseStart_5733805 baseEnd_5733805 := by
    simpa [prefixWord, tailWord_5733805, baseEnd_5733805] using wordTrace_append hprefix tailTrace_5733805
  have hstable : (prefixWord ++ tailWord_5733805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733805).length < 2 ^ (prefixWord ++ tailWord_5733805).sum := by decide
  have hdescent : baseEnd_5733805 < baseStart_5733805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733846 : List Nat := [5, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_5733846 : Nat := 118140960795 + 5733846 * 2 ^ 59
def prefixEnd_5733846 : Nat := 4983230072969 + 3 ^ 40 * 5733846 * 2
def baseEnd_5733846 : Nat := 2944218996859878534855529

theorem tailTrace_5733846 : CollatzResearch.WordTrace tailWord_5733846 prefixEnd_5733846 2944218996859878534855529 := by
  unfold tailWord_5733846
  simp only [CollatzResearch.WordTrace]
  refine ⟨13070659024078917486175337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139420362923508453185870261 13070659024078917486175337)
  ·
    refine ⟨9802994268059188114631503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13070659024078917486175337 9802994268059188114631503)
    ·
      refine ⟨14704491402088782171947255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9802994268059188114631503 14704491402088782171947255)
      ·
        refine ⟨22056737103133173257920883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14704491402088782171947255 22056737103133173257920883)
        ·
          refine ⟨33085105654699759886881325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22056737103133173257920883 33085105654699759886881325)
          ·
            refine ⟨12406914620512409957580497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33085105654699759886881325 12406914620512409957580497)
            ·
              refine ⟨9305185965384307468185373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12406914620512409957580497 9305185965384307468185373)
              ·
                refine ⟨3489444737019115300569515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9305185965384307468185373 3489444737019115300569515)
                ·
                  refine ⟨5234167105528672950854273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3489444737019115300569515 5234167105528672950854273)
                  ·
                    refine ⟨3925625329146504713140705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5234167105528672950854273 3925625329146504713140705)
                    ·
                      refine ⟨2944218996859878534855529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3925625329146504713140705 2944218996859878534855529)
                      ·
                        rfl

theorem cell23_5733846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_5733846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733846 prefixEnd_5733846 := by exact prefixLift 5733846
  have htrace : WordTrace (prefixWord ++ tailWord_5733846) baseStart_5733846 baseEnd_5733846 := by
    simpa [prefixWord, tailWord_5733846, baseEnd_5733846] using wordTrace_append hprefix tailTrace_5733846
  have hstable : (prefixWord ++ tailWord_5733846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733846).length < 2 ^ (prefixWord ++ tailWord_5733846).sum := by decide
  have hdescent : baseEnd_5733846 < baseStart_5733846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733855 : List Nat := [1, 1, 2, 3, 3, 1, 3, 3, 1, 3, 2]
def baseStart_5733855 : Nat := 118140960795 + 5733855 * 2 ^ 59
def prefixEnd_5733855 : Nat := 4983230072969 + 3 ^ 40 * 5733855 * 2
def baseEnd_5733855 : Nat := 2944223618185768999642987

theorem tailTrace_5733855 : CollatzResearch.WordTrace tailWord_5733855 prefixEnd_5733855 2944223618185768999642987 := by
  unfold tailWord_5733855
  simp only [CollatzResearch.WordTrace]
  refine ⟨209130872642230074315883019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139420581761486716210588679 209130872642230074315883019)
  ·
    refine ⟨313696308963345111473824529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209130872642230074315883019 313696308963345111473824529)
    ·
      refine ⟨235272231722508833605368397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313696308963345111473824529 235272231722508833605368397)
      ·
        refine ⟨88227086895940812602013149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235272231722508833605368397 88227086895940812602013149)
        ·
          refine ⟨33085157585977804725754931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88227086895940812602013149 33085157585977804725754931)
          ·
            refine ⟨49627736378966707088632397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33085157585977804725754931 49627736378966707088632397)
            ·
              refine ⟨18610401142112515158237149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49627736378966707088632397 18610401142112515158237149)
              ·
                refine ⟨6978900428292193184338931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18610401142112515158237149 6978900428292193184338931)
                ·
                  refine ⟨10468350642438289776508397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6978900428292193184338931 10468350642438289776508397)
                  ·
                    refine ⟨3925631490914358666190649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10468350642438289776508397 3925631490914358666190649)
                    ·
                      refine ⟨2944223618185768999642987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3925631490914358666190649 2944223618185768999642987)
                      ·
                        rfl

theorem cell23_5733855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_5733855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733855 prefixEnd_5733855 := by exact prefixLift 5733855
  have htrace : WordTrace (prefixWord ++ tailWord_5733855) baseStart_5733855 baseEnd_5733855 := by
    simpa [prefixWord, tailWord_5733855, baseEnd_5733855] using wordTrace_append hprefix tailTrace_5733855
  have hstable : (prefixWord ++ tailWord_5733855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733855).length < 2 ^ (prefixWord ++ tailWord_5733855).sum := by decide
  have hdescent : baseEnd_5733855 < baseStart_5733855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733871 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 3]
def baseStart_5733871 : Nat := 118140960795 + 5733871 * 2 ^ 59
def prefixEnd_5733871 : Nat := 4983230072969 + 3 ^ 40 * 5733871 * 2
def baseEnd_5733871 : Nat := 2944231833876240937042913

theorem tailTrace_5733871 : CollatzResearch.WordTrace tailWord_5733871 prefixEnd_5733871 2944231833876240937042913 := by
  unfold tailWord_5733871
  simp only [CollatzResearch.WordTrace]
  refine ⟨209131456210172109048465467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139420970806781406032310311 209131456210172109048465467)
  ·
    refine ⟨313697184315258163572698201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209131456210172109048465467 313697184315258163572698201)
    ·
      refine ⟨235272888236443622679523651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313697184315258163572698201 235272888236443622679523651)
      ·
        refine ⟨352909332354665434019285477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235272888236443622679523651 352909332354665434019285477)
        ·
          refine ⟨66170499816499768878616027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 352909332354665434019285477 66170499816499768878616027)
          ·
            refine ⟨99255749724749653317924041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66170499816499768878616027 99255749724749653317924041)
            ·
              refine ⟨74441812293562239988443031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99255749724749653317924041 74441812293562239988443031)
              ·
                refine ⟨111662718440343359982664547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74441812293562239988443031 111662718440343359982664547)
                ·
                  refine ⟨167494077660515039973996821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111662718440343359982664547 167494077660515039973996821)
                  ·
                    refine ⟨7851284890336642498781101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 167494077660515039973996821 7851284890336642498781101)
                    ·
                      refine ⟨2944231833876240937042913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7851284890336642498781101 2944231833876240937042913)
                      ·
                        rfl

theorem cell23_5733871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 3].length) (baseStart_5733871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733871 prefixEnd_5733871 := by exact prefixLift 5733871
  have htrace : WordTrace (prefixWord ++ tailWord_5733871) baseStart_5733871 baseEnd_5733871 := by
    simpa [prefixWord, tailWord_5733871, baseEnd_5733871] using wordTrace_append hprefix tailTrace_5733871
  have hstable : (prefixWord ++ tailWord_5733871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733871).length < 2 ^ (prefixWord ++ tailWord_5733871).sum := by decide
  have hdescent : baseEnd_5733871 < baseStart_5733871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733878 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_5733878 : Nat := 118140960795 + 5733878 * 2 ^ 59
def prefixEnd_5733878 : Nat := 4983230072969 + 3 ^ 40 * 5733878 * 2
def baseEnd_5733878 : Nat := 981411809413607469885127

theorem tailTrace_5733878 : CollatzResearch.WordTrace tailWord_5733878 prefixEnd_5733878 981411809413607469885127 := by
  unfold tailWord_5733878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13070731970071671827748143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139421141014097832829313525 13070731970071671827748143)
  ·
    refine ⟨19606097955107507741622215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13070731970071671827748143 19606097955107507741622215)
    ·
      refine ⟨29409146932661261612433323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19606097955107507741622215 29409146932661261612433323)
      ·
        refine ⟨44113720398991892418649985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29409146932661261612433323 44113720398991892418649985)
        ·
          refine ⟨33085290299243919313987489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44113720398991892418649985 33085290299243919313987489)
          ·
            refine ⟨24813967724432939485490617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33085290299243919313987489 24813967724432939485490617)
            ·
              refine ⟨18610475793324704614117963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24813967724432939485490617 18610475793324704614117963)
              ·
                refine ⟨27915713689987056921176945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18610475793324704614117963 27915713689987056921176945)
                ·
                  refine ⟨20936785267490292690882709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27915713689987056921176945 20936785267490292690882709)
                  ·
                    refine ⟨981411809413607469885127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20936785267490292690882709 981411809413607469885127)
                    ·
                      rfl

theorem cell23_5733878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_5733878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733878 prefixEnd_5733878 := by exact prefixLift 5733878
  have htrace : WordTrace (prefixWord ++ tailWord_5733878) baseStart_5733878 baseEnd_5733878 := by
    simpa [prefixWord, tailWord_5733878, baseEnd_5733878] using wordTrace_append hprefix tailTrace_5733878
  have hstable : (prefixWord ++ tailWord_5733878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733878).length < 2 ^ (prefixWord ++ tailWord_5733878).sum := by decide
  have hdescent : baseEnd_5733878 < baseStart_5733878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733885 : List Nat := [1, 4, 1, 1, 1, 4, 3, 1, 1, 4, 2]
def baseStart_5733885 : Nat := 118140960795 + 5733885 * 2 ^ 59
def prefixEnd_5733885 : Nat := 4983230072969 + 3 ^ 40 * 5733885 * 2
def baseEnd_5733885 : Nat := 2944239022605403882267849

theorem tailTrace_5733885 : CollatzResearch.WordTrace tailWord_5733885 prefixEnd_5733885 2944239022605403882267849 := by
  unfold tailWord_5733885
  simp only [CollatzResearch.WordTrace]
  refine ⟨209131966832121389439475109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139421311221414259626316739 209131966832121389439475109)
  ·
    refine ⟨39212243781022760519901583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209131966832121389439475109 39212243781022760519901583)
    ·
      refine ⟨58818365671534140779852375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39212243781022760519901583 58818365671534140779852375)
      ·
        refine ⟨88227548507301211169778563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58818365671534140779852375 88227548507301211169778563)
        ·
          refine ⟨132341322760951816754667845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88227548507301211169778563 132341322760951816754667845)
          ·
            refine ⟨24813998017678465641500221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132341322760951816754667845 24813998017678465641500221)
            ·
              refine ⟨9305249256629424615562583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24813998017678465641500221 9305249256629424615562583)
              ·
                refine ⟨13957873884944136923343875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9305249256629424615562583 13957873884944136923343875)
                ·
                  refine ⟨20936810827416205385015813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13957873884944136923343875 20936810827416205385015813)
                  ·
                    refine ⟨3925652030140538509690465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20936810827416205385015813 3925652030140538509690465)
                    ·
                      refine ⟨2944239022605403882267849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3925652030140538509690465 2944239022605403882267849)
                      ·
                        rfl

theorem cell23_5733885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_5733885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733885 prefixEnd_5733885 := by exact prefixLift 5733885
  have htrace : WordTrace (prefixWord ++ tailWord_5733885) baseStart_5733885 baseEnd_5733885 := by
    simpa [prefixWord, tailWord_5733885, baseEnd_5733885] using wordTrace_append hprefix tailTrace_5733885
  have hstable : (prefixWord ++ tailWord_5733885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733885).length < 2 ^ (prefixWord ++ tailWord_5733885).sum := by decide
  have hdescent : baseEnd_5733885 < baseStart_5733885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733971 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 4]
def baseStart_5733971 : Nat := 118140960795 + 5733971 * 2 ^ 59
def prefixEnd_5733971 : Nat := 4983230072969 + 3 ^ 40 * 5733971 * 2
def baseEnd_5733971 : Nat := 2944283181941690545792453

theorem tailTrace_5733971 : CollatzResearch.WordTrace tailWord_5733971 prefixEnd_5733971 2944283181941690545792453 := by
  unfold tailWord_5733971
  simp only [CollatzResearch.WordTrace]
  refine ⟨209135103509809826127105767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139423402339873217418070511 209135103509809826127105767)
  ·
    refine ⟨313702655264714739190658651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209135103509809826127105767 313702655264714739190658651)
    ·
      refine ⟨470553982897072108785987977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313702655264714739190658651 470553982897072108785987977)
      ·
        refine ⟨352915487172804081589490983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470553982897072108785987977 352915487172804081589490983)
        ·
          refine ⟨529373230759206122384236475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352915487172804081589490983 529373230759206122384236475)
          ·
            refine ⟨794059846138809183576354713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529373230759206122384236475 794059846138809183576354713)
            ·
              refine ⟨595544884604106887682266035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794059846138809183576354713 595544884604106887682266035)
              ·
                refine ⟨893317326906160331523399053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595544884604106887682266035 893317326906160331523399053)
                ·
                  refine ⟨334993997589810124321274645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893317326906160331523399053 334993997589810124321274645)
                  ·
                    refine ⟨15702843637022349577559749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 334993997589810124321274645 15702843637022349577559749)
                    ·
                      refine ⟨2944283181941690545792453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15702843637022349577559749 2944283181941690545792453)
                      ·
                        rfl

theorem cell23_5733971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_5733971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733971 prefixEnd_5733971 := by exact prefixLift 5733971
  have htrace : WordTrace (prefixWord ++ tailWord_5733971) baseStart_5733971 baseEnd_5733971 := by
    simpa [prefixWord, tailWord_5733971, baseEnd_5733971] using wordTrace_append hprefix tailTrace_5733971
  have hstable : (prefixWord ++ tailWord_5733971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733971).length < 2 ^ (prefixWord ++ tailWord_5733971).sum := by decide
  have hdescent : baseEnd_5733971 < baseStart_5733971 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5733992 : List Nat := [2, 1, 4, 3, 1, 2, 1, 1, 2, 4, 2]
def baseStart_5733992 : Nat := 118140960795 + 5733992 * 2 ^ 59
def prefixEnd_5733992 : Nat := 4983230072969 + 3 ^ 40 * 5733992 * 2
def baseEnd_5733992 : Nat := 2944293965035434963629857

theorem tailTrace_5733992 : CollatzResearch.WordTrace tailWord_5733992 prefixEnd_5733992 2944293965035434963629857 := by
  unfold tailWord_5733992
  simp only [CollatzResearch.WordTrace]
  refine ⟨104567934721366873356810115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139423912961822497809080153 104567934721366873356810115)
  ·
    refine ⟨156851902082050310035215173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104567934721366873356810115 156851902082050310035215173)
    ·
      refine ⟨29409731640384433131602845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156851902082050310035215173 29409731640384433131602845)
      ·
        refine ⟨11028649365144162424351067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29409731640384433131602845 11028649365144162424351067)
        ·
          refine ⟨16542974047716243636526601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11028649365144162424351067 16542974047716243636526601)
          ·
            refine ⟨12407230535787182727394951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16542974047716243636526601 12407230535787182727394951)
            ·
              refine ⟨18610845803680774091092427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12407230535787182727394951 18610845803680774091092427)
              ·
                refine ⟨27916268705521161136638641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18610845803680774091092427 27916268705521161136638641)
                ·
                  refine ⟨20937201529140870852478981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27916268705521161136638641 20937201529140870852478981)
                  ·
                    refine ⟨3925725286713913284839809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20937201529140870852478981 3925725286713913284839809)
                    ·
                      refine ⟨2944293965035434963629857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3925725286713913284839809 2944293965035434963629857)
                      ·
                        rfl

theorem cell23_5733992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_5733992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5733992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5733992 prefixEnd_5733992 := by exact prefixLift 5733992
  have htrace : WordTrace (prefixWord ++ tailWord_5733992) baseStart_5733992 baseEnd_5733992 := by
    simpa [prefixWord, tailWord_5733992, baseEnd_5733992] using wordTrace_append hprefix tailTrace_5733992
  have hstable : (prefixWord ++ tailWord_5733992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5733992).length < 2 ^ (prefixWord ++ tailWord_5733992).sum := by decide
  have hdescent : baseEnd_5733992 < baseStart_5733992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5733992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734076 : List Nat := [2, 2, 2, 3, 1, 4, 1, 3, 1, 1, 3]
def baseStart_5734076 : Nat := 118140960795 + 5734076 * 2 ^ 59
def prefixEnd_5734076 : Nat := 4983230072969 + 3 ^ 40 * 5734076 * 2
def baseEnd_5734076 : Nat := 2944337097410412634979471

theorem tailTrace_5734076 : CollatzResearch.WordTrace tailWord_5734076 prefixEnd_5734076 2944337097410412634979471 := by
  unfold tailWord_5734076
  simp only [CollatzResearch.WordTrace]
  refine ⟨104569466587214714529839041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139425955449619619373118721 104569466587214714529839041)
  ·
    refine ⟨78427099940411035897379281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104569466587214714529839041 78427099940411035897379281)
    ·
      refine ⟨58820324955308276923034461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78427099940411035897379281 58820324955308276923034461)
      ·
        refine ⟨22057621858240603846137923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58820324955308276923034461 22057621858240603846137923)
        ·
          refine ⟨33086432787360905769206885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22057621858240603846137923 33086432787360905769206885)
          ·
            refine ⟨6203706147630169831726291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33086432787360905769206885 6203706147630169831726291)
            ·
              refine ⟨9305559221445254747589437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6203706147630169831726291 9305559221445254747589437)
              ·
                refine ⟨3489584708041970530346039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9305559221445254747589437 3489584708041970530346039)
                ·
                  refine ⟨5234377062062955795519059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3489584708041970530346039 5234377062062955795519059)
                  ·
                    refine ⟨7851565593094433693278589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5234377062062955795519059 7851565593094433693278589)
                    ·
                      refine ⟨2944337097410412634979471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7851565593094433693278589 2944337097410412634979471)
                      ·
                        rfl

theorem cell23_5734076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_5734076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734076 prefixEnd_5734076 := by exact prefixLift 5734076
  have htrace : WordTrace (prefixWord ++ tailWord_5734076) baseStart_5734076 baseEnd_5734076 := by
    simpa [prefixWord, tailWord_5734076, baseEnd_5734076] using wordTrace_append hprefix tailTrace_5734076
  have hstable : (prefixWord ++ tailWord_5734076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734076).length < 2 ^ (prefixWord ++ tailWord_5734076).sum := by decide
  have hdescent : baseEnd_5734076 < baseStart_5734076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734086 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_5734086 : Nat := 118140960795 + 5734086 * 2 ^ 59
def prefixEnd_5734086 : Nat := 4983230072969 + 3 ^ 40 * 5734086 * 2
def baseEnd_5734086 : Nat := 2944342232216957595854425

theorem tailTrace_5734086 : CollatzResearch.WordTrace tailWord_5734086 prefixEnd_5734086 2944342232216957595854425 := by
  unfold tailWord_5734086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6535603059512287523985691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 139426198602928800511694741 6535603059512287523985691)
  ·
    refine ⟨9803404589268431285978537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6535603059512287523985691 9803404589268431285978537)
    ·
      refine ⟨7352553441951323464483903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9803404589268431285978537 7352553441951323464483903)
      ·
        refine ⟨11028830162926985196725855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7352553441951323464483903 11028830162926985196725855)
        ·
          refine ⟨16543245244390477795088783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11028830162926985196725855 16543245244390477795088783)
          ·
            refine ⟨24814867866585716692633175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16543245244390477795088783 24814867866585716692633175)
            ·
              refine ⟨37222301799878575038949763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24814867866585716692633175 37222301799878575038949763)
              ·
                refine ⟨55833452699817862558424645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37222301799878575038949763 55833452699817862558424645)
                ·
                  refine ⟨10468772381215849229704621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55833452699817862558424645 10468772381215849229704621)
                  ·
                    refine ⟨3925789642955943461139233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10468772381215849229704621 3925789642955943461139233)
                    ·
                      refine ⟨2944342232216957595854425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3925789642955943461139233 2944342232216957595854425)
                      ·
                        rfl

theorem cell23_5734086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_5734086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734086 prefixEnd_5734086 := by exact prefixLift 5734086
  have htrace : WordTrace (prefixWord ++ tailWord_5734086) baseStart_5734086 baseEnd_5734086 := by
    simpa [prefixWord, tailWord_5734086, baseEnd_5734086] using wordTrace_append hprefix tailTrace_5734086
  have hstable : (prefixWord ++ tailWord_5734086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734086).length < 2 ^ (prefixWord ++ tailWord_5734086).sum := by decide
  have hdescent : baseEnd_5734086 < baseStart_5734086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734119 : List Nat := [1, 1, 5, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5734119 : Nat := 118140960795 + 5734119 * 2 ^ 59
def prefixEnd_5734119 : Nat := 4983230072969 + 3 ^ 40 * 5734119 * 2
def baseEnd_5734119 : Nat := 2944359177078555966741773

theorem tailTrace_5734119 : CollatzResearch.WordTrace tailWord_5734119 prefixEnd_5734119 2944359177078555966741773 := by
  unfold tailWord_5734119
  simp only [CollatzResearch.WordTrace]
  refine ⟨209140501513273647403493411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139427001008849098268995607 209140501513273647403493411)
  ·
    refine ⟨313710752269910471105240117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209140501513273647403493411 313710752269910471105240117)
    ·
      refine ⟨29410383025304106666116261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 313710752269910471105240117 29410383025304106666116261)
      ·
        refine ⟨5514446817244519999896799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29410383025304106666116261 5514446817244519999896799)
        ·
          refine ⟨8271670225866779999845199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5514446817244519999896799 8271670225866779999845199)
          ·
            refine ⟨12407505338800169999767799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8271670225866779999845199 12407505338800169999767799)
            ·
              refine ⟨18611258008200254999651699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12407505338800169999767799 18611258008200254999651699)
              ·
                refine ⟨27916887012300382499477549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18611258008200254999651699 27916887012300382499477549)
                ·
                  refine ⟨10468832629612643437304081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27916887012300382499477549 10468832629612643437304081)
                  ·
                    refine ⟨7851624472209482577978061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10468832629612643437304081 7851624472209482577978061)
                    ·
                      refine ⟨2944359177078555966741773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7851624472209482577978061 2944359177078555966741773)
                      ·
                        rfl

theorem cell23_5734119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5734119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734119 prefixEnd_5734119 := by exact prefixLift 5734119
  have htrace : WordTrace (prefixWord ++ tailWord_5734119) baseStart_5734119 baseEnd_5734119 := by
    simpa [prefixWord, tailWord_5734119, baseEnd_5734119] using wordTrace_append hprefix tailTrace_5734119
  have hstable : (prefixWord ++ tailWord_5734119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734119).length < 2 ^ (prefixWord ++ tailWord_5734119).sum := by decide
  have hdescent : baseEnd_5734119 < baseStart_5734119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734128 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 5]
def baseStart_5734128 : Nat := 118140960795 + 5734128 * 2 ^ 59
def prefixEnd_5734128 : Nat := 4983230072969 + 3 ^ 40 * 5734128 * 2
def baseEnd_5734128 : Nat := 2944363798404446431529231

theorem tailTrace_5734128 : CollatzResearch.WordTrace tailWord_5734128 prefixEnd_5734128 2944363798404446431529231 := by
  unfold tailWord_5734128
  simp only [CollatzResearch.WordTrace]
  refine ⟨104570414885120520970285519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139427219846827361293714025 104570414885120520970285519)
  ·
    refine ⟨156855622327680781455428279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104570414885120520970285519 156855622327680781455428279)
    ·
      refine ⟨235283433491521172183142419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156855622327680781455428279 235283433491521172183142419)
      ·
        refine ⟨352925150237281758274713629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235283433491521172183142419 352925150237281758274713629)
        ·
          refine ⟨132346931338980659353017611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352925150237281758274713629 132346931338980659353017611)
          ·
            refine ⟨198520397008470989029526417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132346931338980659353017611 198520397008470989029526417)
            ·
              refine ⟨148890297756353241772144813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198520397008470989029526417 148890297756353241772144813)
              ·
                refine ⟨55833861658632465664554305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148890297756353241772144813 55833861658632465664554305)
                ·
                  refine ⟨41875396243974349248415729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55833861658632465664554305 41875396243974349248415729)
                  ·
                    refine ⟨31406547182980761936311797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41875396243974349248415729 31406547182980761936311797)
                    ·
                      refine ⟨2944363798404446431529231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31406547182980761936311797 2944363798404446431529231)
                      ·
                        rfl

theorem cell23_5734128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_5734128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734128 prefixEnd_5734128 := by exact prefixLift 5734128
  have htrace : WordTrace (prefixWord ++ tailWord_5734128) baseStart_5734128 baseEnd_5734128 := by
    simpa [prefixWord, tailWord_5734128, baseEnd_5734128] using wordTrace_append hprefix tailTrace_5734128
  have hstable : (prefixWord ++ tailWord_5734128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734128).length < 2 ^ (prefixWord ++ tailWord_5734128).sum := by decide
  have hdescent : baseEnd_5734128 < baseStart_5734128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734165 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_5734165 : Nat := 118140960795 + 5734165 * 2 ^ 59
def prefixEnd_5734165 : Nat := 4983230072969 + 3 ^ 40 * 5734165 * 2
def baseEnd_5734165 : Nat := 981460932396220928922187

theorem tailTrace_5734165 : CollatzResearch.WordTrace tailWord_5734165 prefixEnd_5734165 981460932396220928922187 := by
  unfold tailWord_5734165
  simp only [CollatzResearch.WordTrace]
  refine ⟨209142179271106997259667949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139428119514071331506445299 209142179271106997259667949)
  ·
    refine ⟨78428317226665123972375481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209142179271106997259667949 78428317226665123972375481)
    ·
      refine ⟨58821237919998842979281611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78428317226665123972375481 58821237919998842979281611)
      ·
        refine ⟨88231856879998264468922417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58821237919998842979281611 88231856879998264468922417)
        ·
          refine ⟨66173892659998698351691813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88231856879998264468922417 66173892659998698351691813)
          ·
            refine ⟨12407604873749755940942215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66173892659998698351691813 12407604873749755940942215)
            ·
              refine ⟨18611407310624633911413323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12407604873749755940942215 18611407310624633911413323)
              ·
                refine ⟨27917110965936950867119985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18611407310624633911413323 27917110965936950867119985)
                ·
                  refine ⟨20937833224452713150339989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27917110965936950867119985 20937833224452713150339989)
                  ·
                    refine ⟨981460932396220928922187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20937833224452713150339989 981460932396220928922187)
                    ·
                      rfl

theorem cell23_5734165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_5734165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734165 prefixEnd_5734165 := by exact prefixLift 5734165
  have htrace : WordTrace (prefixWord ++ tailWord_5734165) baseStart_5734165 baseEnd_5734165 := by
    simpa [prefixWord, tailWord_5734165, baseEnd_5734165] using wordTrace_append hprefix tailTrace_5734165
  have hstable : (prefixWord ++ tailWord_5734165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734165).length < 2 ^ (prefixWord ++ tailWord_5734165).sum := by decide
  have hdescent : baseEnd_5734165 < baseStart_5734165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734175 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 3]
def baseStart_5734175 : Nat := 118140960795 + 5734175 * 2 ^ 59
def prefixEnd_5734175 : Nat := 4983230072969 + 3 ^ 40 * 5734175 * 2
def baseEnd_5734175 : Nat := 2944387931995207747641515

theorem tailTrace_5734175 : CollatzResearch.WordTrace tailWord_5734175 prefixEnd_5734175 2944387931995207747641515 := by
  unfold tailWord_5734175
  simp only [CollatzResearch.WordTrace]
  refine ⟨209142544001070768967531979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139428362667380512645021319 209142544001070768967531979)
  ·
    refine ⟨313713816001606153451297969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209142544001070768967531979 313713816001606153451297969)
    ·
      refine ⟨235285362001204615088473477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313713816001606153451297969 235285362001204615088473477)
      ·
        refine ⟨44116005375225865329088777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235285362001204615088473477 44116005375225865329088777)
        ·
          refine ⟨33087004031419398996816583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44116005375225865329088777 33087004031419398996816583)
          ·
            refine ⟨49630506047129098495224875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33087004031419398996816583 49630506047129098495224875)
            ·
              refine ⟨74445759070693647742837313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49630506047129098495224875 74445759070693647742837313)
              ·
                refine ⟨55834319303020235807127985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74445759070693647742837313 55834319303020235807127985)
                ·
                  refine ⟨41875739477265176855345989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55834319303020235807127985 41875739477265176855345989)
                  ·
                    refine ⟨7851701151987220660377373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41875739477265176855345989 7851701151987220660377373)
                    ·
                      refine ⟨2944387931995207747641515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7851701151987220660377373 2944387931995207747641515)
                      ·
                        rfl

theorem cell23_5734175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_5734175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734175 prefixEnd_5734175 := by exact prefixLift 5734175
  have htrace : WordTrace (prefixWord ++ tailWord_5734175) baseStart_5734175 baseEnd_5734175 := by
    simpa [prefixWord, tailWord_5734175, baseEnd_5734175] using wordTrace_append hprefix tailTrace_5734175
  have hstable : (prefixWord ++ tailWord_5734175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734175).length < 2 ^ (prefixWord ++ tailWord_5734175).sum := by decide
  have hdescent : baseEnd_5734175 < baseStart_5734175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734206 : List Nat := [4, 2, 1, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_5734206 : Nat := 118140960795 + 5734206 * 2 ^ 59
def prefixEnd_5734206 : Nat := 4983230072969 + 3 ^ 40 * 5734206 * 2
def baseEnd_5734206 : Nat := 2944403849895497126353873

theorem tailTrace_5734206 : CollatzResearch.WordTrace tailWord_5734206 prefixEnd_5734206 2944403849895497126353873 := by
  unfold tailWord_5734206
  simp only [CollatzResearch.WordTrace]
  refine ⟨26142959332994807657738809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139429116442638974174606981 26142959332994807657738809)
  ·
    refine ⟨19607219499746105743304107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26142959332994807657738809 19607219499746105743304107)
    ·
      refine ⟨29410829249619158614956161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19607219499746105743304107 29410829249619158614956161)
      ·
        refine ⟨22058121937214368961217121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29410829249619158614956161 22058121937214368961217121)
        ·
          refine ⟨16543591452910776720912841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22058121937214368961217121 16543591452910776720912841)
          ·
            refine ⟨12407693589683082540684631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16543591452910776720912841 12407693589683082540684631)
            ·
              refine ⟨18611540384524623811026947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12407693589683082540684631 18611540384524623811026947)
              ·
                refine ⟨27917310576786935716540421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18611540384524623811026947 27917310576786935716540421)
                ·
                  refine ⟨5234495733147550446851329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27917310576786935716540421 5234495733147550446851329)
                  ·
                    refine ⟨3925871799860662835138497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5234495733147550446851329 3925871799860662835138497)
                    ·
                      refine ⟨2944403849895497126353873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3925871799860662835138497 2944403849895497126353873)
                      ·
                        rfl

theorem cell23_5734206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_5734206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734206 prefixEnd_5734206 := by exact prefixLift 5734206
  have htrace : WordTrace (prefixWord ++ tailWord_5734206) baseStart_5734206 baseEnd_5734206 := by
    simpa [prefixWord, tailWord_5734206, baseEnd_5734206] using wordTrace_append hprefix tailTrace_5734206
  have hstable : (prefixWord ++ tailWord_5734206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734206).length < 2 ^ (prefixWord ++ tailWord_5734206).sum := by decide
  have hdescent : baseEnd_5734206 < baseStart_5734206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734225 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 1, 7]
def baseStart_5734225 : Nat := 118140960795 + 5734225 * 2 ^ 59
def prefixEnd_5734225 : Nat := 4983230072969 + 3 ^ 40 * 5734225 * 2
def baseEnd_5734225 : Nat := 981471202009310850672095

theorem tailTrace_5734225 : CollatzResearch.WordTrace tailWord_5734225 prefixEnd_5734225 981471202009310850672095 := by
  unfold tailWord_5734225
  simp only [CollatzResearch.WordTrace]
  refine ⟨209144367650889627506852129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139429578433926418337901419 209144367650889627506852129)
  ·
    refine ⟨156858275738167220630139097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209144367650889627506852129 156858275738167220630139097)
    ·
      refine ⟨117643706803625415472604323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156858275738167220630139097 117643706803625415472604323)
      ·
        refine ⟨176465560205438123208906485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117643706803625415472604323 176465560205438123208906485)
        ·
          refine ⟨16543646269259824050834983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176465560205438123208906485 16543646269259824050834983)
          ·
            refine ⟨24815469403889736076252475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16543646269259824050834983 24815469403889736076252475)
            ·
              refine ⟨37223204105834604114378713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24815469403889736076252475 37223204105834604114378713)
              ·
                refine ⟨27917403079375953085784035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37223204105834604114378713 27917403079375953085784035)
                ·
                  refine ⟨41876104619063929628676053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27917403079375953085784035 41876104619063929628676053)
                  ·
                    refine ⟨981471202009310850672095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41876104619063929628676053 981471202009310850672095)
                    ·
                      rfl

theorem cell23_5734225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_5734225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734225 prefixEnd_5734225 := by exact prefixLift 5734225
  have htrace : WordTrace (prefixWord ++ tailWord_5734225) baseStart_5734225 baseEnd_5734225 := by
    simpa [prefixWord, tailWord_5734225, baseEnd_5734225] using wordTrace_append hprefix tailTrace_5734225
  have hstable : (prefixWord ++ tailWord_5734225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734225).length < 2 ^ (prefixWord ++ tailWord_5734225).sum := by decide
  have hdescent : baseEnd_5734225 < baseStart_5734225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734242 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_5734242 : Nat := 118140960795 + 5734242 * 2 ^ 59
def prefixEnd_5734242 : Nat := 4983230072969 + 3 ^ 40 * 5734242 * 2
def baseEnd_5734242 : Nat := 981474111733019661834569

theorem tailTrace_5734242 : CollatzResearch.WordTrace tailWord_5734242 prefixEnd_5734242 981474111733019661834569 := by
  unfold tailWord_5734242
  simp only [CollatzResearch.WordTrace]
  refine ⟨52286246922957009852555245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139429991794552026273480653 52286246922957009852555245)
  ·
    refine ⟨19607342596108878694708217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52286246922957009852555245 19607342596108878694708217)
    ·
      refine ⟨14705506947081659021031163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19607342596108878694708217 14705506947081659021031163)
      ·
        refine ⟨22058260420622488531546745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14705506947081659021031163 22058260420622488531546745)
        ·
          refine ⟨16543695315466866398660059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22058260420622488531546745 16543695315466866398660059)
          ·
            refine ⟨24815542973200299597990089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16543695315466866398660059 24815542973200299597990089)
            ·
              refine ⟨18611657229900224698492567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24815542973200299597990089 18611657229900224698492567)
              ·
                refine ⟨27917485844850337047738851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18611657229900224698492567 27917485844850337047738851)
                ·
                  refine ⟨41876228767275505571608277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27917485844850337047738851 41876228767275505571608277)
                  ·
                    refine ⟨981474111733019661834569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41876228767275505571608277 981474111733019661834569)
                    ·
                      rfl

theorem cell23_5734242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_5734242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734242 prefixEnd_5734242 := by exact prefixLift 5734242
  have htrace : WordTrace (prefixWord ++ tailWord_5734242) baseStart_5734242 baseEnd_5734242 := by
    simpa [prefixWord, tailWord_5734242, baseEnd_5734242] using wordTrace_append hprefix tailTrace_5734242
  have hstable : (prefixWord ++ tailWord_5734242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734242).length < 2 ^ (prefixWord ++ tailWord_5734242).sum := by decide
  have hdescent : baseEnd_5734242 < baseStart_5734242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734296 : List Nat := [2, 1, 2, 6, 1, 1, 2, 1, 2, 1, 4]
def baseStart_5734296 : Nat := 118140960795 + 5734296 * 2 ^ 59
def prefixEnd_5734296 : Nat := 4983230072969 + 3 ^ 40 * 5734296 * 2
def baseEnd_5734296 : Nat := 2944450063154401774228459

theorem tailTrace_5734296 : CollatzResearch.WordTrace tailWord_5734296 prefixEnd_5734296 2944450063154401774228459 := by
  unfold tailWord_5734296
  simp only [CollatzResearch.WordTrace]
  refine ⟨104573478616816203316343371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139431304822421604421791161 104573478616816203316343371)
  ·
    refine ⟨156860217925224304974515057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104573478616816203316343371 156860217925224304974515057)
    ·
      refine ⟨117645163443918228730886293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156860217925224304974515057 117645163443918228730886293)
      ·
        refine ⟨5514617036433666971760295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 117645163443918228730886293 5514617036433666971760295)
        ·
          refine ⟨8271925554650500457640443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5514617036433666971760295 8271925554650500457640443)
          ·
            refine ⟨12407888331975750686460665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8271925554650500457640443 12407888331975750686460665)
            ·
              refine ⟨9305916248981813014845499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12407888331975750686460665 9305916248981813014845499)
              ·
                refine ⟨13958874373472719522268249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9305916248981813014845499 13958874373472719522268249)
                ·
                  refine ⟨10469155780104539641701187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13958874373472719522268249 10469155780104539641701187)
                  ·
                    refine ⟨15703733670156809462551781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10469155780104539641701187 15703733670156809462551781)
                    ·
                      refine ⟨2944450063154401774228459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15703733670156809462551781 2944450063154401774228459)
                      ·
                        rfl

theorem cell23_5734296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_5734296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734296 prefixEnd_5734296 := by exact prefixLift 5734296
  have htrace : WordTrace (prefixWord ++ tailWord_5734296) baseStart_5734296 baseEnd_5734296 := by
    simpa [prefixWord, tailWord_5734296, baseEnd_5734296] using wordTrace_append hprefix tailTrace_5734296
  have hstable : (prefixWord ++ tailWord_5734296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734296).length < 2 ^ (prefixWord ++ tailWord_5734296).sum := by decide
  have hdescent : baseEnd_5734296 < baseStart_5734296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734315 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 7, 5]
def baseStart_5734315 : Nat := 118140960795 + 5734315 * 2 ^ 59
def prefixEnd_5734315 : Nat := 4983230072969 + 3 ^ 40 * 5734315 * 2
def baseEnd_5734315 : Nat := 981486606428945733296957

theorem tailTrace_5734315 : CollatzResearch.WordTrace tailWord_5734315 prefixEnd_5734315 981486606428945733296957 := by
  unfold tailWord_5734315
  simp only [CollatzResearch.WordTrace]
  refine ⟨209147650220563572877628399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139431766813709048585085599 209147650220563572877628399)
  ·
    refine ⟨313721475330845359316442599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209147650220563572877628399 313721475330845359316442599)
    ·
      refine ⟨470582212996268038974663899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313721475330845359316442599 470582212996268038974663899)
      ·
        refine ⟨705873319494402058461995849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470582212996268038974663899 705873319494402058461995849)
        ·
          refine ⟨529404989620801543846496887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705873319494402058461995849 529404989620801543846496887)
          ·
            refine ⟨794107484431202315769745331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529404989620801543846496887 794107484431202315769745331)
            ·
              refine ⟨1191161226646803473654617997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794107484431202315769745331 1191161226646803473654617997)
              ·
                refine ⟨446685459992551302620481749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1191161226646803473654617997 446685459992551302620481749)
                ·
                  refine ⟨10469190468575421155167541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 446685459992551302620481749 10469190468575421155167541)
                  ·
                    refine ⟨981486606428945733296957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10469190468575421155167541 981486606428945733296957)
                    ·
                      rfl

theorem cell23_5734315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 5].length) (baseStart_5734315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734315 prefixEnd_5734315 := by exact prefixLift 5734315
  have htrace : WordTrace (prefixWord ++ tailWord_5734315) baseStart_5734315 baseEnd_5734315 := by
    simpa [prefixWord, tailWord_5734315, baseEnd_5734315] using wordTrace_append hprefix tailTrace_5734315
  have hstable : (prefixWord ++ tailWord_5734315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734315).length < 2 ^ (prefixWord ++ tailWord_5734315).sum := by decide
  have hdescent : baseEnd_5734315 < baseStart_5734315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734329 : List Nat := [1, 2, 1, 4, 2, 1, 2, 3, 3, 1, 3]
def baseStart_5734329 : Nat := 118140960795 + 5734329 * 2 ^ 59
def prefixEnd_5734329 : Nat := 4983230072969 + 3 ^ 40 * 5734329 * 2
def baseEnd_5734329 : Nat := 2944467008016000145115807

theorem tailTrace_5734329 : CollatzResearch.WordTrace tailWord_5734329 prefixEnd_5734329 2944467008016000145115807 := by
  unfold tailWord_5734329
  simp only [CollatzResearch.WordTrace]
  refine ⟨209148160842512853268638041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139432107228341902179092027 209148160842512853268638041)
  ·
    refine ⟨156861120631884639951478531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209148160842512853268638041 156861120631884639951478531)
    ·
      refine ⟨235291680947826959927217797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156861120631884639951478531 235291680947826959927217797)
      ·
        refine ⟨44117190177717554986353337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235291680947826959927217797 44117190177717554986353337)
        ·
          refine ⟨33087892633288166239765003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44117190177717554986353337 33087892633288166239765003)
          ·
            refine ⟨49631838949932249359647505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33087892633288166239765003 49631838949932249359647505)
            ·
              refine ⟨37223879212449187019735629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49631838949932249359647505 37223879212449187019735629)
              ·
                refine ⟨13958954704668445132400861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37223879212449187019735629 13958954704668445132400861)
                ·
                  refine ⟨5234608014250666924650323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13958954704668445132400861 5234608014250666924650323)
                  ·
                    refine ⟨7851912021376000386975485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5234608014250666924650323 7851912021376000386975485)
                    ·
                      refine ⟨2944467008016000145115807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7851912021376000386975485 2944467008016000145115807)
                      ·
                        rfl

theorem cell23_5734329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_5734329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734329 prefixEnd_5734329 := by exact prefixLift 5734329
  have htrace : WordTrace (prefixWord ++ tailWord_5734329) baseStart_5734329 baseEnd_5734329 := by
    simpa [prefixWord, tailWord_5734329, baseEnd_5734329] using wordTrace_append hprefix tailTrace_5734329
  have hstable : (prefixWord ++ tailWord_5734329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734329).length < 2 ^ (prefixWord ++ tailWord_5734329).sum := by decide
  have hdescent : baseEnd_5734329 < baseStart_5734329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734345 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 5, 6]
def baseStart_5734345 : Nat := 118140960795 + 5734345 * 2 ^ 59
def prefixEnd_5734345 : Nat := 4983230072969 + 3 ^ 40 * 5734345 * 2
def baseEnd_5734345 : Nat := 981491741235490694171911

theorem tailTrace_5734345 : CollatzResearch.WordTrace tailWord_5734345 prefixEnd_5734345 981491741235490694171911 := by
  unfold tailWord_5734345
  simp only [CollatzResearch.WordTrace]
  refine ⟨209148744410454888001220489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139432496273636592000813659 209148744410454888001220489)
  ·
    refine ⟨156861558307841166000915367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209148744410454888001220489 156861558307841166000915367)
    ·
      refine ⟨235292337461761749001373051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156861558307841166000915367 235292337461761749001373051)
      ·
        refine ⟨352938506192642623502059577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235292337461761749001373051 352938506192642623502059577)
        ·
          refine ⟨264703879644481967626544683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352938506192642623502059577 264703879644481967626544683)
          ·
            refine ⟨397055819466722951439817025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264703879644481967626544683 397055819466722951439817025)
            ·
              refine ⟨297791864600042213579862769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397055819466722951439817025 297791864600042213579862769)
              ·
                refine ⟨223343898450031660184897077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297791864600042213579862769 223343898450031660184897077)
                ·
                  refine ⟨20938490479690468142334101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223343898450031660184897077 20938490479690468142334101)
                  ·
                    refine ⟨981491741235490694171911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20938490479690468142334101 981491741235490694171911)
                    ·
                      rfl

theorem cell23_5734345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_5734345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734345 prefixEnd_5734345 := by exact prefixLift 5734345
  have htrace : WordTrace (prefixWord ++ tailWord_5734345) baseStart_5734345 baseEnd_5734345 := by
    simpa [prefixWord, tailWord_5734345, baseEnd_5734345] using wordTrace_append hprefix tailTrace_5734345
  have hstable : (prefixWord ++ tailWord_5734345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734345).length < 2 ^ (prefixWord ++ tailWord_5734345).sum := by decide
  have hdescent : baseEnd_5734345 < baseStart_5734345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734352 : List Nat := [2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 4]
def baseStart_5734352 : Nat := 118140960795 + 5734352 * 2 ^ 59
def prefixEnd_5734352 : Nat := 4983230072969 + 3 ^ 40 * 5734352 * 2
def baseEnd_5734352 : Nat := 2944478818071053555128201

theorem tailTrace_5734352 : CollatzResearch.WordTrace tailWord_5734352 prefixEnd_5734352 2944478818071053555128201 := by
  unfold tailWord_5734352
  simp only [CollatzResearch.WordTrace]
  refine ⟨104574499860714764098362655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139432666480953018797816873 104574499860714764098362655)
  ·
    refine ⟨156861749791072146147543983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104574499860714764098362655 156861749791072146147543983)
    ·
      refine ⟨235292624686608219221315975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156861749791072146147543983 235292624686608219221315975)
      ·
        refine ⟨352938937029912328831973963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235292624686608219221315975 352938937029912328831973963)
        ·
          refine ⟨529408405544868493247960945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352938937029912328831973963 529408405544868493247960945)
          ·
            refine ⟨397056304158651369935970709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529408405544868493247960945 397056304158651369935970709)
            ·
              refine ⟨18612014257436782965748627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 397056304158651369935970709 18612014257436782965748627)
              ·
                refine ⟨27918021386155174448622941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18612014257436782965748627 27918021386155174448622941)
                ·
                  refine ⟨10469258019808190418233603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27918021386155174448622941 10469258019808190418233603)
                  ·
                    refine ⟨15703887029712285627350405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10469258019808190418233603 15703887029712285627350405)
                    ·
                      refine ⟨2944478818071053555128201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15703887029712285627350405 2944478818071053555128201)
                      ·
                        rfl

theorem cell23_5734352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 4].length) (baseStart_5734352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734352 prefixEnd_5734352 := by exact prefixLift 5734352
  have htrace : WordTrace (prefixWord ++ tailWord_5734352) baseStart_5734352 baseEnd_5734352 := by
    simpa [prefixWord, tailWord_5734352, baseEnd_5734352] using wordTrace_append hprefix tailTrace_5734352
  have hstable : (prefixWord ++ tailWord_5734352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734352).length < 2 ^ (prefixWord ++ tailWord_5734352).sum := by decide
  have hdescent : baseEnd_5734352 < baseStart_5734352 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734372 : List Nat := [2, 3, 1, 1, 1, 1, 4, 3, 1, 1, 5]
def baseStart_5734372 : Nat := 118140960795 + 5734372 * 2 ^ 59
def prefixEnd_5734372 : Nat := 4983230072969 + 3 ^ 40 * 5734372 * 2
def baseEnd_5734372 : Nat := 2944489087684143476878109

theorem tailTrace_5734372 : CollatzResearch.WordTrace tailWord_5734372 prefixEnd_5734372 2944489087684143476878109 := by
  unfold tailWord_5734372
  simp only [CollatzResearch.WordTrace]
  refine ⟨104574864590678535806226685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139433152787571381074968913 104574864590678535806226685)
  ·
    refine ⟨39215574221504450927335007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104574864590678535806226685 39215574221504450927335007)
    ·
      refine ⟨58823361332256676391002511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39215574221504450927335007 58823361332256676391002511)
      ·
        refine ⟨88235041998385014586503767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58823361332256676391002511 88235041998385014586503767)
        ·
          refine ⟨132352562997577521879755651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88235041998385014586503767 132352562997577521879755651)
          ·
            refine ⟨198528844496366282819633477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132352562997577521879755651 198528844496366282819633477)
            ·
              refine ⟨37224158343068678028681277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198528844496366282819633477 37224158343068678028681277)
              ·
                refine ⟨13959059378650754260755479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37224158343068678028681277 13959059378650754260755479)
                ·
                  refine ⟨20938589067976131391133219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13959059378650754260755479 20938589067976131391133219)
                  ·
                    refine ⟨31407883601964197086699829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20938589067976131391133219 31407883601964197086699829)
                    ·
                      refine ⟨2944489087684143476878109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31407883601964197086699829 2944489087684143476878109)
                      ·
                        rfl

theorem cell23_5734372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 3, 1, 1, 5].length) (baseStart_5734372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734372 prefixEnd_5734372 := by exact prefixLift 5734372
  have htrace : WordTrace (prefixWord ++ tailWord_5734372) baseStart_5734372 baseEnd_5734372 := by
    simpa [prefixWord, tailWord_5734372, baseEnd_5734372] using wordTrace_append hprefix tailTrace_5734372
  have hstable : (prefixWord ++ tailWord_5734372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734372).length < 2 ^ (prefixWord ++ tailWord_5734372).sum := by decide
  have hdescent : baseEnd_5734372 < baseStart_5734372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734396 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 2, 4]
def baseStart_5734396 : Nat := 118140960795 + 5734396 * 2 ^ 59
def prefixEnd_5734396 : Nat := 4983230072969 + 3 ^ 40 * 5734396 * 2
def baseEnd_5734396 : Nat := 981500470406617127659333

theorem tailTrace_5734396 : CollatzResearch.WordTrace tailWord_5734396 prefixEnd_5734396 981500470406617127659333 := by
  unfold tailWord_5734396
  simp only [CollatzResearch.WordTrace]
  refine ⟨104575302266635061855663521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139433736355513415807551361 104575302266635061855663521)
  ·
    refine ⟨78431476699976296391747641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104575302266635061855663521 78431476699976296391747641)
    ·
      refine ⟨58823607524982222293810731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78431476699976296391747641 58823607524982222293810731)
      ·
        refine ⟨88235411287473333440716097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58823607524982222293810731 88235411287473333440716097)
        ·
          refine ⟨66176558465605000080537073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88235411287473333440716097 66176558465605000080537073)
          ·
            refine ⟨49632418849203750060402805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66176558465605000080537073 49632418849203750060402805)
            ·
              refine ⟨4653039267112851568162763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49632418849203750060402805 4653039267112851568162763)
              ·
                refine ⟨6979558900669277352244145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4653039267112851568162763 6979558900669277352244145)
                ·
                  refine ⟨5234669175501958014183109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6979558900669277352244145 5234669175501958014183109)
                  ·
                    refine ⟨981500470406617127659333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5234669175501958014183109 981500470406617127659333)
                    ·
                      rfl

theorem cell23_5734396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_5734396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734396 prefixEnd_5734396 := by exact prefixLift 5734396
  have htrace : WordTrace (prefixWord ++ tailWord_5734396) baseStart_5734396 baseEnd_5734396 := by
    simpa [prefixWord, tailWord_5734396, baseEnd_5734396] using wordTrace_append hprefix tailTrace_5734396
  have hstable : (prefixWord ++ tailWord_5734396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734396).length < 2 ^ (prefixWord ++ tailWord_5734396).sum := by decide
  have hdescent : baseEnd_5734396 < baseStart_5734396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734419 : List Nat := [1, 1, 1, 2, 1, 4, 3, 2, 4, 1, 3]
def baseStart_5734419 : Nat := 118140960795 + 5734419 * 2 ^ 59
def prefixEnd_5734419 : Nat := 4983230072969 + 3 ^ 40 * 5734419 * 2
def baseEnd_5734419 : Nat := 2944513221274904792990393

theorem tailTrace_5734419 : CollatzResearch.WordTrace tailWord_5734419 prefixEnd_5734419 2944513221274904792990393 := by
  unfold tailWord_5734419
  simp only [CollatzResearch.WordTrace]
  refine ⟨209151443412186798639414311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139434295608124532426276207 209151443412186798639414311)
  ·
    refine ⟨313727165118280197959121467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209151443412186798639414311 313727165118280197959121467)
    ·
      refine ⟨470590747677420296938682201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313727165118280197959121467 470590747677420296938682201)
      ·
        refine ⟨352943060758065222704011651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470590747677420296938682201 352943060758065222704011651)
        ·
          refine ⟨529414591137097834056017477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352943060758065222704011651 529414591137097834056017477)
          ·
            refine ⟨99265235838205843885503277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 529414591137097834056017477 99265235838205843885503277)
            ·
              refine ⟨37224463439327191457063729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99265235838205843885503277 37224463439327191457063729)
              ·
                refine ⟨27918347579495393592797797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37224463439327191457063729 27918347579495393592797797)
                ·
                  refine ⟨5234690171155386298649587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27918347579495393592797797 5234690171155386298649587)
                  ·
                    refine ⟨7852035256733079447974381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5234690171155386298649587 7852035256733079447974381)
                    ·
                      refine ⟨2944513221274904792990393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7852035256733079447974381 2944513221274904792990393)
                      ·
                        rfl

theorem cell23_5734419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 1, 3].length) (baseStart_5734419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734419 prefixEnd_5734419 := by exact prefixLift 5734419
  have htrace : WordTrace (prefixWord ++ tailWord_5734419) baseStart_5734419 baseEnd_5734419 := by
    simpa [prefixWord, tailWord_5734419, baseEnd_5734419] using wordTrace_append hprefix tailTrace_5734419
  have hstable : (prefixWord ++ tailWord_5734419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734419).length < 2 ^ (prefixWord ++ tailWord_5734419).sum := by decide
  have hdescent : baseEnd_5734419 < baseStart_5734419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734453 : List Nat := [1, 3, 3, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_5734453 : Nat := 118140960795 + 5734453 * 2 ^ 59
def prefixEnd_5734453 : Nat := 4983230072969 + 3 ^ 40 * 5734453 * 2
def baseEnd_5734453 : Nat := 2944530679617157659965237

theorem tailTrace_5734453 : CollatzResearch.WordTrace tailWord_5734453 prefixEnd_5734453 2944530679617157659965237 := by
  unfold tailWord_5734453
  simp only [CollatzResearch.WordTrace]
  refine ⟨209152683494063622446152013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139435122329375748297434675 209152683494063622446152013)
  ·
    refine ⟨78432256310273858417307005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209152683494063622446152013 78432256310273858417307005)
    ·
      refine ⟨29412096116352696906490127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78432256310273858417307005 29412096116352696906490127)
      ·
        refine ⟨44118144174529045359735191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29412096116352696906490127 44118144174529045359735191)
        ·
          refine ⟨66177216261793568039602787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44118144174529045359735191 66177216261793568039602787)
          ·
            refine ⟨99265824392690352059404181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66177216261793568039602787 99265824392690352059404181)
            ·
              refine ⟨4653085518407360252784571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 99265824392690352059404181 4653085518407360252784571)
              ·
                refine ⟨6979628277611040379176857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4653085518407360252784571 6979628277611040379176857)
                ·
                  refine ⟨5234721208208280284382643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6979628277611040379176857 5234721208208280284382643)
                  ·
                    refine ⟨7852081812312420426573965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5234721208208280284382643 7852081812312420426573965)
                    ·
                      refine ⟨2944530679617157659965237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7852081812312420426573965 2944530679617157659965237)
                      ·
                        rfl

theorem cell23_5734453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_5734453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734453 prefixEnd_5734453 := by exact prefixLift 5734453
  have htrace : WordTrace (prefixWord ++ tailWord_5734453) baseStart_5734453 baseEnd_5734453 := by
    simpa [prefixWord, tailWord_5734453, baseEnd_5734453] using wordTrace_append hprefix tailTrace_5734453
  have hstable : (prefixWord ++ tailWord_5734453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734453).length < 2 ^ (prefixWord ++ tailWord_5734453).sum := by decide
  have hdescent : baseEnd_5734453 < baseStart_5734453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734472 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 3, 4, 4]
def baseStart_5734472 : Nat := 118140960795 + 5734472 * 2 ^ 59
def prefixEnd_5734472 : Nat := 4983230072969 + 3 ^ 40 * 5734472 * 2
def baseEnd_5734472 : Nat := 2944540435749593085627649

theorem tailTrace_5734472 : CollatzResearch.WordTrace tailWord_5734472 prefixEnd_5734472 2944540435749593085627649 := by
  unfold tailWord_5734472
  simp only [CollatzResearch.WordTrace]
  refine ⟨104576688240497394345546835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139435584320663192460729113 104576688240497394345546835)
  ·
    refine ⟨156865032360746091518320253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104576688240497394345546835 156865032360746091518320253)
    ·
      refine ⟨58824387135279784319370095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156865032360746091518320253 58824387135279784319370095)
      ·
        refine ⟨88236580702919676479055143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58824387135279784319370095 88236580702919676479055143)
        ·
          refine ⟨132354871054379514718582715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88236580702919676479055143 132354871054379514718582715)
          ·
            refine ⟨198532306581569272077874073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132354871054379514718582715 198532306581569272077874073)
            ·
              refine ⟨148899229936176954058405555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198532306581569272077874073 148899229936176954058405555)
              ·
                refine ⟨223348844904265431087608333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148899229936176954058405555 223348844904265431087608333)
                ·
                  refine ⟨83755816839099536657853125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 223348844904265431087608333 83755816839099536657853125)
                  ·
                    refine ⟨15704215657331163123347461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83755816839099536657853125 15704215657331163123347461)
                    ·
                      refine ⟨2944540435749593085627649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15704215657331163123347461 2944540435749593085627649)
                      ·
                        rfl

theorem cell23_5734472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_5734472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734472 prefixEnd_5734472 := by exact prefixLift 5734472
  have htrace : WordTrace (prefixWord ++ tailWord_5734472) baseStart_5734472 baseEnd_5734472 := by
    simpa [prefixWord, tailWord_5734472, baseEnd_5734472] using wordTrace_append hprefix tailTrace_5734472
  have hstable : (prefixWord ++ tailWord_5734472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734472).length < 2 ^ (prefixWord ++ tailWord_5734472).sum := by decide
  have hdescent : baseEnd_5734472 < baseStart_5734472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734476 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 6, 2, 2]
def baseStart_5734476 : Nat := 118140960795 + 5734476 * 2 ^ 59
def prefixEnd_5734476 : Nat := 4983230072969 + 3 ^ 40 * 5734476 * 2
def baseEnd_5734476 : Nat := 2944542489672211069977631

theorem tailTrace_5734476 : CollatzResearch.WordTrace tailWord_5734476 prefixEnd_5734476 2944542489672211069977631 := by
  unfold tailWord_5734476
  simp only [CollatzResearch.WordTrace]
  refine ⟨104576761186490148687119641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139435681581986864916159521 104576761186490148687119641)
  ·
    refine ⟨78432570889867611515339731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104576761186490148687119641 78432570889867611515339731)
    ·
      refine ⟨117648856334801417273009597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78432570889867611515339731 117648856334801417273009597)
      ·
        refine ⟨44118321125550531477378599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117648856334801417273009597 44118321125550531477378599)
        ·
          refine ⟨66177481688325797216067899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44118321125550531477378599 66177481688325797216067899)
          ·
            refine ⟨99266222532488695824101849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66177481688325797216067899 99266222532488695824101849)
            ·
              refine ⟨74449666899366521868076387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99266222532488695824101849 74449666899366521868076387)
              ·
                refine ⟨111674500349049782802114581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74449666899366521868076387 111674500349049782802114581)
                ·
                  refine ⟨5234742203861708568849121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111674500349049782802114581 5234742203861708568849121)
                  ·
                    refine ⟨3926056652896281426636841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5234742203861708568849121 3926056652896281426636841)
                    ·
                      refine ⟨2944542489672211069977631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926056652896281426636841 2944542489672211069977631)
                      ·
                        rfl

theorem cell23_5734476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_5734476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734476 prefixEnd_5734476 := by exact prefixLift 5734476
  have htrace : WordTrace (prefixWord ++ tailWord_5734476) baseStart_5734476 baseEnd_5734476 := by
    simpa [prefixWord, tailWord_5734476, baseEnd_5734476] using wordTrace_append hprefix tailTrace_5734476
  have hstable : (prefixWord ++ tailWord_5734476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734476).length < 2 ^ (prefixWord ++ tailWord_5734476).sum := by decide
  have hdescent : baseEnd_5734476 < baseStart_5734476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734506 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_5734506 : Nat := 118140960795 + 5734506 * 2 ^ 59
def prefixEnd_5734506 : Nat := 4983230072969 + 3 ^ 40 * 5734506 * 2
def baseEnd_5734506 : Nat := 2944557894091845952602493

theorem tailTrace_5734506 : CollatzResearch.WordTrace tailWord_5734506 prefixEnd_5734506 2944557894091845952602493 := by
  unfold tailWord_5734506
  simp only [CollatzResearch.WordTrace]
  refine ⟨52288654140717903124457843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139436411041914408331887581 52288654140717903124457843)
  ·
    refine ⟨78432981211076854686686765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52288654140717903124457843 78432981211076854686686765)
    ·
      refine ⟨29412367954153820507507537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78432981211076854686686765 29412367954153820507507537)
      ·
        refine ⟨22059275965615365380630653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29412367954153820507507537 22059275965615365380630653)
        ·
          refine ⟨8272228487105762017736495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22059275965615365380630653 8272228487105762017736495)
          ·
            refine ⟨12408342730658643026604743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8272228487105762017736495 12408342730658643026604743)
            ·
              refine ⟨18612514095987964539907115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12408342730658643026604743 18612514095987964539907115)
              ·
                refine ⟨27918771143981946809860673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18612514095987964539907115 27918771143981946809860673)
                ·
                  refine ⟨20939078357986460107395505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27918771143981946809860673 20939078357986460107395505)
                  ·
                    refine ⟨15704308768489845080546629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20939078357986460107395505 15704308768489845080546629)
                    ·
                      refine ⟨2944557894091845952602493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15704308768489845080546629 2944557894091845952602493)
                      ·
                        rfl

theorem cell23_5734506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_5734506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734506 prefixEnd_5734506 := by exact prefixLift 5734506
  have htrace : WordTrace (prefixWord ++ tailWord_5734506) baseStart_5734506 baseEnd_5734506 := by
    simpa [prefixWord, tailWord_5734506, baseEnd_5734506] using wordTrace_append hprefix tailTrace_5734506
  have hstable : (prefixWord ++ tailWord_5734506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734506).length < 2 ^ (prefixWord ++ tailWord_5734506).sum := by decide
  have hdescent : baseEnd_5734506 < baseStart_5734506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734522 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_5734522 : Nat := 118140960795 + 5734522 * 2 ^ 59
def prefixEnd_5734522 : Nat := 4983230072969 + 3 ^ 40 * 5734522 * 2
def baseEnd_5734522 : Nat := 2944566109782317890002419

theorem tailTrace_5734522 : CollatzResearch.WordTrace tailWord_5734522 prefixEnd_5734522 2944566109782317890002419 := by
  unfold tailWord_5734522
  simp only [CollatzResearch.WordTrace]
  refine ⟨52288800032703411807603455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139436800087209098153609213 52288800032703411807603455)
  ·
    refine ⟨78433200049055117711405183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52288800032703411807603455 78433200049055117711405183)
    ·
      refine ⟨117649800073582676567107775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78433200049055117711405183 117649800073582676567107775)
      ·
        refine ⟨176474700110374014850661663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117649800073582676567107775 176474700110374014850661663)
        ·
          refine ⟨264712050165561022275992495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176474700110374014850661663 264712050165561022275992495)
          ·
            refine ⟨397068075248341533413988743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264712050165561022275992495 397068075248341533413988743)
            ·
              refine ⟨595602112872512300120983115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397068075248341533413988743 595602112872512300120983115)
              ·
                refine ⟨893403169308768450181474673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595602112872512300120983115 893403169308768450181474673)
                ·
                  refine ⟨670052376981576337636106005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 893403169308768450181474673 670052376981576337636106005)
                  ·
                    refine ⟨31408705171011390826692469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 670052376981576337636106005 31408705171011390826692469)
                    ·
                      refine ⟨2944566109782317890002419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31408705171011390826692469 2944566109782317890002419)
                      ·
                        rfl

theorem cell23_5734522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_5734522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734522 prefixEnd_5734522 := by exact prefixLift 5734522
  have htrace : WordTrace (prefixWord ++ tailWord_5734522) baseStart_5734522 baseEnd_5734522 := by
    simpa [prefixWord, tailWord_5734522, baseEnd_5734522] using wordTrace_append hprefix tailTrace_5734522
  have hstable : (prefixWord ++ tailWord_5734522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734522).length < 2 ^ (prefixWord ++ tailWord_5734522).sum := by decide
  have hdescent : baseEnd_5734522 < baseStart_5734522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734549 : List Nat := [1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_5734549 : Nat := 118140960795 + 5734549 * 2 ^ 59
def prefixEnd_5734549 : Nat := 4983230072969 + 3 ^ 40 * 5734549 * 2
def baseEnd_5734549 : Nat := 2944579973759989284364795

theorem tailTrace_5734549 : CollatzResearch.WordTrace tailWord_5734549 prefixEnd_5734549 2944579973759989284364795 := by
  unfold tailWord_5734549
  simp only [CollatzResearch.WordTrace]
  refine ⟨209156184901715830841646701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139437456601143887227764467 209156184901715830841646701)
  ·
    refine ⟨78433569338143436565617513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209156184901715830841646701 78433569338143436565617513)
    ·
      refine ⟨58825177003607577424213135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78433569338143436565617513 58825177003607577424213135)
      ·
        refine ⟨88237765505411366136319703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58825177003607577424213135 88237765505411366136319703)
        ·
          refine ⟨132356648258117049204479555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88237765505411366136319703 132356648258117049204479555)
          ·
            refine ⟨198534972387175573806719333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132356648258117049204479555 198534972387175573806719333)
            ·
              refine ⟨37225307322595420088759875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198534972387175573806719333 37225307322595420088759875)
              ·
                refine ⟨55837960983893130133139813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37225307322595420088759875 55837960983893130133139813)
                ·
                  refine ⟨10469617684479961899963715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55837960983893130133139813 10469617684479961899963715)
                  ·
                    refine ⟨15704426526719942849945573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10469617684479961899963715 15704426526719942849945573)
                    ·
                      refine ⟨2944579973759989284364795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15704426526719942849945573 2944579973759989284364795)
                      ·
                        rfl

theorem cell23_5734549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_5734549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734549 prefixEnd_5734549 := by exact prefixLift 5734549
  have htrace : WordTrace (prefixWord ++ tailWord_5734549) baseStart_5734549 baseEnd_5734549 := by
    simpa [prefixWord, tailWord_5734549, baseEnd_5734549] using wordTrace_append hprefix tailTrace_5734549
  have hstable : (prefixWord ++ tailWord_5734549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734549).length < 2 ^ (prefixWord ++ tailWord_5734549).sum := by decide
  have hdescent : baseEnd_5734549 < baseStart_5734549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734643 : List Nat := [1, 1, 1, 2, 2, 4, 4, 1, 2, 3, 2]
def baseStart_5734643 : Nat := 118140960795 + 5734643 * 2 ^ 59
def prefixEnd_5734643 : Nat := 4983230072969 + 3 ^ 40 * 5734643 * 2
def baseEnd_5734643 : Nat := 2944628240941511916589363

theorem tailTrace_5734643 : CollatzResearch.WordTrace tailWord_5734643 prefixEnd_5734643 2944628240941511916589363 := by
  unfold tailWord_5734643
  simp only [CollatzResearch.WordTrace]
  refine ⟨209159613363375284895568583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139439742242250189930379055 209159613363375284895568583)
  ·
    refine ⟨313739420045062927343352875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209159613363375284895568583 313739420045062927343352875)
    ·
      refine ⟨470609130067594391015029313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313739420045062927343352875 470609130067594391015029313)
      ·
        refine ⟨352956847550695793261271985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470609130067594391015029313 352956847550695793261271985)
        ·
          refine ⟨264717635663021844945953989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352956847550695793261271985 264717635663021844945953989)
          ·
            refine ⟨49634556686816595927366373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 264717635663021844945953989 49634556686816595927366373)
            ·
              refine ⟨9306479378778111736381195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49634556686816595927366373 9306479378778111736381195)
              ·
                refine ⟨13959719068167167604571793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9306479378778111736381195 13959719068167167604571793)
                ·
                  refine ⟨10469789301125375703428845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13959719068167167604571793 10469789301125375703428845)
                  ·
                    refine ⟨3926170987922015888785817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10469789301125375703428845 3926170987922015888785817)
                    ·
                      refine ⟨2944628240941511916589363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926170987922015888785817 2944628240941511916589363)
                      ·
                        rfl

theorem cell23_5734643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 3, 2].length) (baseStart_5734643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734643 prefixEnd_5734643 := by exact prefixLift 5734643
  have htrace : WordTrace (prefixWord ++ tailWord_5734643) baseStart_5734643 baseEnd_5734643 := by
    simpa [prefixWord, tailWord_5734643, baseEnd_5734643] using wordTrace_append hprefix tailTrace_5734643
  have hstable : (prefixWord ++ tailWord_5734643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734643).length < 2 ^ (prefixWord ++ tailWord_5734643).sum := by decide
  have hdescent : baseEnd_5734643 < baseStart_5734643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734656 : List Nat := [2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 4]
def baseStart_5734656 : Nat := 118140960795 + 5734656 * 2 ^ 59
def prefixEnd_5734656 : Nat := 4983230072969 + 3 ^ 40 * 5734656 * 2
def baseEnd_5734656 : Nat := 2944634916190020365726803

theorem tailTrace_5734656 : CollatzResearch.WordTrace tailWord_5734656 prefixEnd_5734656 2944634916190020365726803 := by
  unfold tailWord_5734656
  simp only [CollatzResearch.WordTrace]
  refine ⟨104580043756164094057895911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139440058341552125410527881 104580043756164094057895911)
  ·
    refine ⟨156870065634246141086843867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104580043756164094057895911 156870065634246141086843867)
    ·
      refine ⟨235305098451369211630265801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156870065634246141086843867 235305098451369211630265801)
      ·
        refine ⟨176478823838526908722699351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235305098451369211630265801 176478823838526908722699351)
        ·
          refine ⟨264718235757790363084049027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176478823838526908722699351 264718235757790363084049027)
          ·
            refine ⟨397077353636685544626073541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264718235757790363084049027 397077353636685544626073541)
            ·
              refine ⟨74452003806878539617388789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 397077353636685544626073541 74452003806878539617388789)
              ·
                refine ⟨6979875356894863089130199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74452003806878539617388789 6979875356894863089130199)
                ·
                  refine ⟨10469813035342294633695299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6979875356894863089130199 10469813035342294633695299)
                  ·
                    refine ⟨15704719553013441950542949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10469813035342294633695299 15704719553013441950542949)
                    ·
                      refine ⟨2944634916190020365726803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15704719553013441950542949 2944634916190020365726803)
                      ·
                        rfl

theorem cell23_5734656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_5734656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734656 prefixEnd_5734656 := by exact prefixLift 5734656
  have htrace : WordTrace (prefixWord ++ tailWord_5734656) baseStart_5734656 baseEnd_5734656 := by
    simpa [prefixWord, tailWord_5734656, baseEnd_5734656] using wordTrace_append hprefix tailTrace_5734656
  have hstable : (prefixWord ++ tailWord_5734656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734656).length < 2 ^ (prefixWord ++ tailWord_5734656).sum := by decide
  have hdescent : baseEnd_5734656 < baseStart_5734656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734666 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 4, 4]
def baseStart_5734666 : Nat := 118140960795 + 5734666 * 2 ^ 59
def prefixEnd_5734666 : Nat := 4983230072969 + 3 ^ 40 * 5734666 * 2
def baseEnd_5734666 : Nat := 981546683665521775533919

theorem tailTrace_5734666 : CollatzResearch.WordTrace tailWord_5734666 prefixEnd_5734666 981546683665521775533919 := by
  unfold tailWord_5734666
  simp only [CollatzResearch.WordTrace]
  refine ⟨52290113060572989955913963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139440301494861306549103901 52290113060572989955913963)
  ·
    refine ⟨78435169590859484933870945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52290113060572989955913963 78435169590859484933870945)
    ·
      refine ⟨58826377193144613700403209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78435169590859484933870945 58826377193144613700403209)
      ·
        refine ⟨44119782894858460275302407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58826377193144613700403209 44119782894858460275302407)
        ·
          refine ⟨66179674342287690412953611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44119782894858460275302407 66179674342287690412953611)
          ·
            refine ⟨99269511513431535619430417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66179674342287690412953611 99269511513431535619430417)
            ·
              refine ⟨74452133635073651714572813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99269511513431535619430417 74452133635073651714572813)
              ·
                refine ⟨27919550113152619392964805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74452133635073651714572813 27919550113152619392964805)
                ·
                  refine ⟨5234915646216116136180901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27919550113152619392964805 5234915646216116136180901)
                  ·
                    refine ⟨981546683665521775533919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5234915646216116136180901 981546683665521775533919)
                    ·
                      rfl

theorem cell23_5734666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_5734666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734666 prefixEnd_5734666 := by exact prefixLift 5734666
  have htrace : WordTrace (prefixWord ++ tailWord_5734666) baseStart_5734666 baseEnd_5734666 := by
    simpa [prefixWord, tailWord_5734666, baseEnd_5734666] using wordTrace_append hprefix tailTrace_5734666
  have hstable : (prefixWord ++ tailWord_5734666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734666).length < 2 ^ (prefixWord ++ tailWord_5734666).sum := by decide
  have hdescent : baseEnd_5734666 < baseStart_5734666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734690 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_5734690 : Nat := 118140960795 + 5734690 * 2 ^ 59
def prefixEnd_5734690 : Nat := 4983230072969 + 3 ^ 40 * 5734690 * 2
def baseEnd_5734690 : Nat := 2944652374532273232701647

theorem tailTrace_5734690 : CollatzResearch.WordTrace tailWord_5734690 prefixEnd_5734690 2944652374532273232701647 := by
  unfold tailWord_5734690
  simp only [CollatzResearch.WordTrace]
  refine ⟨52290331898551252980632381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139440885062803341281686349 52290331898551252980632381)
  ·
    refine ⟨19608874461956719867737143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52290331898551252980632381 19608874461956719867737143)
    ·
      refine ⟨29413311692935079801605715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19608874461956719867737143 29413311692935079801605715)
      ·
        refine ⟨44119967539402619702408573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29413311692935079801605715 44119967539402619702408573)
        ·
          refine ⟨16544987827275982388403215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44119967539402619702408573 16544987827275982388403215)
          ·
            refine ⟨24817481740913973582604823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16544987827275982388403215 24817481740913973582604823)
            ·
              refine ⟨37226222611370960373907235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24817481740913973582604823 37226222611370960373907235)
              ·
                refine ⟨55839333917056440560860853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37226222611370960373907235 55839333917056440560860853)
                ·
                  refine ⟨5234937554724041302580705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55839333917056440560860853 5234937554724041302580705)
                  ·
                    refine ⟨3926203166043030976935529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5234937554724041302580705 3926203166043030976935529)
                    ·
                      refine ⟨2944652374532273232701647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926203166043030976935529 2944652374532273232701647)
                      ·
                        rfl

theorem cell23_5734690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_5734690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734690 prefixEnd_5734690 := by exact prefixLift 5734690
  have htrace : WordTrace (prefixWord ++ tailWord_5734690) baseStart_5734690 baseEnd_5734690 := by
    simpa [prefixWord, tailWord_5734690, baseEnd_5734690] using wordTrace_append hprefix tailTrace_5734690
  have hstable : (prefixWord ++ tailWord_5734690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734690).length < 2 ^ (prefixWord ++ tailWord_5734690).sum := by decide
  have hdescent : baseEnd_5734690 < baseStart_5734690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734707 : List Nat := [1, 1, 1, 2, 5, 1, 4, 3, 1, 2, 2]
def baseStart_5734707 : Nat := 118140960795 + 5734707 * 2 ^ 59
def prefixEnd_5734707 : Nat := 4983230072969 + 3 ^ 40 * 5734707 * 2
def baseEnd_5734707 : Nat := 2944661103703399666189069

theorem tailTrace_5734707 : CollatzResearch.WordTrace tailWord_5734707 prefixEnd_5734707 2944661103703399666189069 := by
  unfold tailWord_5734707
  simp only [CollatzResearch.WordTrace]
  refine ⟨209161947635143423825898375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139441298423428949217265583 209161947635143423825898375)
  ·
    refine ⟨313742921452715135738847563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209161947635143423825898375 313742921452715135738847563)
    ·
      refine ⟨470614382179072703608271345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313742921452715135738847563 470614382179072703608271345)
      ·
        refine ⟨352960786634304527706203509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470614382179072703608271345 352960786634304527706203509)
        ·
          refine ⟨33090073746966049472456579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 352960786634304527706203509 33090073746966049472456579)
          ·
            refine ⟨49635110620449074208684869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33090073746966049472456579 49635110620449074208684869)
            ·
              refine ⟨9306583241334201414128413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49635110620449074208684869 9306583241334201414128413)
              ·
                refine ⟨3489968715500325530298155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9306583241334201414128413 3489968715500325530298155)
                ·
                  refine ⟨5234953073250488295447233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3489968715500325530298155 5234953073250488295447233)
                  ·
                    refine ⟨3926214804937866221585425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5234953073250488295447233 3926214804937866221585425)
                    ·
                      refine ⟨2944661103703399666189069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926214804937866221585425 2944661103703399666189069)
                      ·
                        rfl

theorem cell23_5734707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 3, 1, 2, 2].length) (baseStart_5734707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734707 prefixEnd_5734707 := by exact prefixLift 5734707
  have htrace : WordTrace (prefixWord ++ tailWord_5734707) baseStart_5734707 baseEnd_5734707 := by
    simpa [prefixWord, tailWord_5734707, baseEnd_5734707] using wordTrace_append hprefix tailTrace_5734707
  have hstable : (prefixWord ++ tailWord_5734707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734707).length < 2 ^ (prefixWord ++ tailWord_5734707).sum := by decide
  have hdescent : baseEnd_5734707 < baseStart_5734707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734724 : List Nat := [2, 3, 4, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_5734724 : Nat := 118140960795 + 5734724 * 2 ^ 59
def prefixEnd_5734724 : Nat := 4983230072969 + 3 ^ 40 * 5734724 * 2
def baseEnd_5734724 : Nat := 2944669832874526099676491

theorem tailTrace_5734724 : CollatzResearch.WordTrace tailWord_5734724 prefixEnd_5734724 2944669832874526099676491 := by
  unfold tailWord_5734724
  simp only [CollatzResearch.WordTrace]
  refine ⟨104581283838040917864633613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139441711784054557152844817 104581283838040917864633613)
  ·
    refine ⟨39217981439265344199237605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104581283838040917864633613 39217981439265344199237605)
    ·
      refine ⟨7353371519862252037357051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39217981439265344199237605 7353371519862252037357051)
      ·
        refine ⟨11030057279793378056035577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7353371519862252037357051 11030057279793378056035577)
        ·
          refine ⟨8272542959845033542026683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11030057279793378056035577 8272542959845033542026683)
          ·
            refine ⟨12408814439767550313040025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8272542959845033542026683 12408814439767550313040025)
            ·
              refine ⟨9306610829825662734780019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12408814439767550313040025 9306610829825662734780019)
              ·
                refine ⟨13959916244738494102170029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9306610829825662734780019 13959916244738494102170029)
                ·
                  refine ⟨5234968591776935288313761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13959916244738494102170029 5234968591776935288313761)
                  ·
                    refine ⟨3926226443832701466235321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5234968591776935288313761 3926226443832701466235321)
                    ·
                      refine ⟨2944669832874526099676491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926226443832701466235321 2944669832874526099676491)
                      ·
                        rfl

theorem cell23_5734724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_5734724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734724 prefixEnd_5734724 := by exact prefixLift 5734724
  have htrace : WordTrace (prefixWord ++ tailWord_5734724) baseStart_5734724 baseEnd_5734724 := by
    simpa [prefixWord, tailWord_5734724, baseEnd_5734724] using wordTrace_append hprefix tailTrace_5734724
  have hstable : (prefixWord ++ tailWord_5734724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734724).length < 2 ^ (prefixWord ++ tailWord_5734724).sum := by decide
  have hdescent : baseEnd_5734724 < baseStart_5734724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734739 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 1, 8]
def baseStart_5734739 : Nat := 118140960795 + 5734739 * 2 ^ 59
def prefixEnd_5734739 : Nat := 4983230072969 + 3 ^ 40 * 5734739 * 2
def baseEnd_5734739 : Nat := 981559178361447846996307

theorem tailTrace_5734739 : CollatzResearch.WordTrace tailWord_5734739 prefixEnd_5734739 981559178361447846996307 := by
  unfold tailWord_5734739
  simp only [CollatzResearch.WordTrace]
  refine ⟨209163114771027493291063271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139442076514018328860708847 209163114771027493291063271)
  ·
    refine ⟨313744672156541239936594907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209163114771027493291063271 313744672156541239936594907)
    ·
      refine ⟨470617008234811859904892361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313744672156541239936594907 470617008234811859904892361)
      ·
        refine ⟨352962756176108894928669271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470617008234811859904892361 352962756176108894928669271)
        ·
          refine ⟨529444134264163342393003907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352962756176108894928669271 529444134264163342393003907)
          ·
            refine ⟨794166201396245013589505861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529444134264163342393003907 794166201396245013589505861)
            ·
              refine ⟨148906162761795940048032349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 794166201396245013589505861 148906162761795940048032349)
              ·
                refine ⟨55839811035673477518012131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148906162761795940048032349 55839811035673477518012131)
                ·
                  refine ⟨83759716553510216277018197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55839811035673477518012131 83759716553510216277018197)
                  ·
                    refine ⟨981559178361447846996307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83759716553510216277018197 981559178361447846996307)
                    ·
                      rfl

theorem cell23_5734739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 8].length) (baseStart_5734739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734739 prefixEnd_5734739 := by exact prefixLift 5734739
  have htrace : WordTrace (prefixWord ++ tailWord_5734739) baseStart_5734739 baseEnd_5734739 := by
    simpa [prefixWord, tailWord_5734739, baseEnd_5734739] using wordTrace_append hprefix tailTrace_5734739
  have hstable : (prefixWord ++ tailWord_5734739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734739).length < 2 ^ (prefixWord ++ tailWord_5734739).sum := by decide
  have hdescent : baseEnd_5734739 < baseStart_5734739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734740 : List Nat := [2, 4, 1, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_5734740 : Nat := 118140960795 + 5734740 * 2 ^ 59
def prefixEnd_5734740 : Nat := 4983230072969 + 3 ^ 40 * 5734740 * 2
def baseEnd_5734740 : Nat := 2944678048564998037076417

theorem tailTrace_5734740 : CollatzResearch.WordTrace tailWord_5734740 prefixEnd_5734740 2944678048564998037076417 := by
  unfold tailWord_5734740
  simp only [CollatzResearch.WordTrace]
  refine ⟨104581575622011935230924837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139442100829349246974566449 104581575622011935230924837)
  ·
    refine ⟨19609045429127237855798407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104581575622011935230924837 19609045429127237855798407)
    ·
      refine ⟨29413568143690856783697611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19609045429127237855798407 29413568143690856783697611)
      ·
        refine ⟨44120352215536285175546417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29413568143690856783697611 44120352215536285175546417)
        ·
          refine ⟨33090264161652213881659813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44120352215536285175546417 33090264161652213881659813)
          ·
            refine ⟨6204424530309790102811215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33090264161652213881659813 6204424530309790102811215)
            ·
              refine ⟨9306636795464685154216823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6204424530309790102811215 9306636795464685154216823)
              ·
                refine ⟨13959955193197027731325235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9306636795464685154216823 13959955193197027731325235)
                ·
                  refine ⟨20939932789795541596987853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13959955193197027731325235 20939932789795541596987853)
                  ·
                    refine ⟨7852474796173328098870445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20939932789795541596987853 7852474796173328098870445)
                    ·
                      refine ⟨2944678048564998037076417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7852474796173328098870445 2944678048564998037076417)
                      ·
                        rfl

theorem cell23_5734740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_5734740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734740 prefixEnd_5734740 := by exact prefixLift 5734740
  have htrace : WordTrace (prefixWord ++ tailWord_5734740) baseStart_5734740 baseEnd_5734740 := by
    simpa [prefixWord, tailWord_5734740, baseEnd_5734740] using wordTrace_append hprefix tailTrace_5734740
  have hstable : (prefixWord ++ tailWord_5734740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734740).length < 2 ^ (prefixWord ++ tailWord_5734740).sum := by decide
  have hdescent : baseEnd_5734740 < baseStart_5734740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734833 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 2, 5]
def baseStart_5734833 : Nat := 118140960795 + 5734833 * 2 ^ 59
def prefixEnd_5734833 : Nat := 4983230072969 + 3 ^ 40 * 5734833 * 2
def baseEnd_5734833 : Nat := 981575267421955391071163

theorem tailTrace_5734833 : CollatzResearch.WordTrace tailWord_5734833 prefixEnd_5734833 981575267421955391071163 := by
  unfold tailWord_5734833
  simp only [CollatzResearch.WordTrace]
  refine ⟨209166543232686947344985153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139444362155124631563323435 209166543232686947344985153)
  ·
    refine ⟨156874907424515210508738865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209166543232686947344985153 156874907424515210508738865)
    ·
      refine ⟨117656180568386407881554149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156874907424515210508738865 117656180568386407881554149)
      ·
        refine ⟨22060533856572451477791403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117656180568386407881554149 22060533856572451477791403)
        ·
          refine ⟨33090800784858677216687105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22060533856572451477791403 33090800784858677216687105)
          ·
            refine ⟨24818100588644007912515329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33090800784858677216687105 24818100588644007912515329)
            ·
              refine ⟨18613575441483005934386497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24818100588644007912515329 18613575441483005934386497)
              ·
                refine ⟨13960181581112254450789873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18613575441483005934386497 13960181581112254450789873)
                ·
                  refine ⟨10470136185834190838092405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13960181581112254450789873 10470136185834190838092405)
                  ·
                    refine ⟨981575267421955391071163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10470136185834190838092405 981575267421955391071163)
                    ·
                      rfl

theorem cell23_5734833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_5734833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734833 prefixEnd_5734833 := by exact prefixLift 5734833
  have htrace : WordTrace (prefixWord ++ tailWord_5734833) baseStart_5734833 baseEnd_5734833 := by
    simpa [prefixWord, tailWord_5734833, baseEnd_5734833] using wordTrace_append hprefix tailTrace_5734833
  have hstable : (prefixWord ++ tailWord_5734833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734833).length < 2 ^ (prefixWord ++ tailWord_5734833).sum := by decide
  have hdescent : baseEnd_5734833 < baseStart_5734833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734870 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_5734870 : Nat := 118140960795 + 5734870 * 2 ^ 59
def prefixEnd_5734870 : Nat := 4983230072969 + 3 ^ 40 * 5734870 * 2
def baseEnd_5734870 : Nat := 2944744801050082528450819

theorem tailTrace_5734870 : CollatzResearch.WordTrace tailWord_5734870 prefixEnd_5734870 2944744801050082528450819 := by
  unfold tailWord_5734870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13072993295847056416505129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139445261822368601776054709 13072993295847056416505129)
  ·
    refine ⟨9804744971885292312378847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13072993295847056416505129 9804744971885292312378847)
    ·
      refine ⟨14707117457827938468568271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9804744971885292312378847 14707117457827938468568271)
      ·
        refine ⟨22060676186741907702852407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14707117457827938468568271 22060676186741907702852407)
        ·
          refine ⟨33091014280112861554278611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22060676186741907702852407 33091014280112861554278611)
          ·
            refine ⟨49636521420169292331417917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33091014280112861554278611 49636521420169292331417917)
            ·
              refine ⟨18613695532563484624281719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49636521420169292331417917 18613695532563484624281719)
              ·
                refine ⟨27920543298845226936422579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18613695532563484624281719 27920543298845226936422579)
                ·
                  refine ⟨41880814948267840404633869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27920543298845226936422579 41880814948267840404633869)
                  ·
                    refine ⟨15705305605600440151737701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41880814948267840404633869 15705305605600440151737701)
                    ·
                      refine ⟨2944744801050082528450819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15705305605600440151737701 2944744801050082528450819)
                      ·
                        rfl

theorem cell23_5734870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_5734870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734870 prefixEnd_5734870 := by exact prefixLift 5734870
  have htrace : WordTrace (prefixWord ++ tailWord_5734870) baseStart_5734870 baseEnd_5734870 := by
    simpa [prefixWord, tailWord_5734870, baseEnd_5734870] using wordTrace_append hprefix tailTrace_5734870
  have hstable : (prefixWord ++ tailWord_5734870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734870).length < 2 ^ (prefixWord ++ tailWord_5734870).sum := by decide
  have hdescent : baseEnd_5734870 < baseStart_5734870 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734873 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 1, 4, 3]
def baseStart_5734873 : Nat := 118140960795 + 5734873 * 2 ^ 59
def prefixEnd_5734873 : Nat := 4983230072969 + 3 ^ 40 * 5734873 * 2
def baseEnd_5734873 : Nat := 2944746341492046016713305

theorem tailTrace_5734873 : CollatzResearch.WordTrace tailWord_5734873 prefixEnd_5734873 2944746341492046016713305 := by
  unfold tailWord_5734873
  simp only [CollatzResearch.WordTrace]
  refine ⟨209168002152542034176441273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139445334768361356117627515 209168002152542034176441273)
  ·
    refine ⟨156876001614406525632330955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209168002152542034176441273 156876001614406525632330955)
    ·
      refine ⟨235314002421609788448496433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156876001614406525632330955 235314002421609788448496433)
      ·
        refine ⟨176485501816207341336372325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235314002421609788448496433 176485501816207341336372325)
        ·
          refine ⟨33091031590538876500569811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176485501816207341336372325 33091031590538876500569811)
          ·
            refine ⟨49636547385808314750854717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33091031590538876500569811 49636547385808314750854717)
            ·
              refine ⟨18613705269678118031570519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49636547385808314750854717 18613705269678118031570519)
              ·
                refine ⟨27920557904517177047355779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18613705269678118031570519 27920557904517177047355779)
                ·
                  refine ⟨41880836856775765571033669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27920557904517177047355779 41880836856775765571033669)
                  ·
                    refine ⟨7852656910645456044568813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41880836856775765571033669 7852656910645456044568813)
                    ·
                      refine ⟨2944746341492046016713305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7852656910645456044568813 2944746341492046016713305)
                      ·
                        rfl

theorem cell23_5734873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_5734873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734873 prefixEnd_5734873 := by exact prefixLift 5734873
  have htrace : WordTrace (prefixWord ++ tailWord_5734873) baseStart_5734873 baseEnd_5734873 := by
    simpa [prefixWord, tailWord_5734873, baseEnd_5734873] using wordTrace_append hprefix tailTrace_5734873
  have hstable : (prefixWord ++ tailWord_5734873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734873).length < 2 ^ (prefixWord ++ tailWord_5734873).sum := by decide
  have hdescent : baseEnd_5734873 < baseStart_5734873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734896 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 8]
def baseStart_5734896 : Nat := 118140960795 + 5734896 * 2 ^ 59
def prefixEnd_5734896 : Nat := 4983230072969 + 3 ^ 40 * 5734896 * 2
def baseEnd_5734896 : Nat := 2944758151547099426725699

theorem tailTrace_5734896 : CollatzResearch.WordTrace tailWord_5734896 prefixEnd_5734896 2944758151547099426725699 := by
  unfold tailWord_5734896
  simp only [CollatzResearch.WordTrace]
  refine ⟨104584420515729354552264271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139445894020972472736352361 104584420515729354552264271)
  ·
    refine ⟨156876630773594031828396407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104584420515729354552264271 156876630773594031828396407)
    ·
      refine ⟨235314946160391047742594611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156876630773594031828396407 235314946160391047742594611)
      ·
        refine ⟨352972419240586571613891917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235314946160391047742594611 352972419240586571613891917)
        ·
          refine ⟨132364657215219964355209469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352972419240586571613891917 132364657215219964355209469)
          ·
            refine ⟨49636746455707486633203551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132364657215219964355209469 49636746455707486633203551)
            ·
              refine ⟨74455119683561229949805327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49636746455707486633203551 74455119683561229949805327)
              ·
                refine ⟨111682679525341844924707991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74455119683561229949805327 111682679525341844924707991)
                ·
                  refine ⟨167524019288012767387061987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111682679525341844924707991 167524019288012767387061987)
                  ·
                    refine ⟨251286028932019151080592981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 167524019288012767387061987 251286028932019151080592981)
                    ·
                      refine ⟨2944758151547099426725699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 251286028932019151080592981 2944758151547099426725699)
                      ·
                        rfl

theorem cell23_5734896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 8].length) (baseStart_5734896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734896 prefixEnd_5734896 := by exact prefixLift 5734896
  have htrace : WordTrace (prefixWord ++ tailWord_5734896) baseStart_5734896 baseEnd_5734896 := by
    simpa [prefixWord, tailWord_5734896, baseEnd_5734896] using wordTrace_append hprefix tailTrace_5734896
  have hstable : (prefixWord ++ tailWord_5734896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734896).length < 2 ^ (prefixWord ++ tailWord_5734896).sum := by decide
  have hdescent : baseEnd_5734896 < baseStart_5734896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734906 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_5734906 : Nat := 118140960795 + 5734906 * 2 ^ 59
def prefixEnd_5734906 : Nat := 4983230072969 + 3 ^ 40 * 5734906 * 2
def baseEnd_5734906 : Nat := 981587762117881462533551

theorem tailTrace_5734906 : CollatzResearch.WordTrace tailWord_5734906 prefixEnd_5734906 981587762117881462533551 := by
  unfold tailWord_5734906
  simp only [CollatzResearch.WordTrace]
  refine ⟨52292301440355620203098143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139446137174281653874928381 52292301440355620203098143)
  ·
    refine ⟨78438452160533430304647215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52292301440355620203098143 78438452160533430304647215)
    ·
      refine ⟨117657678240800145456970823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78438452160533430304647215 117657678240800145456970823)
      ·
        refine ⟨176486517361200218185456235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117657678240800145456970823 176486517361200218185456235)
        ·
          refine ⟨264729776041800327278184353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176486517361200218185456235 264729776041800327278184353)
          ·
            refine ⟨198547332031350245458638265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264729776041800327278184353 198547332031350245458638265)
            ·
              refine ⟨148910499023512684093978699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198547332031350245458638265 148910499023512684093978699)
              ·
                refine ⟨223365748535269026140968049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148910499023512684093978699 223365748535269026140968049)
                ·
                  refine ⟨167524311401451769605726037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 223365748535269026140968049 167524311401451769605726037)
                  ·
                    refine ⟨981587762117881462533551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 167524311401451769605726037 981587762117881462533551)
                    ·
                      rfl

theorem cell23_5734906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_5734906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734906 prefixEnd_5734906 := by exact prefixLift 5734906
  have htrace : WordTrace (prefixWord ++ tailWord_5734906) baseStart_5734906 baseEnd_5734906 := by
    simpa [prefixWord, tailWord_5734906, baseEnd_5734906] using wordTrace_append hprefix tailTrace_5734906
  have hstable : (prefixWord ++ tailWord_5734906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734906).length < 2 ^ (prefixWord ++ tailWord_5734906).sum := by decide
  have hdescent : baseEnd_5734906 < baseStart_5734906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734940 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 1, 5]
def baseStart_5734940 : Nat := 118140960795 + 5734940 * 2 ^ 59
def prefixEnd_5734940 : Nat := 4983230072969 + 3 ^ 40 * 5734940 * 2
def baseEnd_5734940 : Nat := 981593581565299084858499

theorem tailTrace_5734940 : CollatzResearch.WordTrace tailWord_5734940 prefixEnd_5734940 981593581565299084858499 := by
  unfold tailWord_5734940
  simp only [CollatzResearch.WordTrace]
  refine ⟨104585222921649652309565137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139446963895532869746086849 104585222921649652309565137)
  ·
    refine ⟨78438917191237239232173853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104585222921649652309565137 78438917191237239232173853)
    ·
      refine ⟨29414593946713964712065195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78438917191237239232173853 29414593946713964712065195)
      ·
        refine ⟨44121890920070947068097793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29414593946713964712065195 44121890920070947068097793)
        ·
          refine ⟨33091418190053210301073345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44121890920070947068097793 33091418190053210301073345)
          ·
            refine ⟨24818563642539907725805009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33091418190053210301073345 24818563642539907725805009)
            ·
              refine ⟨18613922731904930794353757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24818563642539907725805009 18613922731904930794353757)
              ·
                refine ⟨6980221024464349047882659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18613922731904930794353757 6980221024464349047882659)
                ·
                  refine ⟨10470331536696523571823989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6980221024464349047882659 10470331536696523571823989)
                  ·
                    refine ⟨981593581565299084858499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10470331536696523571823989 981593581565299084858499)
                    ·
                      rfl

theorem cell23_5734940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_5734940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734940 prefixEnd_5734940 := by exact prefixLift 5734940
  have htrace : WordTrace (prefixWord ++ tailWord_5734940) baseStart_5734940 baseEnd_5734940 := by
    simpa [prefixWord, tailWord_5734940, baseEnd_5734940] using wordTrace_append hprefix tailTrace_5734940
  have hstable : (prefixWord ++ tailWord_5734940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734940).length < 2 ^ (prefixWord ++ tailWord_5734940).sum := by decide
  have hdescent : baseEnd_5734940 < baseStart_5734940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734943 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 4]
def baseStart_5734943 : Nat := 118140960795 + 5734943 * 2 ^ 59
def prefixEnd_5734943 : Nat := 4983230072969 + 3 ^ 40 * 5734943 * 2
def baseEnd_5734943 : Nat := 2944782285137860742837983

theorem tailTrace_5734943 : CollatzResearch.WordTrace tailWord_5734943 prefixEnd_5734943 2944782285137860742837983 := by
  unfold tailWord_5734943
  simp only [CollatzResearch.WordTrace]
  refine ⟨209170555262288436131489483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139447036841525624087659655 209170555262288436131489483)
  ·
    refine ⟨313755832893432654197234225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209170555262288436131489483 313755832893432654197234225)
    ·
      refine ⟨235316874670074490647925669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313755832893432654197234225 235316874670074490647925669)
      ·
        refine ⟨44121914000638966996486063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 235316874670074490647925669 44121914000638966996486063)
        ·
          refine ⟨66182871000958450494729095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44121914000638966996486063 66182871000958450494729095)
          ·
            refine ⟨99274306501437675742093643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66182871000958450494729095 99274306501437675742093643)
            ·
              refine ⟨148911459752156513613140465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99274306501437675742093643 148911459752156513613140465)
              ·
                refine ⟨111683594814117385209855349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148911459752156513613140465 111683594814117385209855349)
                ·
                  refine ⟨10470337013823504863423939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111683594814117385209855349 10470337013823504863423939)
                  ·
                    refine ⟨15705505520735257295135909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10470337013823504863423939 15705505520735257295135909)
                    ·
                      refine ⟨2944782285137860742837983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15705505520735257295135909 2944782285137860742837983)
                      ·
                        rfl

theorem cell23_5734943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_5734943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734943 prefixEnd_5734943 := by exact prefixLift 5734943
  have htrace : WordTrace (prefixWord ++ tailWord_5734943) baseStart_5734943 baseEnd_5734943 := by
    simpa [prefixWord, tailWord_5734943, baseEnd_5734943] using wordTrace_append hprefix tailTrace_5734943
  have hstable : (prefixWord ++ tailWord_5734943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734943).length < 2 ^ (prefixWord ++ tailWord_5734943).sum := by decide
  have hdescent : baseEnd_5734943 < baseStart_5734943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734947 : List Nat := [1, 1, 1, 4, 4, 2, 1, 2, 2, 3, 2]
def baseStart_5734947 : Nat := 118140960795 + 5734947 * 2 ^ 59
def prefixEnd_5734947 : Nat := 4983230072969 + 3 ^ 40 * 5734947 * 2
def baseEnd_5734947 : Nat := 2944784339060478727187965

theorem tailTrace_5734947 : CollatzResearch.WordTrace tailWord_5734947 prefixEnd_5734947 2944784339060478727187965 := by
  unfold tailWord_5734947
  simp only [CollatzResearch.WordTrace]
  refine ⟨209170701154273944814635095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139447134102849296543090063 209170701154273944814635095)
  ·
    refine ⟨313756051731410917221952643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209170701154273944814635095 313756051731410917221952643)
    ·
      refine ⟨470634077597116375832928965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313756051731410917221952643 470634077597116375832928965)
      ·
        refine ⟨88243889549459320468674181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 470634077597116375832928965 88243889549459320468674181)
        ·
          refine ⟨16545729290523622587876409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88243889549459320468674181 16545729290523622587876409)
          ·
            refine ⟨12409296967892716940907307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16545729290523622587876409 12409296967892716940907307)
            ·
              refine ⟨18613945451839075411360961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12409296967892716940907307 18613945451839075411360961)
              ·
                refine ⟨13960459088879306558520721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18613945451839075411360961 13960459088879306558520721)
                ·
                  refine ⟨10470344316659479918890541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13960459088879306558520721 10470344316659479918890541)
                  ·
                    refine ⟨3926379118747304969583953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10470344316659479918890541 3926379118747304969583953)
                    ·
                      refine ⟨2944784339060478727187965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926379118747304969583953 2944784339060478727187965)
                      ·
                        rfl

theorem cell23_5734947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 2, 2, 3, 2].length) (baseStart_5734947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734947 prefixEnd_5734947 := by exact prefixLift 5734947
  have htrace : WordTrace (prefixWord ++ tailWord_5734947) baseStart_5734947 baseEnd_5734947 := by
    simpa [prefixWord, tailWord_5734947, baseEnd_5734947] using wordTrace_append hprefix tailTrace_5734947
  have hstable : (prefixWord ++ tailWord_5734947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734947).length < 2 ^ (prefixWord ++ tailWord_5734947).sum := by decide
  have hdescent : baseEnd_5734947 < baseStart_5734947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734954 : List Nat := [3, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_5734954 : Nat := 118140960795 + 5734954 * 2 ^ 59
def prefixEnd_5734954 : Nat := 4983230072969 + 3 ^ 40 * 5734954 * 2
def baseEnd_5734954 : Nat := 2944787933425060199800433

theorem tailTrace_5734954 : CollatzResearch.WordTrace tailWord_5734954 prefixEnd_5734954 2944787933425060199800433 := by
  unfold tailWord_5734954
  simp only [CollatzResearch.WordTrace]
  refine ⟨52292739116312146252534979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139447304310165723340093277 52292739116312146252534979)
  ·
    refine ⟨78439108674468219378802469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52292739116312146252534979 78439108674468219378802469)
    ·
      refine ⟨14707332876462791133525463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78439108674468219378802469 14707332876462791133525463)
      ·
        refine ⟨22060999314694186700288195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14707332876462791133525463 22060999314694186700288195)
        ·
          refine ⟨33091498972041280050432293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22060999314694186700288195 33091498972041280050432293)
          ·
            refine ⟨6204656057257740009456055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33091498972041280050432293 6204656057257740009456055)
            ·
              refine ⟨9306984085886610014184083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6204656057257740009456055 9306984085886610014184083)
              ·
                refine ⟨13960476128829915021276125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9306984085886610014184083 13960476128829915021276125)
                ·
                  refine ⟨5235178548311218132978547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13960476128829915021276125 5235178548311218132978547)
                  ·
                    refine ⟨7852767822466827199467821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5235178548311218132978547 7852767822466827199467821)
                    ·
                      refine ⟨2944787933425060199800433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7852767822466827199467821 2944787933425060199800433)
                      ·
                        rfl

theorem cell23_5734954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_5734954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734954 prefixEnd_5734954 := by exact prefixLift 5734954
  have htrace : WordTrace (prefixWord ++ tailWord_5734954) baseStart_5734954 baseEnd_5734954 := by
    simpa [prefixWord, tailWord_5734954, baseEnd_5734954] using wordTrace_append hprefix tailTrace_5734954
  have hstable : (prefixWord ++ tailWord_5734954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734954).length < 2 ^ (prefixWord ++ tailWord_5734954).sum := by decide
  have hdescent : baseEnd_5734954 < baseStart_5734954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734963 : List Nat := [1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 5]
def baseStart_5734963 : Nat := 118140960795 + 5734963 * 2 ^ 59
def prefixEnd_5734963 : Nat := 4983230072969 + 3 ^ 40 * 5734963 * 2
def baseEnd_5734963 : Nat := 2944792554750950664587891

theorem tailTrace_5734963 : CollatzResearch.WordTrace tailWord_5734963 prefixEnd_5734963 2944792554750950664587891 := by
  unfold tailWord_5734963
  simp only [CollatzResearch.WordTrace]
  refine ⟨209171284722215979547217543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139447523148143986364811695 209171284722215979547217543)
  ·
    refine ⟨313756927083323969320826315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209171284722215979547217543 313756927083323969320826315)
    ·
      refine ⟨470635390624985953981239473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313756927083323969320826315 470635390624985953981239473)
      ·
        refine ⟨352976542968739465485929605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470635390624985953981239473 352976542968739465485929605)
        ·
          refine ⟨66183101806638649778611801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 352976542968739465485929605 66183101806638649778611801)
          ·
            refine ⟨49637326354978987333958851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66183101806638649778611801 49637326354978987333958851)
            ·
              refine ⟨74455989532468481000938277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49637326354978987333958851 74455989532468481000938277)
              ·
                refine ⟨13960498037337840187675927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74455989532468481000938277 13960498037337840187675927)
                ·
                  refine ⟨20940747056006760281513891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13960498037337840187675927 20940747056006760281513891)
                  ·
                    refine ⟨31411120584010140422270837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20940747056006760281513891 31411120584010140422270837)
                    ·
                      refine ⟨2944792554750950664587891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31411120584010140422270837 2944792554750950664587891)
                      ·
                        rfl

theorem cell23_5734963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_5734963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734963 prefixEnd_5734963 := by exact prefixLift 5734963
  have htrace : WordTrace (prefixWord ++ tailWord_5734963) baseStart_5734963 baseEnd_5734963 := by
    simpa [prefixWord, tailWord_5734963, baseEnd_5734963] using wordTrace_append hprefix tailTrace_5734963
  have hstable : (prefixWord ++ tailWord_5734963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734963).length < 2 ^ (prefixWord ++ tailWord_5734963).sum := by decide
  have hdescent : baseEnd_5734963 < baseStart_5734963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734977 : List Nat := [1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_5734977 : Nat := 118140960795 + 5734977 * 2 ^ 59
def prefixEnd_5734977 : Nat := 4983230072969 + 3 ^ 40 * 5734977 * 2
def baseEnd_5734977 : Nat := 2944799743480113609812827

theorem tailTrace_5734977 : CollatzResearch.WordTrace tailWord_5734977 prefixEnd_5734977 2944799743480113609812827 := by
  unfold tailWord_5734977
  simp only [CollatzResearch.WordTrace]
  refine ⟨209171795344165259938227185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139447863562776839958818123 209171795344165259938227185)
  ·
    refine ⟨156878846508123944953670389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209171795344165259938227185 156878846508123944953670389)
    ·
      refine ⟨14707391860136619839406599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156878846508123944953670389 14707391860136619839406599)
      ·
        refine ⟨22061087790204929759109899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14707391860136619839406599 22061087790204929759109899)
        ·
          refine ⟨33091631685307394638664849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22061087790204929759109899 33091631685307394638664849)
          ·
            refine ⟨24818723763980545978998637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33091631685307394638664849 24818723763980545978998637)
            ·
              refine ⟨9307021411492704742124489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24818723763980545978998637 9307021411492704742124489)
              ·
                refine ⟨6980266058619528556593367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9307021411492704742124489 6980266058619528556593367)
                ·
                  refine ⟨10470399087929292834890051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6980266058619528556593367 10470399087929292834890051)
                  ·
                    refine ⟨15705598631893939252335077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10470399087929292834890051 15705598631893939252335077)
                    ·
                      refine ⟨2944799743480113609812827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15705598631893939252335077 2944799743480113609812827)
                      ·
                        rfl

theorem cell23_5734977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_5734977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734977 prefixEnd_5734977 := by exact prefixLift 5734977
  have htrace : WordTrace (prefixWord ++ tailWord_5734977) baseStart_5734977 baseEnd_5734977 := by
    simpa [prefixWord, tailWord_5734977, baseEnd_5734977] using wordTrace_append hprefix tailTrace_5734977
  have hstable : (prefixWord ++ tailWord_5734977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734977).length < 2 ^ (prefixWord ++ tailWord_5734977).sum := by decide
  have hdescent : baseEnd_5734977 < baseStart_5734977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5734983 : List Nat := [1, 1, 4, 1, 4, 1, 2, 9]
def baseStart_5734983 : Nat := 118140960795 + 5734983 * 2 ^ 59
def prefixEnd_5734983 : Nat := 4983230072969 + 3 ^ 40 * 5734983 * 2
def baseEnd_5734983 : Nat := 109066771272742243938437

theorem tailTrace_5734983 : CollatzResearch.WordTrace tailWord_5734983 prefixEnd_5734983 109066771272742243938437 := by
  unfold tailWord_5734983
  simp only [CollatzResearch.WordTrace]
  refine ⟨209172014182143522962945603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139448009454762348641963735 209172014182143522962945603)
  ·
    refine ⟨313758021273215284444418405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209172014182143522962945603 313758021273215284444418405)
    ·
      refine ⟨58829628988727865833328451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313758021273215284444418405 58829628988727865833328451)
      ·
        refine ⟨88244443483091798749992677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58829628988727865833328451 88244443483091798749992677)
        ·
          refine ⟨16545833153079712265623627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88244443483091798749992677 16545833153079712265623627)
          ·
            refine ⟨24818749729619568398435441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16545833153079712265623627 24818749729619568398435441)
            ·
              refine ⟨18614062297214676298826581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24818749729619568398435441 18614062297214676298826581)
              ·
                refine ⟨109066771272742243938437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18614062297214676298826581 109066771272742243938437)
                ·
                  rfl

theorem cell23_5734983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 9].length) (baseStart_5734983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5734983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5734983 prefixEnd_5734983 := by exact prefixLift 5734983
  have htrace : WordTrace (prefixWord ++ tailWord_5734983) baseStart_5734983 baseEnd_5734983 := by
    simpa [prefixWord, tailWord_5734983, baseEnd_5734983] using wordTrace_append hprefix tailTrace_5734983
  have hstable : (prefixWord ++ tailWord_5734983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5734983).length < 2 ^ (prefixWord ++ tailWord_5734983).sum := by decide
  have hdescent : baseEnd_5734983 < baseStart_5734983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5734983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735004 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 2, 4]
def baseStart_5735004 : Nat := 118140960795 + 5735004 * 2 ^ 59
def prefixEnd_5735004 : Nat := 4983230072969 + 3 ^ 40 * 5735004 * 2
def baseEnd_5735004 : Nat := 981604535819261668058401

theorem tailTrace_5735004 : CollatzResearch.WordTrace tailWord_5735004 prefixEnd_5735004 981604535819261668058401 := by
  unfold tailWord_5735004
  simp only [CollatzResearch.WordTrace]
  refine ⟨104586390057533721774730033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139448520076711629032973377 104586390057533721774730033)
  ·
    refine ⟨78439792543150291331047525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104586390057533721774730033 78439792543150291331047525)
    ·
      refine ⟨14707461101840679624571411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78439792543150291331047525 14707461101840679624571411)
      ·
        refine ⟨22061191652761019436857117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14707461101840679624571411 22061191652761019436857117)
        ·
          refine ⟨8272946869785382288821419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22061191652761019436857117 8272946869785382288821419)
          ·
            refine ⟨12409420304678073433232129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8272946869785382288821419 12409420304678073433232129)
            ·
              refine ⟨9307065228508555074924097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12409420304678073433232129 9307065228508555074924097)
              ·
                refine ⟨6980298921381416306193073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9307065228508555074924097 6980298921381416306193073)
                ·
                  refine ⟨5235224191036062229644805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6980298921381416306193073 5235224191036062229644805)
                  ·
                    refine ⟨981604535819261668058401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5235224191036062229644805 981604535819261668058401)
                    ·
                      rfl

theorem cell23_5735004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_5735004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735004 prefixEnd_5735004 := by exact prefixLift 5735004
  have htrace : WordTrace (prefixWord ++ tailWord_5735004) baseStart_5735004 baseEnd_5735004 := by
    simpa [prefixWord, tailWord_5735004, baseEnd_5735004] using wordTrace_append hprefix tailTrace_5735004
  have hstable : (prefixWord ++ tailWord_5735004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735004).length < 2 ^ (prefixWord ++ tailWord_5735004).sum := by decide
  have hdescent : baseEnd_5735004 < baseStart_5735004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735054 : List Nat := [4, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2]
def baseStart_5735054 : Nat := 118140960795 + 5735054 * 2 ^ 59
def prefixEnd_5735054 : Nat := 4983230072969 + 3 ^ 40 * 5735054 * 2
def baseEnd_5735054 : Nat := 2944839281490509808549973

theorem tailTrace_5735054 : CollatzResearch.WordTrace tailWord_5735054 prefixEnd_5735054 2944839281490509808549973 := by
  unfold tailWord_5735054
  simp only [CollatzResearch.WordTrace]
  refine ⟨26146825470610787761097527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139449735843257534725853477 26146825470610787761097527)
  ·
    refine ⟨39220238205916181641646291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26146825470610787761097527 39220238205916181641646291)
    ·
      refine ⟨58830357308874272462469437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39220238205916181641646291 58830357308874272462469437)
      ·
        refine ⟨22061383990827852173426039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58830357308874272462469437 22061383990827852173426039)
        ·
          refine ⟨33092075986241778260139059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22061383990827852173426039 33092075986241778260139059)
          ·
            refine ⟨49638113979362667390208589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33092075986241778260139059 49638113979362667390208589)
            ·
              refine ⟨18614292742261000271328221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49638113979362667390208589 18614292742261000271328221)
              ·
                refine ⟨6980359778347875101748083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18614292742261000271328221 6980359778347875101748083)
                ·
                  refine ⟨10470539667521812652622125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6980359778347875101748083 10470539667521812652622125)
                  ·
                    refine ⟨3926452375320679744733297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10470539667521812652622125 3926452375320679744733297)
                    ·
                      refine ⟨2944839281490509808549973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926452375320679744733297 2944839281490509808549973)
                      ·
                        rfl

theorem cell23_5735054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_5735054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735054 prefixEnd_5735054 := by exact prefixLift 5735054
  have htrace : WordTrace (prefixWord ++ tailWord_5735054) baseStart_5735054 baseEnd_5735054 := by
    simpa [prefixWord, tailWord_5735054, baseEnd_5735054] using wordTrace_append hprefix tailTrace_5735054
  have hstable : (prefixWord ++ tailWord_5735054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735054).length < 2 ^ (prefixWord ++ tailWord_5735054).sum := by decide
  have hdescent : baseEnd_5735054 < baseStart_5735054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735113 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_5735113 : Nat := 118140960795 + 5735113 * 2 ^ 59
def prefixEnd_5735113 : Nat := 4983230072969 + 3 ^ 40 * 5735113 * 2
def baseEnd_5735113 : Nat := 2944869576849125077712201

theorem tailTrace_5735113 : CollatzResearch.WordTrace tailWord_5735113 prefixEnd_5735113 2944869576849125077712201 := by
  unfold tailWord_5735113
  simp only [CollatzResearch.WordTrace]
  refine ⟨209176755671672555165177993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139451170447781703443451995 209176755671672555165177993)
  ·
    refine ⟨156882566753754416373883495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209176755671672555165177993 156882566753754416373883495)
    ·
      refine ⟨235323850130631624560825243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156882566753754416373883495 235323850130631624560825243)
      ·
        refine ⟨352985775195947436841237865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235323850130631624560825243 352985775195947436841237865)
        ·
          refine ⟨264739331396960577630928399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352985775195947436841237865 264739331396960577630928399)
          ·
            refine ⟨397108997095440866446392599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264739331396960577630928399 397108997095440866446392599)
            ·
              refine ⟨595663495643161299669588899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397108997095440866446392599 595663495643161299669588899)
              ·
                refine ⟨893495243464741949504383349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595663495643161299669588899 893495243464741949504383349)
                ·
                  refine ⟨83765179074819557766035939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 893495243464741949504383349 83765179074819557766035939)
                  ·
                    refine ⟨125647768612229336649053909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83765179074819557766035939 125647768612229336649053909)
                    ·
                      refine ⟨2944869576849125077712201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125647768612229336649053909 2944869576849125077712201)
                      ·
                        rfl

theorem cell23_5735113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_5735113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735113 prefixEnd_5735113 := by exact prefixLift 5735113
  have htrace : WordTrace (prefixWord ++ tailWord_5735113) baseStart_5735113 baseEnd_5735113 := by
    simpa [prefixWord, tailWord_5735113, baseEnd_5735113] using wordTrace_append hprefix tailTrace_5735113
  have hstable : (prefixWord ++ tailWord_5735113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735113).length < 2 ^ (prefixWord ++ tailWord_5735113).sum := by decide
  have hdescent : baseEnd_5735113 < baseStart_5735113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735124 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 7]
def baseStart_5735124 : Nat := 118140960795 + 5735124 * 2 ^ 59
def prefixEnd_5735124 : Nat := 4983230072969 + 3 ^ 40 * 5735124 * 2
def baseEnd_5735124 : Nat := 327208358348480503852739

theorem tailTrace_5735124 : CollatzResearch.WordTrace tailWord_5735124 prefixEnd_5735124 327208358348480503852739 := by
  unfold tailWord_5735124
  simp only [CollatzResearch.WordTrace]
  refine ⟨104588578437316352021914213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139451437916421802695885617 104588578437316352021914213)
  ·
    refine ⟨19610358456996816004108915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104588578437316352021914213 19610358456996816004108915)
    ·
      refine ⟨29415537685495224006163373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19610358456996816004108915 29415537685495224006163373)
      ·
        refine ⟨11030826632060709002311265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29415537685495224006163373 11030826632060709002311265)
        ·
          refine ⟨8273119974045531751733449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11030826632060709002311265 8273119974045531751733449)
          ·
            refine ⟨6204839980534148813800087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8273119974045531751733449 6204839980534148813800087)
            ·
              refine ⟨9307259970801223220700131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6204839980534148813800087 9307259970801223220700131)
              ·
                refine ⟨13960889956201834831050197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9307259970801223220700131 13960889956201834831050197)
                ·
                  refine ⟨327208358348480503852739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13960889956201834831050197 327208358348480503852739)
                  ·
                    rfl

theorem cell23_5735124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_5735124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735124 prefixEnd_5735124 := by exact prefixLift 5735124
  have htrace : WordTrace (prefixWord ++ tailWord_5735124) baseStart_5735124 baseEnd_5735124 := by
    simpa [prefixWord, tailWord_5735124, baseEnd_5735124] using wordTrace_append hprefix tailTrace_5735124
  have hstable : (prefixWord ++ tailWord_5735124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735124).length < 2 ^ (prefixWord ++ tailWord_5735124).sum := by decide
  have hdescent : baseEnd_5735124 < baseStart_5735124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735130 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_5735130 : Nat := 118140960795 + 5735130 * 2 ^ 59
def prefixEnd_5735130 : Nat := 4983230072969 + 3 ^ 40 * 5735130 * 2
def baseEnd_5735130 : Nat := 2944878306020251511199623

theorem tailTrace_5735130 : CollatzResearch.WordTrace tailWord_5735130 prefixEnd_5735130 2944878306020251511199623 := by
  unfold tailWord_5735130
  simp only [CollatzResearch.WordTrace]
  refine ⟨52294343928152741767136711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139451583808407311379031229 52294343928152741767136711)
  ·
    refine ⟨78441515892229112650705067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52294343928152741767136711 78441515892229112650705067)
    ·
      refine ⟨117662273838343668976057601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78441515892229112650705067 117662273838343668976057601)
      ·
        refine ⟨88246705378757751732043201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117662273838343668976057601 88246705378757751732043201)
        ·
          refine ⟨66185029034068313799032401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88246705378757751732043201 66185029034068313799032401)
          ·
            refine ⟨49638771775551235349274301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66185029034068313799032401 49638771775551235349274301)
            ·
              refine ⟨18614539415831713255977863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49638771775551235349274301 18614539415831713255977863)
              ·
                refine ⟨27921809123747569883966795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18614539415831713255977863 27921809123747569883966795)
                ·
                  refine ⟨41882713685621354825950193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27921809123747569883966795 41882713685621354825950193)
                  ·
                    refine ⟨31412035264216016119462645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41882713685621354825950193 31412035264216016119462645)
                    ·
                      refine ⟨2944878306020251511199623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31412035264216016119462645 2944878306020251511199623)
                      ·
                        rfl

theorem cell23_5735130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_5735130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735130 prefixEnd_5735130 := by exact prefixLift 5735130
  have htrace : WordTrace (prefixWord ++ tailWord_5735130) baseStart_5735130 baseEnd_5735130 := by
    simpa [prefixWord, tailWord_5735130, baseEnd_5735130] using wordTrace_append hprefix tailTrace_5735130
  have hstable : (prefixWord ++ tailWord_5735130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735130).length < 2 ^ (prefixWord ++ tailWord_5735130).sum := by decide
  have hdescent : baseEnd_5735130 < baseStart_5735130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735177 : List Nat := [1, 2, 1, 1, 3, 2, 4, 2, 2, 2, 3]
def baseStart_5735177 : Nat := 118140960795 + 5735177 * 2 ^ 59
def prefixEnd_5735177 : Nat := 4983230072969 + 3 ^ 40 * 5735177 * 2
def baseEnd_5735177 : Nat := 2944902439611012827311907

theorem tailTrace_5735177 : CollatzResearch.WordTrace tailWord_5735177 prefixEnd_5735177 2944902439611012827311907 := by
  unfold tailWord_5735177
  simp only [CollatzResearch.WordTrace]
  refine ⟨209179089943440694095507785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139452726628960462730338523 209179089943440694095507785)
  ·
    refine ⟨156884317457580520571630839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209179089943440694095507785 156884317457580520571630839)
    ·
      refine ⟨235326476186370780857446259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156884317457580520571630839 235326476186370780857446259)
      ·
        refine ⟨352989714279556171286169389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235326476186370780857446259 352989714279556171286169389)
        ·
          refine ⟨132371142854833564232313521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352989714279556171286169389 132371142854833564232313521)
          ·
            refine ⟨99278357141125173174235141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132371142854833564232313521 99278357141125173174235141)
            ·
              refine ⟨18614691963960969970169089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99278357141125173174235141 18614691963960969970169089)
              ·
                refine ⟨13961018972970727477626817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18614691963960969970169089 13961018972970727477626817)
                ·
                  refine ⟨10470764229728045608220113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13961018972970727477626817 10470764229728045608220113)
                  ·
                    refine ⟨7853073172296034206165085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10470764229728045608220113 7853073172296034206165085)
                    ·
                      refine ⟨2944902439611012827311907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7853073172296034206165085 2944902439611012827311907)
                      ·
                        rfl

theorem cell23_5735177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2, 3].length) (baseStart_5735177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735177 prefixEnd_5735177 := by exact prefixLift 5735177
  have htrace : WordTrace (prefixWord ++ tailWord_5735177) baseStart_5735177 baseEnd_5735177 := by
    simpa [prefixWord, tailWord_5735177, baseEnd_5735177] using wordTrace_append hprefix tailTrace_5735177
  have hstable : (prefixWord ++ tailWord_5735177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735177).length < 2 ^ (prefixWord ++ tailWord_5735177).sum := by decide
  have hdescent : baseEnd_5735177 < baseStart_5735177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735241 : List Nat := [1, 2, 1, 1, 2, 5, 2, 4, 1, 1, 3]
def baseStart_5735241 : Nat := 118140960795 + 5735241 * 2 ^ 59
def prefixEnd_5735241 : Nat := 4983230072969 + 3 ^ 40 * 5735241 * 2
def baseEnd_5735241 : Nat := 2944935302372900576911613

theorem tailTrace_5735241 : CollatzResearch.WordTrace tailWord_5735241 prefixEnd_5735241 2944935302372900576911613 := by
  unfold tailWord_5735241
  simp only [CollatzResearch.WordTrace]
  refine ⟨209181424215208833025837577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139454282810139222017225051 209181424215208833025837577)
  ·
    refine ⟨156886068161406624769378183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209181424215208833025837577 156886068161406624769378183)
    ·
      refine ⟨235329102242109937154067275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156886068161406624769378183 235329102242109937154067275)
      ·
        refine ⟨352993653363164905731100913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235329102242109937154067275 352993653363164905731100913)
        ·
          refine ⟨264745240022373679298325685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352993653363164905731100913 264745240022373679298325685)
          ·
            refine ⟨24819866252097532434218033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 264745240022373679298325685 24819866252097532434218033)
            ·
              refine ⟨18614899689073149325663525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24819866252097532434218033 18614899689073149325663525)
              ·
                refine ⟨3490293691701215498561911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18614899689073149325663525 3490293691701215498561911)
                ·
                  refine ⟨5235440537551823247842867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3490293691701215498561911 5235440537551823247842867)
                  ·
                    refine ⟨7853160806327734871764301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5235440537551823247842867 7853160806327734871764301)
                    ·
                      refine ⟨2944935302372900576911613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7853160806327734871764301 2944935302372900576911613)
                      ·
                        rfl

theorem cell23_5735241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 4, 1, 1, 3].length) (baseStart_5735241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735241 prefixEnd_5735241 := by exact prefixLift 5735241
  have htrace : WordTrace (prefixWord ++ tailWord_5735241) baseStart_5735241 baseEnd_5735241 := by
    simpa [prefixWord, tailWord_5735241, baseEnd_5735241] using wordTrace_append hprefix tailTrace_5735241
  have hstable : (prefixWord ++ tailWord_5735241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735241).length < 2 ^ (prefixWord ++ tailWord_5735241).sum := by decide
  have hdescent : baseEnd_5735241 < baseStart_5735241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735257 : List Nat := [1, 2, 1, 2, 2, 4, 3, 1, 1, 6]
def baseStart_5735257 : Nat := 118140960795 + 5735257 * 2 ^ 59
def prefixEnd_5735257 : Nat := 4983230072969 + 3 ^ 40 * 5735257 * 2
def baseEnd_5735257 : Nat := 981647839354457504770513

theorem tailTrace_5735257 : CollatzResearch.WordTrace tailWord_5735257 prefixEnd_5735257 981647839354457504770513 := by
  unfold tailWord_5735257
  simp only [CollatzResearch.WordTrace]
  refine ⟨209182007783150867758420025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139454671855433911838946683 209182007783150867758420025)
  ·
    refine ⟨156886505837363150818815019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209182007783150867758420025 156886505837363150818815019)
    ·
      refine ⟨235329758756044726228222529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156886505837363150818815019 235329758756044726228222529)
      ·
        refine ⟨176497319067033544671166897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235329758756044726228222529 176497319067033544671166897)
        ·
          refine ⟨132372989300275158503375173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176497319067033544671166897 132372989300275158503375173)
          ·
            refine ⟨24819935493801592219382845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132372989300275158503375173 24819935493801592219382845)
            ·
              refine ⟨9307475810175597082268567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24819935493801592219382845 9307475810175597082268567)
              ·
                refine ⟨13961213715263395623402851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9307475810175597082268567 13961213715263395623402851)
                ·
                  refine ⟨20941820572895093435104277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13961213715263395623402851 20941820572895093435104277)
                  ·
                    refine ⟨981647839354457504770513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20941820572895093435104277 981647839354457504770513)
                    ·
                      rfl

theorem cell23_5735257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 6].length) (baseStart_5735257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735257 prefixEnd_5735257 := by exact prefixLift 5735257
  have htrace : WordTrace (prefixWord ++ tailWord_5735257) baseStart_5735257 baseEnd_5735257 := by
    simpa [prefixWord, tailWord_5735257, baseEnd_5735257] using wordTrace_append hprefix tailTrace_5735257
  have hstable : (prefixWord ++ tailWord_5735257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735257).length < 2 ^ (prefixWord ++ tailWord_5735257).sum := by decide
  have hdescent : baseEnd_5735257 < baseStart_5735257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735264 : List Nat := [2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 4]
def baseStart_5735264 : Nat := 118140960795 + 5735264 * 2 ^ 59
def prefixEnd_5735264 : Nat := 4983230072969 + 3 ^ 40 * 5735264 * 2
def baseEnd_5735264 : Nat := 2944947112427953986924007

theorem tailTrace_5735264 : CollatzResearch.WordTrace tailWord_5735264 prefixEnd_5735264 2944947112427953986924007 := by
  unfold tailWord_5735264
  simp only [CollatzResearch.WordTrace]
  refine ⟨104591131547062753976962423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139454842062750338635949897 104591131547062753976962423)
  ·
    refine ⟨156886697320594130965443635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104591131547062753976962423 156886697320594130965443635)
    ·
      refine ⟨235330045980891196448165453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156886697320594130965443635 235330045980891196448165453)
      ·
        refine ⟨88248767242834198668062045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235330045980891196448165453 88248767242834198668062045)
        ·
          refine ⟨33093287716062824500523267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88248767242834198668062045 33093287716062824500523267)
          ·
            refine ⟨49639931574094236750784901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33093287716062824500523267 49639931574094236750784901)
            ·
              refine ⟨9307487170142669390772169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49639931574094236750784901 9307487170142669390772169)
              ·
                refine ⟨6980615377607002043079127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9307487170142669390772169 6980615377607002043079127)
                ·
                  refine ⟨10470923066410503064618691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6980615377607002043079127 10470923066410503064618691)
                  ·
                    refine ⟨15706384599615754596928037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10470923066410503064618691 15706384599615754596928037)
                    ·
                      refine ⟨2944947112427953986924007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15706384599615754596928037 2944947112427953986924007)
                      ·
                        rfl

theorem cell23_5735264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_5735264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735264 prefixEnd_5735264 := by exact prefixLift 5735264
  have htrace : WordTrace (prefixWord ++ tailWord_5735264) baseStart_5735264 baseEnd_5735264 := by
    simpa [prefixWord, tailWord_5735264, baseEnd_5735264] using wordTrace_append hprefix tailTrace_5735264
  have hstable : (prefixWord ++ tailWord_5735264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735264).length < 2 ^ (prefixWord ++ tailWord_5735264).sum := by decide
  have hdescent : baseEnd_5735264 < baseStart_5735264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735277 : List Nat := [1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_5735277 : Nat := 118140960795 + 5735277 * 2 ^ 59
def prefixEnd_5735277 : Nat := 4983230072969 + 3 ^ 40 * 5735277 * 2
def baseEnd_5735277 : Nat := 2944953787676462436061447

theorem tailTrace_5735277 : CollatzResearch.WordTrace tailWord_5735277 prefixEnd_5735277 2944953787676462436061447 := by
  unfold tailWord_5735277
  simp only [CollatzResearch.WordTrace]
  refine ⟨209182737243078411174148085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139455158162052274116098723 209182737243078411174148085)
  ·
    refine ⟨19610881616538601047576383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209182737243078411174148085 19610881616538601047576383)
    ·
      refine ⟨29416322424807901571364575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19610881616538601047576383 29416322424807901571364575)
      ·
        refine ⟨44124483637211852357046863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29416322424807901571364575 44124483637211852357046863)
        ·
          refine ⟨66186725455817778535570295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44124483637211852357046863 66186725455817778535570295)
          ·
            refine ⟨99280088183726667803355443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66186725455817778535570295 99280088183726667803355443)
            ·
              refine ⟨148920132275590001705033165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99280088183726667803355443 148920132275590001705033165)
              ·
                refine ⟨55845049603346250639387437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148920132275590001705033165 55845049603346250639387437)
                ·
                  refine ⟨20941893601254843989770289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55845049603346250639387437 20941893601254843989770289)
                  ·
                    refine ⟨15706420200941132992327717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20941893601254843989770289 15706420200941132992327717)
                    ·
                      refine ⟨2944953787676462436061447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15706420200941132992327717 2944953787676462436061447)
                      ·
                        rfl

theorem cell23_5735277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_5735277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735277 prefixEnd_5735277 := by exact prefixLift 5735277
  have htrace : WordTrace (prefixWord ++ tailWord_5735277) baseStart_5735277 baseEnd_5735277 := by
    simpa [prefixWord, tailWord_5735277, baseEnd_5735277] using wordTrace_append hprefix tailTrace_5735277
  have hstable : (prefixWord ++ tailWord_5735277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735277).length < 2 ^ (prefixWord ++ tailWord_5735277).sum := by decide
  have hdescent : baseEnd_5735277 < baseStart_5735277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735354 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2]
def baseStart_5735354 : Nat := 118140960795 + 5735354 * 2 ^ 59
def prefixEnd_5735354 : Nat := 4983230072969 + 3 ^ 40 * 5735354 * 2
def baseEnd_5735354 : Nat := 2944993325686858634798593

theorem tailTrace_5735354 : CollatzResearch.WordTrace tailWord_5735354 prefixEnd_5735354 2944993325686858634798593 := by
  unfold tailWord_5735354
  simp only [CollatzResearch.WordTrace]
  refine ⟨52296386415949863331175279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139457030442532968883134077 52296386415949863331175279)
  ·
    refine ⟨78444579623924794996762919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52296386415949863331175279 78444579623924794996762919)
    ·
      refine ⟨117666869435887192495144379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78444579623924794996762919 117666869435887192495144379)
      ·
        refine ⟨176500304153830788742716569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117666869435887192495144379 176500304153830788742716569)
        ·
          refine ⟨132375228115373091557037427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176500304153830788742716569 132375228115373091557037427)
          ·
            refine ⟨198562842173059637335556141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132375228115373091557037427 198562842173059637335556141)
            ·
              refine ⟨74461065814897364000833553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198562842173059637335556141 74461065814897364000833553)
              ·
                refine ⟨55845799361173023000625165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74461065814897364000833553 55845799361173023000625165)
                ·
                  refine ⟨20942174760439883625234437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55845799361173023000625165 20942174760439883625234437)
                  ·
                    refine ⟨3926657767582478179731457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20942174760439883625234437 3926657767582478179731457)
                    ·
                      refine ⟨2944993325686858634798593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926657767582478179731457 2944993325686858634798593)
                      ·
                        rfl

theorem cell23_5735354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2].length) (baseStart_5735354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735354 prefixEnd_5735354 := by exact prefixLift 5735354
  have htrace : WordTrace (prefixWord ++ tailWord_5735354) baseStart_5735354 baseEnd_5735354 := by
    simpa [prefixWord, tailWord_5735354, baseEnd_5735354] using wordTrace_append hprefix tailTrace_5735354
  have hstable : (prefixWord ++ tailWord_5735354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735354).length < 2 ^ (prefixWord ++ tailWord_5735354).sum := by decide
  have hdescent : baseEnd_5735354 < baseStart_5735354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735367 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_5735367 : Nat := 118140960795 + 5735367 * 2 ^ 59
def prefixEnd_5735367 : Nat := 4983230072969 + 3 ^ 40 * 5735367 * 2
def baseEnd_5735367 : Nat := 2945000000935367083936033

theorem tailTrace_5735367 : CollatzResearch.WordTrace tailWord_5735367 prefixEnd_5735367 2945000000935367083936033 := by
  unfold tailWord_5735367
  simp only [CollatzResearch.WordTrace]
  refine ⟨209186019812752356544924355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139457346541834904363282903 209186019812752356544924355)
  ·
    refine ⟨313779029719128534817386533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209186019812752356544924355 313779029719128534817386533)
    ·
      refine ⟨58833568072336600278259975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313779029719128534817386533 58833568072336600278259975)
      ·
        refine ⟨88250352108504900417389963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58833568072336600278259975 88250352108504900417389963)
        ·
          refine ⟨132375528162757350626084945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88250352108504900417389963 132375528162757350626084945)
          ·
            refine ⟨99281646122068012969563709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132375528162757350626084945 99281646122068012969563709)
            ·
              refine ⟨37230617295775504863586391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 99281646122068012969563709 37230617295775504863586391)
              ·
                refine ⟨55845925943663257295379587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37230617295775504863586391 55845925943663257295379587)
                ·
                  refine ⟨83768888915494885943069381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55845925943663257295379587 83768888915494885943069381)
                  ·
                    refine ⟨15706666671655291114325509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83768888915494885943069381 15706666671655291114325509)
                    ·
                      refine ⟨2945000000935367083936033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15706666671655291114325509 2945000000935367083936033)
                      ·
                        rfl

theorem cell23_5735367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_5735367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735367 prefixEnd_5735367 := by exact prefixLift 5735367
  have htrace : WordTrace (prefixWord ++ tailWord_5735367) baseStart_5735367 baseEnd_5735367 := by
    simpa [prefixWord, tailWord_5735367, baseEnd_5735367] using wordTrace_append hprefix tailTrace_5735367
  have hstable : (prefixWord ++ tailWord_5735367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735367).length < 2 ^ (prefixWord ++ tailWord_5735367).sum := by decide
  have hdescent : baseEnd_5735367 < baseStart_5735367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735371 : List Nat := [1, 1, 1, 1, 3, 6, 2, 1, 1, 4, 2]
def baseStart_5735371 : Nat := 118140960795 + 5735371 * 2 ^ 59
def prefixEnd_5735371 : Nat := 4983230072969 + 3 ^ 40 * 5735371 * 2
def baseEnd_5735371 : Nat := 2945002054857985068286015

theorem tailTrace_5735371 : CollatzResearch.WordTrace tailWord_5735371 prefixEnd_5735371 2945002054857985068286015 := by
  unfold tailWord_5735371
  simp only [CollatzResearch.WordTrace]
  refine ⟨209186165704737865228069967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139457443803158576818713311 209186165704737865228069967)
  ·
    refine ⟨313779248557106797842104951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209186165704737865228069967 313779248557106797842104951)
    ·
      refine ⟨470668872835660196763157427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313779248557106797842104951 470668872835660196763157427)
      ·
        refine ⟨706003309253490295144736141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470668872835660196763157427 706003309253490295144736141)
        ·
          refine ⟨264751240970058860679276053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 706003309253490295144736141 264751240970058860679276053)
          ·
            refine ⟨12410214420471509094341065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 264751240970058860679276053 12410214420471509094341065)
            ·
              refine ⟨9307660815353631820755799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12410214420471509094341065 9307660815353631820755799)
              ·
                refine ⟨13961491223030447731133699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9307660815353631820755799 13961491223030447731133699)
                ·
                  refine ⟨20942236834545671596700549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13961491223030447731133699 20942236834545671596700549)
                  ·
                    refine ⟨3926669406477313424381353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20942236834545671596700549 3926669406477313424381353)
                    ·
                      refine ⟨2945002054857985068286015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926669406477313424381353 2945002054857985068286015)
                      ·
                        rfl

theorem cell23_5735371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 4, 2].length) (baseStart_5735371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735371 prefixEnd_5735371 := by exact prefixLift 5735371
  have htrace : WordTrace (prefixWord ++ tailWord_5735371) baseStart_5735371 baseEnd_5735371 := by
    simpa [prefixWord, tailWord_5735371, baseEnd_5735371] using wordTrace_append hprefix tailTrace_5735371
  have hstable : (prefixWord ++ tailWord_5735371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735371).length < 2 ^ (prefixWord ++ tailWord_5735371).sum := by decide
  have hdescent : baseEnd_5735371 < baseStart_5735371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735377 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 7]
def baseStart_5735377 : Nat := 118140960795 + 5735377 * 2 ^ 59
def prefixEnd_5735377 : Nat := 4983230072969 + 3 ^ 40 * 5735377 * 2
def baseEnd_5735377 : Nat := 327222792860212449423443

theorem tailTrace_5735377 : CollatzResearch.WordTrace tailWord_5735377 prefixEnd_5735377 327222792860212449423443 := by
  unfold tailWord_5735377
  simp only [CollatzResearch.WordTrace]
  refine ⟨209186384542716128252788385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139457589695144085501858923 209186384542716128252788385)
  ·
    refine ⟨156889788407037096189591289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209186384542716128252788385 156889788407037096189591289)
    ·
      refine ⟨117667341305277822142193467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156889788407037096189591289 117667341305277822142193467)
      ·
        refine ⟨176501011957916733213290201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117667341305277822142193467 176501011957916733213290201)
        ·
          refine ⟨132375758968437549909967651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176501011957916733213290201 132375758968437549909967651)
          ·
            refine ⟨198563638452656324864951477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132375758968437549909967651 198563638452656324864951477)
            ·
              refine ⟨18615341104936530456089201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 198563638452656324864951477 18615341104936530456089201)
              ·
                refine ⟨13961505828702397842066901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18615341104936530456089201 13961505828702397842066901)
                ·
                  refine ⟨327222792860212449423443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13961505828702397842066901 327222792860212449423443)
                  ·
                    rfl

theorem cell23_5735377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 7].length) (baseStart_5735377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735377 prefixEnd_5735377 := by exact prefixLift 5735377
  have htrace : WordTrace (prefixWord ++ tailWord_5735377) baseStart_5735377 baseEnd_5735377 := by
    simpa [prefixWord, tailWord_5735377, baseEnd_5735377] using wordTrace_append hprefix tailTrace_5735377
  have hstable : (prefixWord ++ tailWord_5735377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735377).length < 2 ^ (prefixWord ++ tailWord_5735377).sum := by decide
  have hdescent : baseEnd_5735377 < baseStart_5735377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735417 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_5735417 : Nat := 118140960795 + 5735417 * 2 ^ 59
def prefixEnd_5735417 : Nat := 4983230072969 + 3 ^ 40 * 5735417 * 2
def baseEnd_5735417 : Nat := 2945025674968091888310803

theorem tailTrace_5735417 : CollatzResearch.WordTrace tailWord_5735417 prefixEnd_5735417 2945025674968091888310803 := by
  unfold tailWord_5735417
  simp only [CollatzResearch.WordTrace]
  refine ⟨209187843462571215084244505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139458562308380810056163003 209187843462571215084244505)
  ·
    refine ⟨156890882596928411313183379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209187843462571215084244505 156890882596928411313183379)
    ·
      refine ⟨235336323895392616969775069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156890882596928411313183379 235336323895392616969775069)
      ·
        refine ⟨88251121460772231363665651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 235336323895392616969775069 88251121460772231363665651)
        ·
          refine ⟨132376682191158347045498477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88251121460772231363665651 132376682191158347045498477)
          ·
            refine ⟨49641255821684380142061929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 132376682191158347045498477 49641255821684380142061929)
            ·
              refine ⟨37230941866263285106546447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49641255821684380142061929 37230941866263285106546447)
              ·
                refine ⟨55846412799394927659819671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37230941866263285106546447 55846412799394927659819671)
                ·
                  refine ⟨83769619199092391489729507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55846412799394927659819671 83769619199092391489729507)
                  ·
                    refine ⟨125654428798638587234594261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 83769619199092391489729507 125654428798638587234594261)
                    ·
                      refine ⟨2945025674968091888310803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 125654428798638587234594261 2945025674968091888310803)
                      ·
                        rfl

theorem cell23_5735417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_5735417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735417 prefixEnd_5735417 := by exact prefixLift 5735417
  have htrace : WordTrace (prefixWord ++ tailWord_5735417) baseStart_5735417 baseEnd_5735417 := by
    simpa [prefixWord, tailWord_5735417, baseEnd_5735417] using wordTrace_append hprefix tailTrace_5735417
  have hstable : (prefixWord ++ tailWord_5735417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735417).length < 2 ^ (prefixWord ++ tailWord_5735417).sum := by decide
  have hdescent : baseEnd_5735417 < baseStart_5735417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735422 : List Nat := [4, 2, 2, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_5735422 : Nat := 118140960795 + 5735422 * 2 ^ 59
def prefixEnd_5735422 : Nat := 4983230072969 + 3 ^ 40 * 5735422 * 2
def baseEnd_5735422 : Nat := 2945028242371364368748281

theorem tailTrace_5735422 : CollatzResearch.WordTrace tailWord_5735422 prefixEnd_5735422 2945028242371364368748281 := by
  unfold tailWord_5735422
  simp only [CollatzResearch.WordTrace]
  refine ⟨26148503228444137617272065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139458683885035400625451013 26148503228444137617272065)
  ·
    refine ⟨19611377421333103212954049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26148503228444137617272065 19611377421333103212954049)
    ·
      refine ⟨14708533065999827409715537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19611377421333103212954049 14708533065999827409715537)
      ·
        refine ⟨11031399799499870557286653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14708533065999827409715537 11031399799499870557286653)
        ·
          refine ⟨4136774924812451458982495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11031399799499870557286653 4136774924812451458982495)
          ·
            refine ⟨6205162387218677188473743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4136774924812451458982495 6205162387218677188473743)
            ·
              refine ⟨9307743580828015782710615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6205162387218677188473743 9307743580828015782710615)
              ·
                refine ⟨13961615371242023674065923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9307743580828015782710615 13961615371242023674065923)
                ·
                  refine ⟨20942423056863035511098885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13961615371242023674065923 20942423056863035511098885)
                  ·
                    refine ⟨3926704323161819158331041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20942423056863035511098885 3926704323161819158331041)
                    ·
                      refine ⟨2945028242371364368748281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926704323161819158331041 2945028242371364368748281)
                      ·
                        rfl

theorem cell23_5735422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_5735422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735422 prefixEnd_5735422 := by exact prefixLift 5735422
  have htrace : WordTrace (prefixWord ++ tailWord_5735422) baseStart_5735422 baseEnd_5735422 := by
    simpa [prefixWord, tailWord_5735422, baseEnd_5735422] using wordTrace_append hprefix tailTrace_5735422
  have hstable : (prefixWord ++ tailWord_5735422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735422).length < 2 ^ (prefixWord ++ tailWord_5735422).sum := by decide
  have hdescent : baseEnd_5735422 < baseStart_5735422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735467 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 8]
def baseStart_5735467 : Nat := 118140960795 + 5735467 * 2 ^ 59
def prefixEnd_5735467 : Nat := 4983230072969 + 3 ^ 40 * 5735467 * 2
def baseEnd_5735467 : Nat := 327227927666757410298397

theorem tailTrace_5735467 : CollatzResearch.WordTrace tailWord_5735467 prefixEnd_5735467 327227927666757410298397 := by
  unfold tailWord_5735467
  simp only [CollatzResearch.WordTrace]
  refine ⟨209189667112390073623564655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139459778074926715749043103 209189667112390073623564655)
  ·
    refine ⟨313784500668585110435346983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209189667112390073623564655 313784500668585110435346983)
    ·
      refine ⟨470676751002877665653020475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313784500668585110435346983 470676751002877665653020475)
      ·
        refine ⟨706015126504316498479530713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470676751002877665653020475 706015126504316498479530713)
        ·
          refine ⟨529511344878237373859648035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706015126504316498479530713 529511344878237373859648035)
          ·
            refine ⟨794267017317356060789472053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529511344878237373859648035 794267017317356060789472053)
            ·
              refine ⟨74462532873502130699013005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 794267017317356060789472053 74462532873502130699013005)
              ·
                refine ⟨27923449827563299012129877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74462532873502130699013005 27923449827563299012129877)
                ·
                  refine ⟨327227927666757410298397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27923449827563299012129877 327227927666757410298397)
                  ·
                    rfl

theorem cell23_5735467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 8].length) (baseStart_5735467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735467 prefixEnd_5735467 := by exact prefixLift 5735467
  have htrace : WordTrace (prefixWord ++ tailWord_5735467) baseStart_5735467 baseEnd_5735467 := by
    simpa [prefixWord, tailWord_5735467, baseEnd_5735467] using wordTrace_append hprefix tailTrace_5735467
  have hstable : (prefixWord ++ tailWord_5735467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735467).length < 2 ^ (prefixWord ++ tailWord_5735467).sum := by decide
  have hdescent : baseEnd_5735467 < baseStart_5735467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735522 : List Nat := [3, 3, 2, 2, 1, 1, 4, 2, 1, 4]
def baseStart_5735522 : Nat := 118140960795 + 5735522 * 2 ^ 59
def prefixEnd_5735522 : Nat := 4983230072969 + 3 ^ 40 * 5735522 * 2
def baseEnd_5735522 : Nat := 981693196812271325832607

theorem tailTrace_5735522 : CollatzResearch.WordTrace tailWord_5735522 prefixEnd_5735522 981693196812271325832607 := by
  unfold tailWord_5735522
  simp only [CollatzResearch.WordTrace]
  refine ⟨52297918281797704504204205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139461115418127212011211213 52297918281797704504204205)
  ·
    refine ⟨19611719355674139189076577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52297918281797704504204205 19611719355674139189076577)
    ·
      refine ⟨14708789516755604391807433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19611719355674139189076577 14708789516755604391807433)
      ·
        refine ⟨11031592137566703293855575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14708789516755604391807433 11031592137566703293855575)
        ·
          refine ⟨16547388206350054940783363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11031592137566703293855575 16547388206350054940783363)
          ·
            refine ⟨24821082309525082411175045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16547388206350054940783363 24821082309525082411175045)
            ·
              refine ⟨4653952933035952952095321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24821082309525082411175045 4653952933035952952095321)
              ·
                refine ⟨3490464699776964714071491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4653952933035952952095321 3490464699776964714071491)
                ·
                  refine ⟨5235697049665447071107237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3490464699776964714071491 5235697049665447071107237)
                  ·
                    refine ⟨981693196812271325832607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5235697049665447071107237 981693196812271325832607)
                    ·
                      rfl

theorem cell23_5735522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_5735522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735522 prefixEnd_5735522 := by exact prefixLift 5735522
  have htrace : WordTrace (prefixWord ++ tailWord_5735522) baseStart_5735522 baseEnd_5735522 := by
    simpa [prefixWord, tailWord_5735522, baseEnd_5735522] using wordTrace_append hprefix tailTrace_5735522
  have hstable : (prefixWord ++ tailWord_5735522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735522).length < 2 ^ (prefixWord ++ tailWord_5735522).sum := by decide
  have hdescent : baseEnd_5735522 < baseStart_5735522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735544 : List Nat := [2, 1, 2, 1, 1, 1, 5, 3, 1, 6]
def baseStart_5735544 : Nat := 118140960795 + 5735544 * 2 ^ 59
def prefixEnd_5735544 : Nat := 4983230072969 + 3 ^ 40 * 5735544 * 2
def baseEnd_5735544 : Nat := 981696962337070963807573

theorem tailTrace_5735544 : CollatzResearch.WordTrace tailWord_5735544 prefixEnd_5735544 981696962337070963807573 := by
  unfold tailWord_5735544
  simp only [CollatzResearch.WordTrace]
  refine ⟨104596237766555557887058843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139461650355407410516078457 104596237766555557887058843)
  ·
    refine ⟨156894356649833336830588265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104596237766555557887058843 156894356649833336830588265)
    ·
      refine ⟨117670767487375002622941199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156894356649833336830588265 117670767487375002622941199)
      ·
        refine ⟨176506151231062503934411799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117670767487375002622941199 176506151231062503934411799)
        ·
          refine ⟨264759226846593755901617699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176506151231062503934411799 264759226846593755901617699)
          ·
            refine ⟨397138840269890633852426549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264759226846593755901617699 397138840269890633852426549)
            ·
              refine ⟨37231766275302246923664989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 397138840269890633852426549 37231766275302246923664989)
              ·
                refine ⟨13961912353238342596374371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37231766275302246923664989 13961912353238342596374371)
                ·
                  refine ⟨20942868529857513894561557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13961912353238342596374371 20942868529857513894561557)
                  ·
                    refine ⟨981696962337070963807573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20942868529857513894561557 981696962337070963807573)
                    ·
                      rfl

theorem cell23_5735544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 3, 1, 6].length) (baseStart_5735544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735544 prefixEnd_5735544 := by exact prefixLift 5735544
  have htrace : WordTrace (prefixWord ++ tailWord_5735544) baseStart_5735544 baseEnd_5735544 := by
    simpa [prefixWord, tailWord_5735544, baseEnd_5735544] using wordTrace_append hprefix tailTrace_5735544
  have hstable : (prefixWord ++ tailWord_5735544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735544).length < 2 ^ (prefixWord ++ tailWord_5735544).sum := by decide
  have hdescent : baseEnd_5735544 < baseStart_5735544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735578 : List Nat := [3, 1, 1, 5, 1, 2, 1, 1, 4, 4]
def baseStart_5735578 : Nat := 118140960795 + 5735578 * 2 ^ 59
def prefixEnd_5735578 : Nat := 4983230072969 + 3 ^ 40 * 5735578 * 2
def baseEnd_5735578 : Nat := 981702781784488586132521

theorem tailTrace_5735578 : CollatzResearch.WordTrace tailWord_5735578 prefixEnd_5735578 981702781784488586132521 := by
  unfold tailWord_5735578
  simp only [CollatzResearch.WordTrace]
  refine ⟨52298428903746984895213847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139462477076658626387236925 52298428903746984895213847)
  ·
    refine ⟨78447643355620477342820771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52298428903746984895213847 78447643355620477342820771)
    ·
      refine ⟨117671465033430716014231157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78447643355620477342820771 117671465033430716014231157)
      ·
        refine ⟨11031699846884129626334171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117671465033430716014231157 11031699846884129626334171)
        ·
          refine ⟨16547549770326194439501257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11031699846884129626334171 16547549770326194439501257)
          ·
            refine ⟨12410662327744645829625943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16547549770326194439501257 12410662327744645829625943)
            ·
              refine ⟨18615993491616968744438915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12410662327744645829625943 18615993491616968744438915)
              ·
                refine ⟨27923990237425453116658373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18615993491616968744438915 27923990237425453116658373)
                ·
                  refine ⟨5235748169517272459373445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27923990237425453116658373 5235748169517272459373445)
                  ·
                    refine ⟨981702781784488586132521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5235748169517272459373445 981702781784488586132521)
                    ·
                      rfl

theorem cell23_5735578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_5735578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735578 prefixEnd_5735578 := by exact prefixLift 5735578
  have htrace : WordTrace (prefixWord ++ tailWord_5735578) baseStart_5735578 baseEnd_5735578 := by
    simpa [prefixWord, tailWord_5735578, baseEnd_5735578] using wordTrace_append hprefix tailTrace_5735578
  have hstable : (prefixWord ++ tailWord_5735578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735578).length < 2 ^ (prefixWord ++ tailWord_5735578).sum := by decide
  have hdescent : baseEnd_5735578 < baseStart_5735578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735585 : List Nat := [1, 2, 3, 3, 1, 1, 4, 1, 3, 2, 2]
def baseStart_5735585 : Nat := 118140960795 + 5735585 * 2 ^ 59
def prefixEnd_5735585 : Nat := 4983230072969 + 3 ^ 40 * 5735585 * 2
def baseEnd_5735585 : Nat := 2945111939718047231010031

theorem tailTrace_5735585 : CollatzResearch.WordTrace tailWord_5735585 prefixEnd_5735585 2945111939718047231010031 := by
  unfold tailWord_5735585
  simp only [CollatzResearch.WordTrace]
  refine ⟨209193970925962579776360209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139462647283975053184240139 209193970925962579776360209)
  ·
    refine ⟨156895478194471934832270157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209193970925962579776360209 156895478194471934832270157)
    ·
      refine ⟨58835804322926975562101309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156895478194471934832270157 58835804322926975562101309)
      ·
        refine ⟨22063426621097615835787991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58835804322926975562101309 22063426621097615835787991)
        ·
          refine ⟨33095139931646423753681987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22063426621097615835787991 33095139931646423753681987)
          ·
            refine ⟨49642709897469635630522981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33095139931646423753681987 49642709897469635630522981)
            ·
              refine ⟨9308008105775556680723059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49642709897469635630522981 9308008105775556680723059)
              ·
                refine ⟨13962012158663335021084589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9308008105775556680723059 13962012158663335021084589)
                ·
                  refine ⟨5235754559498750632906721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13962012158663335021084589 5235754559498750632906721)
                  ·
                    refine ⟨3926815919624062974680041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5235754559498750632906721 3926815919624062974680041)
                    ·
                      refine ⟨2945111939718047231010031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926815919624062974680041 2945111939718047231010031)
                      ·
                        rfl

theorem cell23_5735585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_5735585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735585 prefixEnd_5735585 := by exact prefixLift 5735585
  have htrace : WordTrace (prefixWord ++ tailWord_5735585) baseStart_5735585 baseEnd_5735585 := by
    simpa [prefixWord, tailWord_5735585, baseEnd_5735585] using wordTrace_append hprefix tailTrace_5735585
  have hstable : (prefixWord ++ tailWord_5735585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735585).length < 2 ^ (prefixWord ++ tailWord_5735585).sum := by decide
  have hdescent : baseEnd_5735585 < baseStart_5735585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735636 : List Nat := [2, 4, 1, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5735636 : Nat := 118140960795 + 5735636 * 2 ^ 59
def prefixEnd_5735636 : Nat := 4983230072969 + 3 ^ 40 * 5735636 * 2
def baseEnd_5735636 : Nat := 2945138127231426531472297

theorem tailTrace_5735636 : CollatzResearch.WordTrace tailWord_5735636 prefixEnd_5735636 2945138127231426531472297 := by
  unfold tailWord_5735636
  simp only [CollatzResearch.WordTrace]
  refine ⟨104597915524388907743233381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139463887365851876990977841 104597915524388907743233381)
  ·
    refine ⟨19612109160822920201856259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104597915524388907743233381 19612109160822920201856259)
    ·
      refine ⟨29418163741234380302784389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19612109160822920201856259 29418163741234380302784389)
      ·
        refine ⟨5515905701481446306772073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29418163741234380302784389 5515905701481446306772073)
        ·
          refine ⟨4136929276111084730079055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5515905701481446306772073 4136929276111084730079055)
          ·
            refine ⟨6205393914166627095118583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4136929276111084730079055 6205393914166627095118583)
            ·
              refine ⟨9308090871249940642677875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6205393914166627095118583 9308090871249940642677875)
              ·
                refine ⟨13962136306874910964016813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9308090871249940642677875 13962136306874910964016813)
                ·
                  refine ⟨5235801115078091611506305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13962136306874910964016813 5235801115078091611506305)
                  ·
                    refine ⟨3926850836308568708629729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5235801115078091611506305 3926850836308568708629729)
                    ·
                      refine ⟨2945138127231426531472297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926850836308568708629729 2945138127231426531472297)
                      ·
                        rfl

theorem cell23_5735636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5735636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735636 prefixEnd_5735636 := by exact prefixLift 5735636
  have htrace : WordTrace (prefixWord ++ tailWord_5735636) baseStart_5735636 baseEnd_5735636 := by
    simpa [prefixWord, tailWord_5735636, baseEnd_5735636] using wordTrace_append hprefix tailTrace_5735636
  have hstable : (prefixWord ++ tailWord_5735636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735636).length < 2 ^ (prefixWord ++ tailWord_5735636).sum := by decide
  have hdescent : baseEnd_5735636 < baseStart_5735636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735678 : List Nat := [4, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_5735678 : Nat := 118140960795 + 5735678 * 2 ^ 59
def prefixEnd_5735678 : Nat := 4983230072969 + 3 ^ 40 * 5735678 * 2
def baseEnd_5735678 : Nat := 2945159693418915367147103

theorem tailTrace_5735678 : CollatzResearch.WordTrace tailWord_5735678 prefixEnd_5735678 2945159693418915367147103 := by
  unfold tailWord_5735678
  simp only [CollatzResearch.WordTrace]
  refine ⟨26149670364328207082436961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 139464908609750437772997125 26149670364328207082436961)
  ·
    refine ⟨19612252773246155311827721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26149670364328207082436961 19612252773246155311827721)
    ·
      refine ⟨14709189579934616483870791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19612252773246155311827721 14709189579934616483870791)
      ·
        refine ⟨22063784369901924725806187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14709189579934616483870791 22063784369901924725806187)
        ·
          refine ⟨33095676554852887088709281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22063784369901924725806187 33095676554852887088709281)
          ·
            refine ⟨24821757416139665316531961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33095676554852887088709281 24821757416139665316531961)
            ·
              refine ⟨18616318062104748987398971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24821757416139665316531961 18616318062104748987398971)
              ·
                refine ⟨27924477093157123481098457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18616318062104748987398971 27924477093157123481098457)
                ·
                  refine ⟨20943357819867842610823843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27924477093157123481098457 20943357819867842610823843)
                  ·
                    refine ⟨31415036729801763916235765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20943357819867842610823843 31415036729801763916235765)
                    ·
                      refine ⟨2945159693418915367147103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31415036729801763916235765 2945159693418915367147103)
                      ·
                        rfl

theorem cell23_5735678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_5735678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735678 prefixEnd_5735678 := by exact prefixLift 5735678
  have htrace : WordTrace (prefixWord ++ tailWord_5735678) baseStart_5735678 baseEnd_5735678 := by
    simpa [prefixWord, tailWord_5735678, baseEnd_5735678] using wordTrace_append hprefix tailTrace_5735678
  have hstable : (prefixWord ++ tailWord_5735678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735678).length < 2 ^ (prefixWord ++ tailWord_5735678).sum := by decide
  have hdescent : baseEnd_5735678 < baseStart_5735678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735692 : List Nat := [2, 2, 1, 2, 2, 4, 2, 2, 2, 2, 2]
def baseStart_5735692 : Nat := 118140960795 + 5735692 * 2 ^ 59
def prefixEnd_5735692 : Nat := 4983230072969 + 3 ^ 40 * 5735692 * 2
def baseEnd_5735692 : Nat := 2945166882148078312372039

theorem tailTrace_5735692 : CollatzResearch.WordTrace tailWord_5735692 prefixEnd_5735692 2945166882148078312372039 := by
  unfold tailWord_5735692
  simp only [CollatzResearch.WordTrace]
  refine ⟨104598936768287468525252665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139465249024383291367003553 104598936768287468525252665)
  ·
    refine ⟨78449202576215601393939499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104598936768287468525252665 78449202576215601393939499)
    ·
      refine ⟨117673803864323402090909249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78449202576215601393939499 117673803864323402090909249)
      ·
        refine ⟨88255352898242551568181937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117673803864323402090909249 88255352898242551568181937)
        ·
          refine ⟨66191514673681913676136453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88255352898242551568181937 66191514673681913676136453)
          ·
            refine ⟨12410909001315358814275585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66191514673681913676136453 12410909001315358814275585)
            ·
              refine ⟨9308181750986519110706689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12410909001315358814275585 9308181750986519110706689)
              ·
                refine ⟨6981136313239889333030017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9308181750986519110706689 6981136313239889333030017)
                ·
                  refine ⟨5235852234929916999772513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6981136313239889333030017 5235852234929916999772513)
                  ·
                    refine ⟨3926889176197437749829385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5235852234929916999772513 3926889176197437749829385)
                    ·
                      refine ⟨2945166882148078312372039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926889176197437749829385 2945166882148078312372039)
                      ·
                        rfl

theorem cell23_5735692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_5735692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735692 prefixEnd_5735692 := by exact prefixLift 5735692
  have htrace : WordTrace (prefixWord ++ tailWord_5735692) baseStart_5735692 baseEnd_5735692 := by
    simpa [prefixWord, tailWord_5735692, baseEnd_5735692] using wordTrace_append hprefix tailTrace_5735692
  have hstable : (prefixWord ++ tailWord_5735692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735692).length < 2 ^ (prefixWord ++ tailWord_5735692).sum := by decide
  have hdescent : baseEnd_5735692 < baseStart_5735692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735761 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_5735761 : Nat := 118140960795 + 5735761 * 2 ^ 59
def prefixEnd_5735761 : Nat := 4983230072969 + 3 ^ 40 * 5735761 * 2
def baseEnd_5735761 : Nat := 2945202312313238542409221

theorem tailTrace_5735761 : CollatzResearch.WordTrace tailWord_5735761 prefixEnd_5735761 2945202312313238542409221 := by
  unfold tailWord_5735761
  simp only [CollatzResearch.WordTrace]
  refine ⟨209200390173324961834767137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139466926782216641223178091 209200390173324961834767137)
  ·
    refine ⟨156900292629993721376075353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209200390173324961834767137 156900292629993721376075353)
    ·
      refine ⟨117675219472495291032056515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156900292629993721376075353 117675219472495291032056515)
      ·
        refine ⟨176512829208742936548084773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117675219472495291032056515 176512829208742936548084773)
        ·
          refine ⟨33096155476639300602765895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 176512829208742936548084773 33096155476639300602765895)
          ·
            refine ⟨49644233214958950904148843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33096155476639300602765895 49644233214958950904148843)
            ·
              refine ⟨74466349822438426356223265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49644233214958950904148843 74466349822438426356223265)
              ·
                refine ⟨55849762366828819767167449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74466349822438426356223265 55849762366828819767167449)
                ·
                  refine ⟨41887321775121614825375587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55849762366828819767167449 41887321775121614825375587)
                  ·
                    refine ⟨62830982662682422238063381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41887321775121614825375587 62830982662682422238063381)
                    ·
                      refine ⟨2945202312313238542409221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62830982662682422238063381 2945202312313238542409221)
                      ·
                        rfl

theorem cell23_5735761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_5735761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735761 prefixEnd_5735761 := by exact prefixLift 5735761
  have htrace : WordTrace (prefixWord ++ tailWord_5735761) baseStart_5735761 baseEnd_5735761 := by
    simpa [prefixWord, tailWord_5735761, baseEnd_5735761] using wordTrace_append hprefix tailTrace_5735761
  have hstable : (prefixWord ++ tailWord_5735761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735761).length < 2 ^ (prefixWord ++ tailWord_5735761).sum := by decide
  have hdescent : baseEnd_5735761 < baseStart_5735761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735765 : List Nat := [1, 3, 2, 2, 3, 1, 2, 1, 2, 4, 2]
def baseStart_5735765 : Nat := 118140960795 + 5735765 * 2 ^ 59
def prefixEnd_5735765 : Nat := 4983230072969 + 3 ^ 40 * 5735765 * 2
def baseEnd_5735765 : Nat := 2945204366235856526759203

theorem tailTrace_5735765 : CollatzResearch.WordTrace tailWord_5735765 prefixEnd_5735765 2945204366235856526759203 := by
  unfold tailWord_5735765
  simp only [CollatzResearch.WordTrace]
  refine ⟨209200536065310470517912749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139467024043540313678608499 209200536065310470517912749)
  ·
    refine ⟨78450201024491426444217281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209200536065310470517912749 78450201024491426444217281)
    ·
      refine ⟨58837650768368569833162961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78450201024491426444217281 58837650768368569833162961)
      ·
        refine ⟨44128238076276427374872221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58837650768368569833162961 44128238076276427374872221)
        ·
          refine ⟨16548089278603660265577083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44128238076276427374872221 16548089278603660265577083)
          ·
            refine ⟨24822133917905490398365625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16548089278603660265577083 24822133917905490398365625)
            ·
              refine ⟨18616600438429117798774219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24822133917905490398365625 18616600438429117798774219)
              ·
                refine ⟨27924900657643676698161329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18616600438429117798774219 27924900657643676698161329)
                ·
                  refine ⟨20943675493232757523620997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27924900657643676698161329 20943675493232757523620997)
                  ·
                    refine ⟨3926939154981142035678937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20943675493232757523620997 3926939154981142035678937)
                    ·
                      refine ⟨2945204366235856526759203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926939154981142035678937 2945204366235856526759203)
                      ·
                        rfl

theorem cell23_5735765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_5735765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735765 prefixEnd_5735765 := by exact prefixLift 5735765
  have htrace : WordTrace (prefixWord ++ tailWord_5735765) baseStart_5735765 baseEnd_5735765 := by
    simpa [prefixWord, tailWord_5735765, baseEnd_5735765] using wordTrace_append hprefix tailTrace_5735765
  have hstable : (prefixWord ++ tailWord_5735765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735765).length < 2 ^ (prefixWord ++ tailWord_5735765).sum := by decide
  have hdescent : baseEnd_5735765 < baseStart_5735765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735778 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_5735778 : Nat := 118140960795 + 5735778 * 2 ^ 59
def prefixEnd_5735778 : Nat := 4983230072969 + 3 ^ 40 * 5735778 * 2
def baseEnd_5735778 : Nat := 2945211041484364975896643

theorem tailTrace_5735778 : CollatzResearch.WordTrace tailWord_5735778 prefixEnd_5735778 2945211041484364975896643 := by
  unfold tailWord_5735778
  simp only [CollatzResearch.WordTrace]
  refine ⟨52300252553565843434533997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139467340142842249158757325 52300252553565843434533997)
  ·
    refine ⟨19612594707587191287950249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52300252553565843434533997 19612594707587191287950249)
    ·
      refine ⟨14709446030690393465962687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19612594707587191287950249 14709446030690393465962687)
      ·
        refine ⟨22064169046035590198944031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14709446030690393465962687 22064169046035590198944031)
        ·
          refine ⟨33096253569053385298416047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22064169046035590198944031 33096253569053385298416047)
          ·
            refine ⟨49644380353580077947624071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33096253569053385298416047 49644380353580077947624071)
            ·
              refine ⟨74466570530370116921436107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49644380353580077947624071 74466570530370116921436107)
              ·
                refine ⟨111699855795555175382154161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74466570530370116921436107 111699855795555175382154161)
                ·
                  refine ⟨83774891846666381536615621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111699855795555175382154161 83774891846666381536615621)
                  ·
                    refine ⟨15707792221249946538115429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83774891846666381536615621 15707792221249946538115429)
                    ·
                      refine ⟨2945211041484364975896643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15707792221249946538115429 2945211041484364975896643)
                      ·
                        rfl

theorem cell23_5735778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_5735778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735778 prefixEnd_5735778 := by exact prefixLift 5735778
  have htrace : WordTrace (prefixWord ++ tailWord_5735778) baseStart_5735778 baseEnd_5735778 := by
    simpa [prefixWord, tailWord_5735778, baseEnd_5735778] using wordTrace_append hprefix tailTrace_5735778
  have hstable : (prefixWord ++ tailWord_5735778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735778).length < 2 ^ (prefixWord ++ tailWord_5735778).sum := by decide
  have hdescent : baseEnd_5735778 < baseStart_5735778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735809 : List Nat := [1, 2, 4, 3, 3, 1, 1, 1, 3, 4]
def baseStart_5735809 : Nat := 118140960795 + 5735809 * 2 ^ 59
def prefixEnd_5735809 : Nat := 4983230072969 + 3 ^ 40 * 5735809 * 2
def baseEnd_5735809 : Nat := 981742319794884784869667

theorem tailTrace_5735809 : CollatzResearch.WordTrace tailWord_5735809 prefixEnd_5735809 981742319794884784869667 := by
  unfold tailWord_5735809
  simp only [CollatzResearch.WordTrace]
  refine ⟨209202140877151066032514481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139468093918100710688342987 209202140877151066032514481)
  ·
    refine ⟨156901605657863299524385861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209202140877151066032514481 156901605657863299524385861)
    ·
      refine ⟨29419051060849368660822349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156901605657863299524385861 29419051060849368660822349)
      ·
        refine ⟨11032144147818513247808381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29419051060849368660822349 11032144147818513247808381)
        ·
          refine ⟨4137054055431942467928143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11032144147818513247808381 4137054055431942467928143)
          ·
            refine ⟨6205581083147913701892215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137054055431942467928143 6205581083147913701892215)
            ·
              refine ⟨9308371624721870552838323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6205581083147913701892215 9308371624721870552838323)
              ·
                refine ⟨13962557437082805829257485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9308371624721870552838323 13962557437082805829257485)
                ·
                  refine ⟨5235959038906052185971557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13962557437082805829257485 5235959038906052185971557)
                  ·
                    refine ⟨981742319794884784869667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5235959038906052185971557 981742319794884784869667)
                    ·
                      rfl

theorem cell23_5735809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_5735809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735809 prefixEnd_5735809 := by exact prefixLift 5735809
  have htrace : WordTrace (prefixWord ++ tailWord_5735809) baseStart_5735809 baseEnd_5735809 := by
    simpa [prefixWord, tailWord_5735809, baseEnd_5735809] using wordTrace_append hprefix tailTrace_5735809
  have hstable : (prefixWord ++ tailWord_5735809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735809).length < 2 ^ (prefixWord ++ tailWord_5735809).sum := by decide
  have hdescent : baseEnd_5735809 < baseStart_5735809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735842 : List Nat := [3, 3, 1, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_5735842 : Nat := 118140960795 + 5735842 * 2 ^ 59
def prefixEnd_5735842 : Nat := 4983230072969 + 3 ^ 40 * 5735842 * 2
def baseEnd_5735842 : Nat := 2945243904246252725496349

theorem tailTrace_5735842 : CollatzResearch.WordTrace tailWord_5735842 prefixEnd_5735842 2945243904246252725496349 := by
  unfold tailWord_5735842
  simp only [CollatzResearch.WordTrace]
  refine ⟨52300836121507878167116445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139468896324021008445643853 52300836121507878167116445)
  ·
    refine ⟨19612813545565454312668667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52300836121507878167116445 19612813545565454312668667)
    ·
      refine ⟨29419220318348181469003001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19612813545565454312668667 29419220318348181469003001)
      ·
        refine ⟨22064415238761136101752251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29419220318348181469003001 22064415238761136101752251)
        ·
          refine ⟨33096622858141704152628377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22064415238761136101752251 33096622858141704152628377)
          ·
            refine ⟨24822467143606278114471283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33096622858141704152628377 24822467143606278114471283)
            ·
              refine ⟨37233700715409417171706925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24822467143606278114471283 37233700715409417171706925)
              ·
                refine ⟨13962637768278531439390097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37233700715409417171706925 13962637768278531439390097)
                ·
                  refine ⟨10471978326208898579542573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13962637768278531439390097 10471978326208898579542573)
                  ·
                    refine ⟨3926991872328336967328465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10471978326208898579542573 3926991872328336967328465)
                    ·
                      refine ⟨2945243904246252725496349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3926991872328336967328465 2945243904246252725496349)
                      ·
                        rfl

theorem cell23_5735842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_5735842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735842 prefixEnd_5735842 := by exact prefixLift 5735842
  have htrace : WordTrace (prefixWord ++ tailWord_5735842) baseStart_5735842 baseEnd_5735842 := by
    simpa [prefixWord, tailWord_5735842, baseEnd_5735842] using wordTrace_append hprefix tailTrace_5735842
  have hstable : (prefixWord ++ tailWord_5735842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735842).length < 2 ^ (prefixWord ++ tailWord_5735842).sum := by decide
  have hdescent : baseEnd_5735842 < baseStart_5735842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735858 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_5735858 : Nat := 118140960795 + 5735858 * 2 ^ 59
def prefixEnd_5735858 : Nat := 4983230072969 + 3 ^ 40 * 5735858 * 2
def baseEnd_5735858 : Nat := 2945252119936724662896275

theorem tailTrace_5735858 : CollatzResearch.WordTrace tailWord_5735858 prefixEnd_5735858 2945252119936724662896275 := by
  unfold tailWord_5735858
  simp only [CollatzResearch.WordTrace]
  refine ⟨52300982013493386850262057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139469285369315698267365485 52300982013493386850262057)
  ·
    refine ⟨39225736510120040137696543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52300982013493386850262057 39225736510120040137696543)
    ·
      refine ⟨58838604765180060206544815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39225736510120040137696543 58838604765180060206544815)
      ·
        refine ⟨88257907147770090309817223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58838604765180060206544815 88257907147770090309817223)
        ·
          refine ⟨132386860721655135464725835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88257907147770090309817223 132386860721655135464725835)
          ·
            refine ⟨198580291082482703197088753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132386860721655135464725835 198580291082482703197088753)
            ·
              refine ⟨148935218311862027397816565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198580291082482703197088753 148935218311862027397816565)
              ·
                refine ⟨13962676716737065068545303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 148935218311862027397816565 13962676716737065068545303)
                ·
                  refine ⟨20944015075105597602817955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13962676716737065068545303 20944015075105597602817955)
                  ·
                    refine ⟨31416022612658396404226933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20944015075105597602817955 31416022612658396404226933)
                    ·
                      refine ⟨2945252119936724662896275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31416022612658396404226933 2945252119936724662896275)
                      ·
                        rfl

theorem cell23_5735858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_5735858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735858 prefixEnd_5735858 := by exact prefixLift 5735858
  have htrace : WordTrace (prefixWord ++ tailWord_5735858) baseStart_5735858 baseEnd_5735858 := by
    simpa [prefixWord, tailWord_5735858, baseEnd_5735858] using wordTrace_append hprefix tailTrace_5735858
  have hstable : (prefixWord ++ tailWord_5735858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735858).length < 2 ^ (prefixWord ++ tailWord_5735858).sum := by decide
  have hdescent : baseEnd_5735858 < baseStart_5735858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735888 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 3]
def baseStart_5735888 : Nat := 118140960795 + 5735888 * 2 ^ 59
def prefixEnd_5735888 : Nat := 4983230072969 + 3 ^ 40 * 5735888 * 2
def baseEnd_5735888 : Nat := 2945267524356359545521137

theorem tailTrace_5735888 : CollatzResearch.WordTrace tailWord_5735888 prefixEnd_5735888 2945267524356359545521137 := by
  unfold tailWord_5735888
  simp only [CollatzResearch.WordTrace]
  refine ⟨104602511121932431262320159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139470014829243241683093545 104602511121932431262320159)
  ·
    refine ⟨156903766682898646893480239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104602511121932431262320159 156903766682898646893480239)
    ·
      refine ⟨235355650024347970340220359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156903766682898646893480239 235355650024347970340220359)
      ·
        refine ⟨353033475036521955510330539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235355650024347970340220359 353033475036521955510330539)
        ·
          refine ⟨529550212554782933265495809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353033475036521955510330539 529550212554782933265495809)
          ·
            refine ⟨397162659416087199949121857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529550212554782933265495809 397162659416087199949121857)
            ·
              refine ⟨297871994562065399961841393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397162659416087199949121857 297871994562065399961841393)
              ·
                refine ⟨223403995921549049971381045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297871994562065399961841393 223403995921549049971381045)
                ·
                  refine ⟨20944124617645223434816973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223403995921549049971381045 20944124617645223434816973)
                  ·
                    refine ⟨7854046731616958788056365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20944124617645223434816973 7854046731616958788056365)
                    ·
                      refine ⟨2945267524356359545521137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854046731616958788056365 2945267524356359545521137)
                      ·
                        rfl

theorem cell23_5735888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 3].length) (baseStart_5735888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735888 prefixEnd_5735888 := by exact prefixLift 5735888
  have htrace : WordTrace (prefixWord ++ tailWord_5735888) baseStart_5735888 baseEnd_5735888 := by
    simpa [prefixWord, tailWord_5735888, baseEnd_5735888] using wordTrace_append hprefix tailTrace_5735888
  have hstable : (prefixWord ++ tailWord_5735888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735888).length < 2 ^ (prefixWord ++ tailWord_5735888).sum := by decide
  have hdescent : baseEnd_5735888 < baseStart_5735888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735905 : List Nat := [1, 2, 3, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_5735905 : Nat := 118140960795 + 5735905 * 2 ^ 59
def prefixEnd_5735905 : Nat := 4983230072969 + 3 ^ 40 * 5735905 * 2
def baseEnd_5735905 : Nat := 2945276253527485979008559

theorem tailTrace_5735905 : CollatzResearch.WordTrace tailWord_5735905 prefixEnd_5735905 2945276253527485979008559 := by
  unfold tailWord_5735905
  simp only [CollatzResearch.WordTrace]
  refine ⟨209205642284803274428009169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139470428189868849618672779 209205642284803274428009169)
  ·
    refine ⟨156904231713602455821006877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 209205642284803274428009169 156904231713602455821006877)
    ·
      refine ⟨58839086892600920932877579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156904231713602455821006877 58839086892600920932877579)
      ·
        refine ⟨88258630338901381399316369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58839086892600920932877579 88258630338901381399316369)
        ·
          refine ⟨66193972754176036049487277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88258630338901381399316369 66193972754176036049487277)
          ·
            refine ⟨24822739782816013518557729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66193972754176036049487277 24822739782816013518557729)
            ·
              refine ⟨18617054837112010138918297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24822739782816013518557729 18617054837112010138918297)
              ·
                refine ⟨13962791127834007604188723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18617054837112010138918297 13962791127834007604188723)
                ·
                  refine ⟨20944186691751011406283085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13962791127834007604188723 20944186691751011406283085)
                  ·
                    refine ⟨7854070009406629277356157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20944186691751011406283085 7854070009406629277356157)
                    ·
                      refine ⟨2945276253527485979008559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854070009406629277356157 2945276253527485979008559)
                      ·
                        rfl

theorem cell23_5735905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_5735905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735905 prefixEnd_5735905 := by exact prefixLift 5735905
  have htrace : WordTrace (prefixWord ++ tailWord_5735905) baseStart_5735905 baseEnd_5735905 := by
    simpa [prefixWord, tailWord_5735905, baseEnd_5735905] using wordTrace_append hprefix tailTrace_5735905
  have hstable : (prefixWord ++ tailWord_5735905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735905).length < 2 ^ (prefixWord ++ tailWord_5735905).sum := by decide
  have hdescent : baseEnd_5735905 < baseStart_5735905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735909 : List Nat := [1, 3, 1, 5, 1, 1, 4, 1, 1, 2, 3]
def baseStart_5735909 : Nat := 118140960795 + 5735909 * 2 ^ 59
def prefixEnd_5735909 : Nat := 4983230072969 + 3 ^ 40 * 5735909 * 2
def baseEnd_5735909 : Nat := 2945278307450103963358541

theorem tailTrace_5735909 : CollatzResearch.WordTrace tailWord_5735909 prefixEnd_5735909 2945278307450103963358541 := by
  unfold tailWord_5735909
  simp only [CollatzResearch.WordTrace]
  refine ⟨209205788176788783111154781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139470525451192522074103187 209205788176788783111154781)
  ·
    refine ⟨78452170566295793666683043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209205788176788783111154781 78452170566295793666683043)
    ·
      refine ⟨117678255849443690500024565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78452170566295793666683043 117678255849443690500024565)
      ·
        refine ⟨11032336485885345984377303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 117678255849443690500024565 11032336485885345984377303)
        ·
          refine ⟨16548504728828018976565955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11032336485885345984377303 16548504728828018976565955)
          ·
            refine ⟨24822757093242028464848933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16548504728828018976565955 24822757093242028464848933)
            ·
              refine ⟨4654266954982880337159175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24822757093242028464848933 4654266954982880337159175)
              ·
                refine ⟨6981400432474320505738763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654266954982880337159175 6981400432474320505738763)
                ·
                  refine ⟨10472100648711480758608145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6981400432474320505738763 10472100648711480758608145)
                  ·
                    refine ⟨7854075486533610568956109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10472100648711480758608145 7854075486533610568956109)
                    ·
                      refine ⟨2945278307450103963358541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854075486533610568956109 2945278307450103963358541)
                      ·
                        rfl

theorem cell23_5735909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_5735909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735909 prefixEnd_5735909 := by exact prefixLift 5735909
  have htrace : WordTrace (prefixWord ++ tailWord_5735909) baseStart_5735909 baseEnd_5735909 := by
    simpa [prefixWord, tailWord_5735909, baseEnd_5735909] using wordTrace_append hprefix tailTrace_5735909
  have hstable : (prefixWord ++ tailWord_5735909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735909).length < 2 ^ (prefixWord ++ tailWord_5735909).sum := by decide
  have hdescent : baseEnd_5735909 < baseStart_5735909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735915 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 5, 3, 2]
def baseStart_5735915 : Nat := 118140960795 + 5735915 * 2 ^ 59
def prefixEnd_5735915 : Nat := 4983230072969 + 3 ^ 40 * 5735915 * 2
def baseEnd_5735915 : Nat := 2945281388334030939883513

theorem tailTrace_5735915 : CollatzResearch.WordTrace tailWord_5735915 prefixEnd_5735915 2945281388334030939883513 := by
  unfold tailWord_5735915
  simp only [CollatzResearch.WordTrace]
  refine ⟨209206007014767046135873199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139470671343178030757248799 209206007014767046135873199)
  ·
    refine ⟨313809010522150569203809799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209206007014767046135873199 313809010522150569203809799)
    ·
      refine ⟨470713515783225853805714699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 313809010522150569203809799 470713515783225853805714699)
      ·
        refine ⟨706070273674838780708572049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470713515783225853805714699 706070273674838780708572049)
        ·
          refine ⟨529552705256129085531429037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706070273674838780708572049 529552705256129085531429037)
          ·
            refine ⟨198582264471048407074285889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 529552705256129085531429037 198582264471048407074285889)
            ·
              refine ⟨148936698353286305305714417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198582264471048407074285889 148936698353286305305714417)
              ·
                refine ⟨111702523764964728979285813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148936698353286305305714417 111702523764964728979285813)
                ·
                  refine ⟨10472111602965443341808045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 111702523764964728979285813 10472111602965443341808045)
                  ·
                    refine ⟨3927041851112041253178017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10472111602965443341808045 3927041851112041253178017)
                    ·
                      refine ⟨2945281388334030939883513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927041851112041253178017 2945281388334030939883513)
                      ·
                        rfl

theorem cell23_5735915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 3, 2].length) (baseStart_5735915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735915 prefixEnd_5735915 := by exact prefixLift 5735915
  have htrace : WordTrace (prefixWord ++ tailWord_5735915) baseStart_5735915 baseEnd_5735915 := by
    simpa [prefixWord, tailWord_5735915, baseEnd_5735915] using wordTrace_append hprefix tailTrace_5735915
  have hstable : (prefixWord ++ tailWord_5735915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735915).length < 2 ^ (prefixWord ++ tailWord_5735915).sum := by decide
  have hdescent : baseEnd_5735915 < baseStart_5735915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735965 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_5735965 : Nat := 118140960795 + 5735965 * 2 ^ 59
def prefixEnd_5735965 : Nat := 4983230072969 + 3 ^ 40 * 5735965 * 2
def baseEnd_5735965 : Nat := 2945307062366755744258283

theorem tailTrace_5735965 : CollatzResearch.WordTrace tailWord_5735965 prefixEnd_5735965 2945307062366755744258283 := by
  unfold tailWord_5735965
  simp only [CollatzResearch.WordTrace]
  refine ⟨209207830664585904675193349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139471887109723936450128899 209207830664585904675193349)
  ·
    refine ⟨39226468249609857126598753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 209207830664585904675193349 39226468249609857126598753)
    ·
      refine ⟨29419851187207392844949065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39226468249609857126598753 29419851187207392844949065)
      ·
        refine ⟨22064888390405544633711799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29419851187207392844949065 22064888390405544633711799)
        ·
          refine ⟨33097332585608316950567699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22064888390405544633711799 33097332585608316950567699)
          ·
            refine ⟨49645998878412475425851549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33097332585608316950567699 49645998878412475425851549)
            ·
              refine ⟨18617249579404678284694331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49645998878412475425851549 18617249579404678284694331)
              ·
                refine ⟨27925874369107017427041497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18617249579404678284694331 27925874369107017427041497)
                ·
                  refine ⟨20944405776830263070281123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27925874369107017427041497 20944405776830263070281123)
                  ·
                    refine ⟨31416608665245394605421685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20944405776830263070281123 31416608665245394605421685)
                    ·
                      refine ⟨2945307062366755744258283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31416608665245394605421685 2945307062366755744258283)
                      ·
                        rfl

theorem cell23_5735965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_5735965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735965 prefixEnd_5735965 := by exact prefixLift 5735965
  have htrace : WordTrace (prefixWord ++ tailWord_5735965) baseStart_5735965 baseEnd_5735965 := by
    simpa [prefixWord, tailWord_5735965, baseEnd_5735965] using wordTrace_append hprefix tailTrace_5735965
  have hstable : (prefixWord ++ tailWord_5735965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735965).length < 2 ^ (prefixWord ++ tailWord_5735965).sum := by decide
  have hdescent : baseEnd_5735965 < baseStart_5735965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735990 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_5735990 : Nat := 118140960795 + 5735990 * 2 ^ 59
def prefixEnd_5735990 : Nat := 4983230072969 + 3 ^ 40 * 5735990 * 2
def baseEnd_5735990 : Nat := 2945319899383118146445669

theorem tailTrace_5735990 : CollatzResearch.WordTrace tailWord_5735990 prefixEnd_5735990 2945319899383118146445669 := by
  unfold tailWord_5735990
  simp only [CollatzResearch.WordTrace]
  refine ⟨13075546405593458371553339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 139472494992996889296568949 13075546405593458371553339)
  ·
    refine ⟨19613319608390187557330009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13075546405593458371553339 19613319608390187557330009)
    ·
      refine ⟨14709989706292640667997507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19613319608390187557330009 14709989706292640667997507)
      ·
        refine ⟨22064984559438961001996261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14709989706292640667997507 22064984559438961001996261)
        ·
          refine ⟨4137184604894805187874299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22064984559438961001996261 4137184604894805187874299)
          ·
            refine ⟨6205776907342207781811449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4137184604894805187874299 6205776907342207781811449)
            ·
              refine ⟨4654332680506655836358587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6205776907342207781811449 4654332680506655836358587)
              ·
                refine ⟨6981499020759983754537881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654332680506655836358587 6981499020759983754537881)
                ·
                  refine ⟨5236124265569987815903411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6981499020759983754537881 5236124265569987815903411)
                  ·
                    refine ⟨7854186398354981723855117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5236124265569987815903411 7854186398354981723855117)
                    ·
                      refine ⟨2945319899383118146445669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854186398354981723855117 2945319899383118146445669)
                      ·
                        rfl

theorem cell23_5735990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_5735990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735990 prefixEnd_5735990 := by exact prefixLift 5735990
  have htrace : WordTrace (prefixWord ++ tailWord_5735990) baseStart_5735990 baseEnd_5735990 := by
    simpa [prefixWord, tailWord_5735990, baseEnd_5735990] using wordTrace_append hprefix tailTrace_5735990
  have hstable : (prefixWord ++ tailWord_5735990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735990).length < 2 ^ (prefixWord ++ tailWord_5735990).sum := by decide
  have hdescent : baseEnd_5735990 < baseStart_5735990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5735996 : List Nat := [2, 2, 2, 2, 4, 1, 1, 3, 2, 2, 2]
def baseStart_5735996 : Nat := 118140960795 + 5735996 * 2 ^ 59
def prefixEnd_5735996 : Nat := 4983230072969 + 3 ^ 40 * 5735996 * 2
def baseEnd_5735996 : Nat := 2945322980267045122970641

theorem tailTrace_5735996 : CollatzResearch.WordTrace tailWord_5735996 prefixEnd_5735996 2945322980267045122970641 := by
  unfold tailWord_5735996
  simp only [CollatzResearch.WordTrace]
  refine ⟨104604480663736798484785921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139472640884982397979714561 104604480663736798484785921)
  ·
    refine ⟨78453360497802598863589441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104604480663736798484785921 78453360497802598863589441)
    ·
      refine ⟨58840020373351949147692081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78453360497802598863589441 58840020373351949147692081)
      ·
        refine ⟨44130015280013961860769061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58840020373351949147692081 44130015280013961860769061)
        ·
          refine ⟨8274377865002617848894199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44130015280013961860769061 8274377865002617848894199)
          ·
            refine ⟨12411566797503926773341299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274377865002617848894199 12411566797503926773341299)
            ·
              refine ⟨18617350196255890160011949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12411566797503926773341299 18617350196255890160011949)
              ·
                refine ⟨6981506323595958810004481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18617350196255890160011949 6981506323595958810004481)
                ·
                  refine ⟨5236129742696969107503361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6981506323595958810004481 5236129742696969107503361)
                  ·
                    refine ⟨3927097307022726830627521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5236129742696969107503361 3927097307022726830627521)
                    ·
                      refine ⟨2945322980267045122970641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927097307022726830627521 2945322980267045122970641)
                      ·
                        rfl

theorem cell23_5735996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_5735996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5735996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5735996 prefixEnd_5735996 := by exact prefixLift 5735996
  have htrace : WordTrace (prefixWord ++ tailWord_5735996) baseStart_5735996 baseEnd_5735996 := by
    simpa [prefixWord, tailWord_5735996, baseEnd_5735996] using wordTrace_append hprefix tailTrace_5735996
  have hstable : (prefixWord ++ tailWord_5735996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5735996).length < 2 ^ (prefixWord ++ tailWord_5735996).sum := by decide
  have hdescent : baseEnd_5735996 < baseStart_5735996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5735996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736055 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 3]
def baseStart_5736055 : Nat := 118140960795 + 5736055 * 2 ^ 59
def prefixEnd_5736055 : Nat := 4983230072969 + 3 ^ 40 * 5736055 * 2
def baseEnd_5736055 : Nat := 2945353275625660392132869

theorem tailTrace_5736055 : CollatzResearch.WordTrace tailWord_5736055 prefixEnd_5736055 2945353275625660392132869 := by
  unfold tailWord_5736055
  simp only [CollatzResearch.WordTrace]
  refine ⟨209211113234259850045969619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139474075489506566697313079 209211113234259850045969619)
  ·
    refine ⟨313816669851389775068954429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209211113234259850045969619 313816669851389775068954429)
    ·
      refine ⟨117681251194271165650857911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313816669851389775068954429 117681251194271165650857911)
      ·
        refine ⟨176521876791406748476286867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117681251194271165650857911 176521876791406748476286867)
        ·
          refine ⟨264782815187110122714430301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176521876791406748476286867 264782815187110122714430301)
          ·
            refine ⟨99293555695166296017911363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 264782815187110122714430301 99293555695166296017911363)
            ·
              refine ⟨148940333542749444026867045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99293555695166296017911363 148940333542749444026867045)
              ·
                refine ⟨27926312539265520755037571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148940333542749444026867045 27926312539265520755037571)
                ·
                  refine ⟨41889468808898281132556357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27926312539265520755037571 41889468808898281132556357)
                  ·
                    refine ⟨7854275401668427712354317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41889468808898281132556357 7854275401668427712354317)
                    ·
                      refine ⟨2945353275625660392132869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854275401668427712354317 2945353275625660392132869)
                      ·
                        rfl

theorem cell23_5736055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_5736055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736055 prefixEnd_5736055 := by exact prefixLift 5736055
  have htrace : WordTrace (prefixWord ++ tailWord_5736055) baseStart_5736055 baseEnd_5736055 := by
    simpa [prefixWord, tailWord_5736055, baseEnd_5736055] using wordTrace_append hprefix tailTrace_5736055
  have hstable : (prefixWord ++ tailWord_5736055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736055).length < 2 ^ (prefixWord ++ tailWord_5736055).sum := by decide
  have hdescent : baseEnd_5736055 < baseStart_5736055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736085 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_5736085 : Nat := 118140960795 + 5736085 * 2 ^ 59
def prefixEnd_5736085 : Nat := 4983230072969 + 3 ^ 40 * 5736085 * 2
def baseEnd_5736085 : Nat := 2945368680045295274757731

theorem tailTrace_5736085 : CollatzResearch.WordTrace tailWord_5736085 prefixEnd_5736085 2945368680045295274757731 := by
  unfold tailWord_5736085
  simp only [CollatzResearch.WordTrace]
  refine ⟨209212207424151165169561709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139474804949434110113041139 209212207424151165169561709)
  ·
    refine ⟨78454577784056686938585641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 209212207424151165169561709 78454577784056686938585641)
    ·
      refine ⟨58840933338042515203939231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78454577784056686938585641 58840933338042515203939231)
      ·
        refine ⟨88261400007063772805908847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58840933338042515203939231 88261400007063772805908847)
        ·
          refine ⟨132392100010595659208863271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88261400007063772805908847 132392100010595659208863271)
          ·
            refine ⟨198588150015893488813294907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132392100010595659208863271 198588150015893488813294907)
            ·
              refine ⟨297882225023840233219942361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198588150015893488813294907 297882225023840233219942361)
              ·
                refine ⟨223411668767880174914956771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297882225023840233219942361 223411668767880174914956771)
                ·
                  refine ⟨335117503151820262372435157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223411668767880174914956771 335117503151820262372435157)
                  ·
                    refine ⟨7854316480120787399353949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 335117503151820262372435157 7854316480120787399353949)
                    ·
                      refine ⟨2945368680045295274757731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854316480120787399353949 2945368680045295274757731)
                      ·
                        rfl

theorem cell23_5736085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_5736085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736085 prefixEnd_5736085 := by exact prefixLift 5736085
  have htrace : WordTrace (prefixWord ++ tailWord_5736085) baseStart_5736085 baseEnd_5736085 := by
    simpa [prefixWord, tailWord_5736085, baseEnd_5736085] using wordTrace_append hprefix tailTrace_5736085
  have hstable : (prefixWord ++ tailWord_5736085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736085).length < 2 ^ (prefixWord ++ tailWord_5736085).sum := by decide
  have hdescent : baseEnd_5736085 < baseStart_5736085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736092 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 8]
def baseStart_5736092 : Nat := 118140960795 + 5736092 * 2 ^ 59
def prefixEnd_5736092 : Nat := 4983230072969 + 3 ^ 40 * 5736092 * 2
def baseEnd_5736092 : Nat := 327263586045541860818911

theorem tailTrace_5736092 : CollatzResearch.WordTrace tailWord_5736092 prefixEnd_5736092 327263586045541860818911 := by
  unfold tailWord_5736092
  simp only [CollatzResearch.WordTrace]
  refine ⟨104606231367562902682533265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139474975156750536910044353 104606231367562902682533265)
  ·
    refine ⟨78454673525672177011899949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104606231367562902682533265 78454673525672177011899949)
    ·
      refine ⟨29420502572127066379462481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78454673525672177011899949 29420502572127066379462481)
      ·
        refine ⟨22065376929095299784596861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29420502572127066379462481 22065376929095299784596861)
        ·
          refine ⟨8274516348410737419223823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22065376929095299784596861 8274516348410737419223823)
          ·
            refine ⟨12411774522616106128835735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274516348410737419223823 12411774522616106128835735)
            ·
              refine ⟨18617661783924159193253603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12411774522616106128835735 18617661783924159193253603)
              ·
                refine ⟨27926492675886238789880405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18617661783924159193253603 27926492675886238789880405)
                ·
                  refine ⟨327263586045541860818911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27926492675886238789880405 327263586045541860818911)
                  ·
                    rfl

theorem cell23_5736092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_5736092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736092 prefixEnd_5736092 := by exact prefixLift 5736092
  have htrace : WordTrace (prefixWord ++ tailWord_5736092) baseStart_5736092 baseEnd_5736092 := by
    simpa [prefixWord, tailWord_5736092, baseEnd_5736092] using wordTrace_append hprefix tailTrace_5736092
  have hstable : (prefixWord ++ tailWord_5736092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736092).length < 2 ^ (prefixWord ++ tailWord_5736092).sum := by decide
  have hdescent : baseEnd_5736092 < baseStart_5736092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736109 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 6]
def baseStart_5736109 : Nat := 118140960795 + 5736109 * 2 ^ 59
def prefixEnd_5736109 : Nat := 4983230072969 + 3 ^ 40 * 5736109 * 2
def baseEnd_5736109 : Nat := 327264555953444797873069

theorem tailTrace_5736109 : CollatzResearch.WordTrace tailWord_5736109 prefixEnd_5736109 327264555953444797873069 := by
  unfold tailWord_5736109
  simp only [CollatzResearch.WordTrace]
  refine ⟨209213082776064217268435381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139475388517376144845623587 209213082776064217268435381)
  ·
    refine ⟨19613726510256020368915817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 209213082776064217268435381 19613726510256020368915817)
    ·
      refine ⟨14710294882692015276686863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19613726510256020368915817 14710294882692015276686863)
      ·
        refine ⟨22065442324038022915030295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14710294882692015276686863 22065442324038022915030295)
        ·
          refine ⟨33098163486057034372545443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22065442324038022915030295 33098163486057034372545443)
          ·
            refine ⟨49647245229085551558818165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33098163486057034372545443 49647245229085551558818165)
            ·
              refine ⟨4654429240226770458639203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49647245229085551558818165 4654429240226770458639203)
              ·
                refine ⟨6981643860340155687958805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4654429240226770458639203 6981643860340155687958805)
                ·
                  refine ⟨327264555953444797873069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6981643860340155687958805 327264555953444797873069)
                  ·
                    rfl

theorem cell23_5736109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_5736109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736109 prefixEnd_5736109 := by exact prefixLift 5736109
  have htrace : WordTrace (prefixWord ++ tailWord_5736109) baseStart_5736109 baseEnd_5736109 := by
    simpa [prefixWord, tailWord_5736109, baseEnd_5736109] using wordTrace_append hprefix tailTrace_5736109
  have hstable : (prefixWord ++ tailWord_5736109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736109).length < 2 ^ (prefixWord ++ tailWord_5736109).sum := by decide
  have hdescent : baseEnd_5736109 < baseStart_5736109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736112 : List Nat := [2, 1, 1, 1, 2, 1, 5, 2, 1, 5, 2]
def baseStart_5736112 : Nat := 118140960795 + 5736112 * 2 ^ 59
def prefixEnd_5736112 : Nat := 4983230072969 + 3 ^ 40 * 5736112 * 2
def baseEnd_5736112 : Nat := 2945382544022966669120107

theorem tailTrace_5736112 : CollatzResearch.WordTrace tailWord_5736112 prefixEnd_5736112 2945382544022966669120107 := by
  unfold tailWord_5736112
  simp only [CollatzResearch.WordTrace]
  refine ⟨104606596097526674390397295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139475461463368899187196393 104606596097526674390397295)
  ·
    refine ⟨156909894146290011585595943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104606596097526674390397295 156909894146290011585595943)
    ·
      refine ⟨235364841219435017378393915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156909894146290011585595943 235364841219435017378393915)
      ·
        refine ⟨353047261829152526067590873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235364841219435017378393915 353047261829152526067590873)
        ·
          refine ⟨264785446371864394550693155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353047261829152526067590873 264785446371864394550693155)
          ·
            refine ⟨397178169557796591826039733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264785446371864394550693155 397178169557796591826039733)
            ·
              refine ⟨37235453396043430483691225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 397178169557796591826039733 37235453396043430483691225)
              ·
                refine ⟨27926590047032572862768419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37235453396043430483691225 27926590047032572862768419)
                ·
                  refine ⟨41889885070548859294152629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27926590047032572862768419 41889885070548859294152629)
                  ·
                    refine ⟨3927176725363955558826809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41889885070548859294152629 3927176725363955558826809)
                    ·
                      refine ⟨2945382544022966669120107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927176725363955558826809 2945382544022966669120107)
                      ·
                        rfl

theorem cell23_5736112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 2, 1, 5, 2].length) (baseStart_5736112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736112 prefixEnd_5736112 := by exact prefixLift 5736112
  have htrace : WordTrace (prefixWord ++ tailWord_5736112) baseStart_5736112 baseEnd_5736112 := by
    simpa [prefixWord, tailWord_5736112, baseEnd_5736112] using wordTrace_append hprefix tailTrace_5736112
  have hstable : (prefixWord ++ tailWord_5736112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736112).length < 2 ^ (prefixWord ++ tailWord_5736112).sum := by decide
  have hdescent : baseEnd_5736112 < baseStart_5736112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736119 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 3, 1, 3]
def baseStart_5736119 : Nat := 118140960795 + 5736119 * 2 ^ 59
def prefixEnd_5736119 : Nat := 4983230072969 + 3 ^ 40 * 5736119 * 2
def baseEnd_5736119 : Nat := 2945386138387548141732575

theorem tailTrace_5736119 : CollatzResearch.WordTrace tailWord_5736119 prefixEnd_5736119 2945386138387548141732575 := by
  unfold tailWord_5736119
  simp only [CollatzResearch.WordTrace]
  refine ⟨209213447506027988976299411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139475631670685325984199607 209213447506027988976299411)
  ·
    refine ⟨313820171259041983464449117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209213447506027988976299411 313820171259041983464449117)
    ·
      refine ⟨117682564222140743799168419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 313820171259041983464449117 117682564222140743799168419)
      ·
        refine ⟨176523846333211115698752629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117682564222140743799168419 176523846333211115698752629)
        ·
          refine ⟨16549110593738542096758059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 176523846333211115698752629 16549110593738542096758059)
          ·
            refine ⟨24823665890607813145137089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16549110593738542096758059 24823665890607813145137089)
            ·
              refine ⟨18617749417955859858852817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24823665890607813145137089 18617749417955859858852817)
              ·
                refine ⟨13963312063466894894139613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18617749417955859858852817 13963312063466894894139613)
                ·
                  refine ⟨5236242023800085585302355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13963312063466894894139613 5236242023800085585302355)
                  ·
                    refine ⟨7854363035700128377953533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5236242023800085585302355 7854363035700128377953533)
                    ·
                      refine ⟨2945386138387548141732575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7854363035700128377953533 2945386138387548141732575)
                      ·
                        rfl

theorem cell23_5736119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_5736119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736119 prefixEnd_5736119 := by exact prefixLift 5736119
  have htrace : WordTrace (prefixWord ++ tailWord_5736119) baseStart_5736119 baseEnd_5736119 := by
    simpa [prefixWord, tailWord_5736119, baseEnd_5736119] using wordTrace_append hprefix tailTrace_5736119
  have hstable : (prefixWord ++ tailWord_5736119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736119).length < 2 ^ (prefixWord ++ tailWord_5736119).sum := by decide
  have hdescent : baseEnd_5736119 < baseStart_5736119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736122 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 1, 5]
def baseStart_5736122 : Nat := 118140960795 + 5736122 * 2 ^ 59
def prefixEnd_5736122 : Nat := 4983230072969 + 3 ^ 40 * 5736122 * 2
def baseEnd_5736122 : Nat := 981795892943170543331687

theorem tailTrace_5736122 : CollatzResearch.WordTrace tailWord_5736122 prefixEnd_5736122 981795892943170543331687 := by
  unfold tailWord_5736122
  simp only [CollatzResearch.WordTrace]
  refine ⟨52303389231254280122164655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139475704616678080325772413 52303389231254280122164655)
  ·
    refine ⟨78455083846881420183246983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52303389231254280122164655 78455083846881420183246983)
    ·
      refine ⟨117682625770322130274870475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78455083846881420183246983 117682625770322130274870475)
      ·
        refine ⟨176523938655483195412305713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117682625770322130274870475 176523938655483195412305713)
        ·
          refine ⟨132392953991612396559229285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176523938655483195412305713 132392953991612396559229285)
          ·
            refine ⟨24823678873427324354855491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 132392953991612396559229285 24823678873427324354855491)
            ·
              refine ⟨37235518310140986532283237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24823678873427324354855491 37235518310140986532283237)
              ·
                refine ⟨6981659683151434974803107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37235518310140986532283237 6981659683151434974803107)
                ·
                  refine ⟨10472489524727152462204661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6981659683151434974803107 10472489524727152462204661)
                  ·
                    refine ⟨981795892943170543331687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10472489524727152462204661 981795892943170543331687)
                    ·
                      rfl

theorem cell23_5736122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_5736122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736122 prefixEnd_5736122 := by exact prefixLift 5736122
  have htrace : WordTrace (prefixWord ++ tailWord_5736122) baseStart_5736122 baseEnd_5736122 := by
    simpa [prefixWord, tailWord_5736122, baseEnd_5736122] using wordTrace_append hprefix tailTrace_5736122
  have hstable : (prefixWord ++ tailWord_5736122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736122).length < 2 ^ (prefixWord ++ tailWord_5736122).sum := by decide
  have hdescent : baseEnd_5736122 < baseStart_5736122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736135 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 3, 6]
def baseStart_5736135 : Nat := 118140960795 + 5736135 * 2 ^ 59
def prefixEnd_5736135 : Nat := 4983230072969 + 3 ^ 40 * 5736135 * 2
def baseEnd_5736135 : Nat := 981798118026006693044167

theorem tailTrace_5736135 : CollatzResearch.WordTrace tailWord_5736135 prefixEnd_5736135 981798118026006693044167 := by
  unfold tailWord_5736135
  simp only [CollatzResearch.WordTrace]
  refine ⟨209214031073970023708881859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 139476020715980015805921239 209214031073970023708881859)
  ·
    refine ⟨313821046610955035563322789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 209214031073970023708881859 313821046610955035563322789)
    ·
      refine ⟨58841446239554069168123023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 313821046610955035563322789 58841446239554069168123023)
      ·
        refine ⟨88262169359331103752184535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58841446239554069168123023 88262169359331103752184535)
        ·
          refine ⟨132393254038996655628276803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88262169359331103752184535 132393254038996655628276803)
          ·
            refine ⟨198589881058494983442415205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132393254038996655628276803 198589881058494983442415205)
            ·
              refine ⟨37235602698467809395452851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 198589881058494983442415205 37235602698467809395452851)
              ·
                refine ⟨55853404047701714093179277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37235602698467809395452851 55853404047701714093179277)
                ·
                  refine ⟨20945026517888142784942229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55853404047701714093179277 20945026517888142784942229)
                  ·
                    refine ⟨981798118026006693044167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20945026517888142784942229 981798118026006693044167)
                    ·
                      rfl

theorem cell23_5736135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_5736135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736135 prefixEnd_5736135 := by exact prefixLift 5736135
  have htrace : WordTrace (prefixWord ++ tailWord_5736135) baseStart_5736135 baseEnd_5736135 := by
    simpa [prefixWord, tailWord_5736135, baseEnd_5736135] using wordTrace_append hprefix tailTrace_5736135
  have hstable : (prefixWord ++ tailWord_5736135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736135).length < 2 ^ (prefixWord ++ tailWord_5736135).sum := by decide
  have hdescent : baseEnd_5736135 < baseStart_5736135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736146 : List Nat := [3, 2, 2, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_5736146 : Nat := 118140960795 + 5736146 * 2 ^ 59
def prefixEnd_5736146 : Nat := 4983230072969 + 3 ^ 40 * 5736146 * 2
def baseEnd_5736146 : Nat := 2945400002365219536094951

theorem tailTrace_5736146 : CollatzResearch.WordTrace tailWord_5736146 prefixEnd_5736146 2945400002365219536094951 := by
  unfold tailWord_5736146
  simp only [CollatzResearch.WordTrace]
  refine ⟨52303608069232543146883073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 139476288184620115058354861 52303608069232543146883073)
  ·
    refine ⟨39227706051924407360162305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52303608069232543146883073 39227706051924407360162305)
    ·
      refine ⟨29420779538943305520121729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39227706051924407360162305 29420779538943305520121729)
      ·
        refine ⟨22065584654207479140091297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29420779538943305520121729 22065584654207479140091297)
        ·
          refine ⟨16549188490655609355068473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22065584654207479140091297 16549188490655609355068473)
          ·
            refine ⟨12411891367991707016301355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16549188490655609355068473 12411891367991707016301355)
            ·
              refine ⟨18617837051987560524452033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12411891367991707016301355 18617837051987560524452033)
              ·
                refine ⟨13963377788990670393339025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18617837051987560524452033 13963377788990670393339025)
                ·
                  refine ⟨10472533341743002795004269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13963377788990670393339025 10472533341743002795004269)
                  ·
                    refine ⟨3927200003153626048126601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10472533341743002795004269 3927200003153626048126601)
                    ·
                      refine ⟨2945400002365219536094951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3927200003153626048126601 2945400002365219536094951)
                      ·
                        rfl

theorem cell23_5736146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_5736146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736146 prefixEnd_5736146 := by exact prefixLift 5736146
  have htrace : WordTrace (prefixWord ++ tailWord_5736146) baseStart_5736146 baseEnd_5736146 := by
    simpa [prefixWord, tailWord_5736146, baseEnd_5736146] using wordTrace_append hprefix tailTrace_5736146
  have hstable : (prefixWord ++ tailWord_5736146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736146).length < 2 ^ (prefixWord ++ tailWord_5736146).sum := by decide
  have hdescent : baseEnd_5736146 < baseStart_5736146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5736152 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 4, 4]
def baseStart_5736152 : Nat := 118140960795 + 5736152 * 2 ^ 59
def prefixEnd_5736152 : Nat := 4983230072969 + 3 ^ 40 * 5736152 * 2
def baseEnd_5736152 : Nat := 981801027749715504206641

theorem tailTrace_5736152 : CollatzResearch.WordTrace tailWord_5736152 prefixEnd_5736152 981801027749715504206641 := by
  unfold tailWord_5736152
  simp only [CollatzResearch.WordTrace]
  refine ⟨104607325557454217806125355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 139476434076605623741500473 104607325557454217806125355)
  ·
    refine ⟨156910988336181326709188033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104607325557454217806125355 156910988336181326709188033)
    ·
      refine ⟨117683241252135995031891025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156910988336181326709188033 117683241252135995031891025)
      ·
        refine ⟨88262430939101996273918269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117683241252135995031891025 88262430939101996273918269)
        ·
          refine ⟨33098411602163248602719351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88262430939101996273918269 33098411602163248602719351)
          ·
            refine ⟨49647617403244872904079027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33098411602163248602719351 49647617403244872904079027)
            ·
              refine ⟨74471426104867309356118541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49647617403244872904079027 74471426104867309356118541)
              ·
                refine ⟨27926784789325241008544453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74471426104867309356118541 27926784789325241008544453)
                ·
                  refine ⟨5236272147998482689102085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27926784789325241008544453 5236272147998482689102085)
                  ·
                    refine ⟨981801027749715504206641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5236272147998482689102085 981801027749715504206641)
                    ·
                      rfl

theorem cell23_5736152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 4, 4].length) (baseStart_5736152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5736152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5736152 prefixEnd_5736152 := by exact prefixLift 5736152
  have htrace : WordTrace (prefixWord ++ tailWord_5736152) baseStart_5736152 baseEnd_5736152 := by
    simpa [prefixWord, tailWord_5736152, baseEnd_5736152] using wordTrace_append hprefix tailTrace_5736152
  have hstable : (prefixWord ++ tailWord_5736152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5736152).length < 2 ^ (prefixWord ++ tailWord_5736152).sum := by decide
  have hdescent : baseEnd_5736152 < baseStart_5736152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5736152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
