import V185TrunkScan21Chunk099

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1215068 : List Nat := [2, 2, 4, 1, 4, 1, 1, 1, 5]
def baseStart_1215068 : Nat := 118140960795 + 1215068 * 2 ^ 59
def prefixEnd_1215068 : Nat := 4983230072969 + 3 ^ 40 * 1215068 * 2
def baseEnd_1215068 : Nat := 277295071954381010916449

theorem tailTrace_1215068 : CollatzResearch.WordTrace tailWord_1215068 prefixEnd_1215068 277295071954381010916449 := by
  unfold tailWord_1215068
  simp only [CollatzResearch.WordTrace]
  refine ⟨22158585381011813969114929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29544780508015751958819905 22158585381011813969114929)
  ·
    refine ⟨16618939035758860476836197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22158585381011813969114929 16618939035758860476836197)
    ·
      refine ⟨3116051069204786339406787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16618939035758860476836197 3116051069204786339406787)
      ·
        refine ⟨4674076603807179509110181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3116051069204786339406787 4674076603807179509110181)
        ·
          refine ⟨876389363213846157958159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4674076603807179509110181 876389363213846157958159)
          ·
            refine ⟨1314584044820769236937239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876389363213846157958159 1314584044820769236937239)
            ·
              refine ⟨1971876067231153855405859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1314584044820769236937239 1971876067231153855405859)
              ·
                refine ⟨2957814100846730783108789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971876067231153855405859 2957814100846730783108789)
                ·
                  refine ⟨277295071954381010916449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2957814100846730783108789 277295071954381010916449)
                  ·
                    rfl

theorem cell21_1215068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_1215068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215068 prefixEnd_1215068 := by exact prefixLift 1215068
  have htrace : WordTrace (prefixWord ++ tailWord_1215068) baseStart_1215068 baseEnd_1215068 := by
    simpa [prefixWord, tailWord_1215068, baseEnd_1215068] using wordTrace_append hprefix tailTrace_1215068
  have hstable : (prefixWord ++ tailWord_1215068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215068).length < 2 ^ (prefixWord ++ tailWord_1215068).sum := by decide
  have hdescent : baseEnd_1215068 < baseStart_1215068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215107 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 8]
def baseStart_1215107 : Nat := 118140960795 + 1215107 * 2 ^ 59
def prefixEnd_1215107 : Nat := 4983230072969 + 3 ^ 40 * 1215107 * 2
def baseEnd_1215107 : Nat := 277303972285725609766369

theorem tailTrace_1215107 : CollatzResearch.WordTrace tailWord_1215107 prefixEnd_1215107 277303972285725609766369 := by
  unfold tailWord_1215107
  simp only [CollatzResearch.WordTrace]
  refine ⟨44318593208882337598899575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29545728805921558399266383 44318593208882337598899575)
  ·
    refine ⟨66477889813323506398349363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44318593208882337598899575 66477889813323506398349363)
    ·
      refine ⟨99716834719985259597524045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66477889813323506398349363 99716834719985259597524045)
      ·
        refine ⟨37393813019994472349071517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99716834719985259597524045 37393813019994472349071517)
        ·
          refine ⟨14022679882497927130901819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37393813019994472349071517 14022679882497927130901819)
          ·
            refine ⟨21034019823746890696352729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14022679882497927130901819 21034019823746890696352729)
            ·
              refine ⟨15775514867810168022264547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21034019823746890696352729 15775514867810168022264547)
              ·
                refine ⟨23663272301715252033396821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15775514867810168022264547 23663272301715252033396821)
                ·
                  refine ⟨277303972285725609766369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23663272301715252033396821 277303972285725609766369)
                  ·
                    rfl

theorem cell21_1215107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_1215107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215107 prefixEnd_1215107 := by exact prefixLift 1215107
  have htrace : WordTrace (prefixWord ++ tailWord_1215107) baseStart_1215107 baseEnd_1215107 := by
    simpa [prefixWord, tailWord_1215107, baseEnd_1215107] using wordTrace_append hprefix tailTrace_1215107
  have hstable : (prefixWord ++ tailWord_1215107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215107).length < 2 ^ (prefixWord ++ tailWord_1215107).sum := by decide
  have hdescent : baseEnd_1215107 < baseStart_1215107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215155 : List Nat := [1, 1, 1, 2, 3, 5, 3, 5]
def baseStart_1215155 : Nat := 118140960795 + 1215155 * 2 ^ 59
def prefixEnd_1215155 : Nat := 4983230072969 + 3 ^ 40 * 1215155 * 2
def baseEnd_1215155 : Nat := 92438308846562730988757

theorem tailTrace_1215155 : CollatzResearch.WordTrace tailWord_1215155 prefixEnd_1215155 92438308846562730988757 := by
  unfold tailWord_1215155
  simp only [CollatzResearch.WordTrace]
  refine ⟨44320343912708441796646919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29546895941805627864431279 44320343912708441796646919)
  ·
    refine ⟨66480515869062662694970379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44320343912708441796646919 66480515869062662694970379)
    ·
      refine ⟨99720773803593994042455569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66480515869062662694970379 99720773803593994042455569)
      ·
        refine ⟨74790580352695495531841677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99720773803593994042455569 74790580352695495531841677)
        ·
          refine ⟨28046467632260810824440629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74790580352695495531841677 28046467632260810824440629)
          ·
            refine ⟨2629356340524451014791309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28046467632260810824440629 2629356340524451014791309)
            ·
              refine ⟨986008627696669130546741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2629356340524451014791309 986008627696669130546741)
              ·
                refine ⟨92438308846562730988757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 986008627696669130546741 92438308846562730988757)
                ·
                  rfl

theorem cell21_1215155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 5].length) (baseStart_1215155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215155 prefixEnd_1215155 := by exact prefixLift 1215155
  have htrace : WordTrace (prefixWord ++ tailWord_1215155) baseStart_1215155 baseEnd_1215155 := by
    simpa [prefixWord, tailWord_1215155, baseEnd_1215155] using wordTrace_append hprefix tailTrace_1215155
  have hstable : (prefixWord ++ tailWord_1215155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215155).length < 2 ^ (prefixWord ++ tailWord_1215155).sum := by decide
  have hdescent : baseEnd_1215155 < baseStart_1215155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215290 : List Nat := [3, 1, 1, 1, 6, 9]
def baseStart_1215290 : Nat := 118140960795 + 1215290 * 2 ^ 59
def prefixEnd_1215290 : Nat := 4983230072969 + 3 ^ 40 * 1215290 * 2
def baseEnd_1215290 : Nat := 10272064273294739193185

theorem tailTrace_1215290 : CollatzResearch.WordTrace tailWord_1215290 prefixEnd_1215290 10272064273294739193185 := by
  unfold tailWord_1215290
  simp only [CollatzResearch.WordTrace]
  refine ⟨11081316941804839963202831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29550178511479573235207549 11081316941804839963202831)
  ·
    refine ⟨16621975412707259944804247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11081316941804839963202831 16621975412707259944804247)
    ·
      refine ⟨24932963119060889917206371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16621975412707259944804247 24932963119060889917206371)
      ·
        refine ⟨37399444678591334875809557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24932963119060889917206371 37399444678591334875809557)
        ·
          refine ⟨1753098969308968822303573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37399444678591334875809557 1753098969308968822303573)
          ·
            refine ⟨10272064273294739193185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1753098969308968822303573 10272064273294739193185)
            ·
              rfl

theorem cell21_1215290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 9].length) (baseStart_1215290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215290 prefixEnd_1215290 := by exact prefixLift 1215290
  have htrace : WordTrace (prefixWord ++ tailWord_1215290) baseStart_1215290 baseEnd_1215290 := by
    simpa [prefixWord, tailWord_1215290, baseEnd_1215290] using wordTrace_append hprefix tailTrace_1215290
  have hstable : (prefixWord ++ tailWord_1215290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215290).length < 2 ^ (prefixWord ++ tailWord_1215290).sum := by decide
  have hdescent : baseEnd_1215290 < baseStart_1215290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215321 : List Nat := [1, 2, 1, 2, 2, 5, 1, 2, 5]
def baseStart_1215321 : Nat := 118140960795 + 1215321 * 2 ^ 59
def prefixEnd_1215321 : Nat := 4983230072969 + 3 ^ 40 * 1215321 * 2
def baseEnd_1215321 : Nat := 277352810001308793199265

theorem tailTrace_1215321 : CollatzResearch.WordTrace tailWord_1215321 prefixEnd_1215321 277352810001308793199265 := by
  unfold tailWord_1215321
  simp only [CollatzResearch.WordTrace]
  refine ⟨44326398430107052147189817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29550932286738034764793211 44326398430107052147189817)
  ·
    refine ⟨33244798822580289110392363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44326398430107052147189817 33244798822580289110392363)
    ·
      refine ⟨49867198233870433665588545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33244798822580289110392363 49867198233870433665588545)
      ·
        refine ⟨37400398675402825249191409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49867198233870433665588545 37400398675402825249191409)
        ·
          refine ⟨28050299006552118936893557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37400398675402825249191409 28050299006552118936893557)
          ·
            refine ⟨2629715531864261150333771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28050299006552118936893557 2629715531864261150333771)
            ·
              refine ⟨3944573297796391725500657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2629715531864261150333771 3944573297796391725500657)
              ·
                refine ⟨2958429973347293794125493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3944573297796391725500657 2958429973347293794125493)
                ·
                  refine ⟨277352810001308793199265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2958429973347293794125493 277352810001308793199265)
                  ·
                    rfl

theorem cell21_1215321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_1215321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215321 prefixEnd_1215321 := by exact prefixLift 1215321
  have htrace : WordTrace (prefixWord ++ tailWord_1215321) baseStart_1215321 baseEnd_1215321 := by
    simpa [prefixWord, tailWord_1215321, baseEnd_1215321] using wordTrace_append hprefix tailTrace_1215321
  have hstable : (prefixWord ++ tailWord_1215321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215321).length < 2 ^ (prefixWord ++ tailWord_1215321).sum := by decide
  have hdescent : baseEnd_1215321 < baseStart_1215321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215324 : List Nat := [2, 2, 4, 2, 1, 2, 3, 5]
def baseStart_1215324 : Nat := 118140960795 + 1215324 * 2 ^ 59
def prefixEnd_1215324 : Nat := 4983230072969 + 3 ^ 40 * 1215324 * 2
def baseEnd_1215324 : Nat := 92451164880727151549753

theorem tailTrace_1215324 : CollatzResearch.WordTrace tailWord_1215324 prefixEnd_1215324 92451164880727151549753 := by
  unfold tailWord_1215324
  simp only [CollatzResearch.WordTrace]
  refine ⟨22163253924548091829774513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29551005232730789106366017 22163253924548091829774513)
  ·
    refine ⟨16622440443411068872330885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22163253924548091829774513 16622440443411068872330885)
    ·
      refine ⟨3116707583139575413562041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16622440443411068872330885 3116707583139575413562041)
      ·
        refine ⟨2337530687354681560171531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3116707583139575413562041 2337530687354681560171531)
        ·
          refine ⟨3506296031032022340257297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2337530687354681560171531 3506296031032022340257297)
          ·
            refine ⟨2629722023274016755192973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3506296031032022340257297 2629722023274016755192973)
            ·
              refine ⟨986145758727756283197365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2629722023274016755192973 986145758727756283197365)
              ·
                refine ⟨92451164880727151549753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 986145758727756283197365 92451164880727151549753)
                ·
                  rfl

theorem cell21_1215324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_1215324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215324 prefixEnd_1215324 := by exact prefixLift 1215324
  have htrace : WordTrace (prefixWord ++ tailWord_1215324) baseStart_1215324 baseEnd_1215324 := by
    simpa [prefixWord, tailWord_1215324, baseEnd_1215324] using wordTrace_append hprefix tailTrace_1215324
  have hstable : (prefixWord ++ tailWord_1215324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215324).length < 2 ^ (prefixWord ++ tailWord_1215324).sum := by decide
  have hdescent : baseEnd_1215324 < baseStart_1215324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215369 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 4]
def baseStart_1215369 : Nat := 118140960795 + 1215369 * 2 ^ 59
def prefixEnd_1215369 : Nat := 4983230072969 + 3 ^ 40 * 1215369 * 2
def baseEnd_1215369 : Nat := 277363764255271376399167

theorem tailTrace_1215369 : CollatzResearch.WordTrace tailWord_1215369 prefixEnd_1215369 277363764255271376399167 := by
  unfold tailWord_1215369
  simp only [CollatzResearch.WordTrace]
  refine ⟨44328149133933156344937161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29552099422622104229958107 44328149133933156344937161)
  ·
    refine ⟨33246111850449867258702871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44328149133933156344937161 33246111850449867258702871)
    ·
      refine ⟨49869167775674800888054307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33246111850449867258702871 49869167775674800888054307)
      ·
        refine ⟨74803751663512201332081461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49869167775674800888054307 74803751663512201332081461)
        ·
          refine ⟨7012851718454268874882637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74803751663512201332081461 7012851718454268874882637)
          ·
            refine ⟨2629819394420350828080989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7012851718454268874882637 2629819394420350828080989)
            ·
              refine ⟨986182272907631560530371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2629819394420350828080989 986182272907631560530371)
              ·
                refine ⟨1479273409361447340795557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986182272907631560530371 1479273409361447340795557)
                ·
                  refine ⟨277363764255271376399167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1479273409361447340795557 277363764255271376399167)
                  ·
                    rfl

theorem cell21_1215369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_1215369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215369 prefixEnd_1215369 := by exact prefixLift 1215369
  have htrace : WordTrace (prefixWord ++ tailWord_1215369) baseStart_1215369 baseEnd_1215369 := by
    simpa [prefixWord, tailWord_1215369, baseEnd_1215369] using wordTrace_append hprefix tailTrace_1215369
  have hstable : (prefixWord ++ tailWord_1215369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215369).length < 2 ^ (prefixWord ++ tailWord_1215369).sum := by decide
  have hdescent : baseEnd_1215369 < baseStart_1215369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215521 : List Nat := [1, 2, 3, 2, 3, 3, 1, 2, 4]
def baseStart_1215521 : Nat := 118140960795 + 1215521 * 2 ^ 59
def prefixEnd_1215521 : Nat := 4983230072969 + 3 ^ 40 * 1215521 * 2
def baseEnd_1215521 : Nat := 277398452726152889865523

theorem tailTrace_1215521 : CollatzResearch.WordTrace tailWord_1215521 prefixEnd_1215521 277398452726152889865523 := by
  unfold tailWord_1215521
  simp only [CollatzResearch.WordTrace]
  refine ⟨44333693029382486304470417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29555795352921657536313611 44333693029382486304470417)
  ·
    refine ⟨33250269772036864728352813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44333693029382486304470417 33250269772036864728352813)
    ·
      refine ⟨12468851164513824273132305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33250269772036864728352813 12468851164513824273132305)
      ·
        refine ⟨9351638373385368204849229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12468851164513824273132305 9351638373385368204849229)
        ·
          refine ⟨3506864390019513076818461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9351638373385368204849229 3506864390019513076818461)
          ·
            refine ⟨1315074146257317403806923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3506864390019513076818461 1315074146257317403806923)
            ·
              refine ⟨1972611219385976105710385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315074146257317403806923 1972611219385976105710385)
              ·
                refine ⟨1479458414539482079282789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1972611219385976105710385 1479458414539482079282789)
                ·
                  refine ⟨277398452726152889865523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1479458414539482079282789 277398452726152889865523)
                  ·
                    rfl

theorem cell21_1215521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_1215521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215521 prefixEnd_1215521 := by exact prefixLift 1215521
  have htrace : WordTrace (prefixWord ++ tailWord_1215521) baseStart_1215521 baseEnd_1215521 := by
    simpa [prefixWord, tailWord_1215521, baseEnd_1215521] using wordTrace_append hprefix tailTrace_1215521
  have hstable : (prefixWord ++ tailWord_1215521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215521).length < 2 ^ (prefixWord ++ tailWord_1215521).sum := by decide
  have hdescent : baseEnd_1215521 < baseStart_1215521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215549 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 5]
def baseStart_1215549 : Nat := 118140960795 + 1215549 * 2 ^ 59
def prefixEnd_1215549 : Nat := 4983230072969 + 3 ^ 40 * 1215549 * 2
def baseEnd_1215549 : Nat := 277404842707631063398799

theorem tailTrace_1215549 : CollatzResearch.WordTrace tailWord_1215549 prefixEnd_1215549 277404842707631063398799 := by
  unfold tailWord_1215549
  simp only [CollatzResearch.WordTrace]
  refine ⟨44334714273281047086489701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29556476182187364724326467 44334714273281047086489701)
  ·
    refine ⟨8312758926240196328716819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44334714273281047086489701 8312758926240196328716819)
    ·
      refine ⟨12469138389360294493075229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8312758926240196328716819 12469138389360294493075229)
      ·
        refine ⟨4675926896010110434903211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12469138389360294493075229 4675926896010110434903211)
        ·
          refine ⟨7013890344015165652354817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4675926896010110434903211 7013890344015165652354817)
          ·
            refine ⟨5260417758011374239266113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7013890344015165652354817 5260417758011374239266113)
            ·
              refine ⟨3945313318508530679449585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5260417758011374239266113 3945313318508530679449585)
              ·
                refine ⟨2958984988881398009587189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3945313318508530679449585 2958984988881398009587189)
                ·
                  refine ⟨277404842707631063398799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2958984988881398009587189 277404842707631063398799)
                  ·
                    rfl

theorem cell21_1215549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_1215549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215549 prefixEnd_1215549 := by exact prefixLift 1215549
  have htrace : WordTrace (prefixWord ++ tailWord_1215549) baseStart_1215549 baseEnd_1215549 := by
    simpa [prefixWord, tailWord_1215549, baseEnd_1215549] using wordTrace_append hprefix tailTrace_1215549
  have hstable : (prefixWord ++ tailWord_1215549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215549).length < 2 ^ (prefixWord ++ tailWord_1215549).sum := by decide
  have hdescent : baseEnd_1215549 < baseStart_1215549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215580 : List Nat := [2, 2, 4, 1, 1, 1, 2, 4, 4]
def baseStart_1215580 : Nat := 118140960795 + 1215580 * 2 ^ 59
def prefixEnd_1215580 : Nat := 4983230072969 + 3 ^ 40 * 1215580 * 2
def baseEnd_1215580 : Nat := 277411917329981898382069

theorem tailTrace_1215580 : CollatzResearch.WordTrace tailWord_1215580 prefixEnd_1215580 277411917329981898382069 := by
  unfold tailWord_1215580
  simp only [CollatzResearch.WordTrace]
  refine ⟨22167922468084369690434097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29557229957445826253912129 22167922468084369690434097)
  ·
    refine ⟨16625941851063277267825573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22167922468084369690434097 16625941851063277267825573)
    ·
      refine ⟨3117364097074364487717295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16625941851063277267825573 3117364097074364487717295)
      ·
        refine ⟨4676046145611546731575943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3117364097074364487717295 4676046145611546731575943)
        ·
          refine ⟨7014069218417320097363915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4676046145611546731575943 7014069218417320097363915)
          ·
            refine ⟨10521103827625980146045873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7014069218417320097363915 10521103827625980146045873)
            ·
              refine ⟨7890827870719485109534405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10521103827625980146045873 7890827870719485109534405)
              ·
                refine ⟨1479530225759903458037701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7890827870719485109534405 1479530225759903458037701)
                ·
                  refine ⟨277411917329981898382069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1479530225759903458037701 277411917329981898382069)
                  ·
                    rfl

theorem cell21_1215580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_1215580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215580 prefixEnd_1215580 := by exact prefixLift 1215580
  have htrace : WordTrace (prefixWord ++ tailWord_1215580) baseStart_1215580 baseEnd_1215580 := by
    simpa [prefixWord, tailWord_1215580, baseEnd_1215580] using wordTrace_append hprefix tailTrace_1215580
  have hstable : (prefixWord ++ tailWord_1215580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215580).length < 2 ^ (prefixWord ++ tailWord_1215580).sum := by decide
  have hdescent : baseEnd_1215580 < baseStart_1215580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215594 : List Nat := [3, 1, 3, 2, 2, 1, 1, 8]
def baseStart_1215594 : Nat := 118140960795 + 1215594 * 2 ^ 59
def prefixEnd_1215594 : Nat := 4983230072969 + 3 ^ 40 * 1215594 * 2
def baseEnd_1215594 : Nat := 92471704106906995049569

theorem tailTrace_1215594 : CollatzResearch.WordTrace tailWord_1215594 prefixEnd_1215594 92471704106906995049569 := by
  unfold tailWord_1215594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11084088889529504942969459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29557570372078679847918557 11084088889529504942969459)
  ·
    refine ⟨16626133334294257414454189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11084088889529504942969459 16626133334294257414454189)
    ·
      refine ⟨6234800000360346530420321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16626133334294257414454189 6234800000360346530420321)
      ·
        refine ⟨4676100000270259897815241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6234800000360346530420321 4676100000270259897815241)
        ·
          refine ⟨3507075000202694923361431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4676100000270259897815241 3507075000202694923361431)
          ·
            refine ⟨5260612500304042385042147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3507075000202694923361431 5260612500304042385042147)
            ·
              refine ⟨7890918750456063577563221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5260612500304042385042147 7890918750456063577563221)
              ·
                refine ⟨92471704106906995049569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7890918750456063577563221 92471704106906995049569)
                ·
                  rfl

theorem cell21_1215594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_1215594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215594 prefixEnd_1215594 := by exact prefixLift 1215594
  have htrace : WordTrace (prefixWord ++ tailWord_1215594) baseStart_1215594 baseEnd_1215594 := by
    simpa [prefixWord, tailWord_1215594, baseEnd_1215594] using wordTrace_append hprefix tailTrace_1215594
  have hstable : (prefixWord ++ tailWord_1215594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215594).length < 2 ^ (prefixWord ++ tailWord_1215594).sum := by decide
  have hdescent : baseEnd_1215594 < baseStart_1215594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215597 : List Nat := [1, 5, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1215597 : Nat := 118140960795 + 1215597 * 2 ^ 59
def prefixEnd_1215597 : Nat := 4983230072969 + 3 ^ 40 * 1215597 * 2
def baseEnd_1215597 : Nat := 277415796961593646598701

theorem tailTrace_1215597 : CollatzResearch.WordTrace tailWord_1215597 prefixEnd_1215597 277415796961593646598701 := by
  unfold tailWord_1215597
  simp only [CollatzResearch.WordTrace]
  refine ⟨44336464977107151284237045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29557643318071434189491363 44336464977107151284237045)
  ·
    refine ⟨4156543591603795432897223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44336464977107151284237045 4156543591603795432897223)
    ·
      refine ⟨6234815387405693149345835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4156543591603795432897223 6234815387405693149345835)
      ·
        refine ⟨9352223081108539724018753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6234815387405693149345835 9352223081108539724018753)
        ·
          refine ⟨7014167310831404793014065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9352223081108539724018753 7014167310831404793014065)
          ·
            refine ⟨5260625483123553594760549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7014167310831404793014065 5260625483123553594760549)
            ·
              refine ⟨986367278085666299017603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5260625483123553594760549 986367278085666299017603)
              ·
                refine ⟨1479550917128499448526405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986367278085666299017603 1479550917128499448526405)
                ·
                  refine ⟨277415796961593646598701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1479550917128499448526405 277415796961593646598701)
                  ·
                    rfl

theorem cell21_1215597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1215597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215597 prefixEnd_1215597 := by exact prefixLift 1215597
  have htrace : WordTrace (prefixWord ++ tailWord_1215597) baseStart_1215597 baseEnd_1215597 := by
    simpa [prefixWord, tailWord_1215597, baseEnd_1215597] using wordTrace_append hprefix tailTrace_1215597
  have hstable : (prefixWord ++ tailWord_1215597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215597).length < 2 ^ (prefixWord ++ tailWord_1215597).sum := by decide
  have hdescent : baseEnd_1215597 < baseStart_1215597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215608 : List Nat := [2, 1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_1215608 : Nat := 118140960795 + 1215608 * 2 ^ 59
def prefixEnd_1215608 : Nat := 4983230072969 + 3 ^ 40 * 1215608 * 2
def baseEnd_1215608 : Nat := 277418307311460071915345

theorem tailTrace_1215608 : CollatzResearch.WordTrace tailWord_1215608 prefixEnd_1215608 277418307311460071915345 := by
  unfold tailWord_1215608
  simp only [CollatzResearch.WordTrace]
  refine ⟨22168433090033650081443739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29557910786711533441924985 22168433090033650081443739)
  ·
    refine ⟨33252649635050475122165609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22168433090033650081443739 33252649635050475122165609)
    ·
      refine ⟨24939487226287856341624207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33252649635050475122165609 24939487226287856341624207)
      ·
        refine ⟨37409230839431784512436311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24939487226287856341624207 37409230839431784512436311)
        ·
          refine ⟨56113846259147676768654467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37409230839431784512436311 56113846259147676768654467)
          ·
            refine ⟨84170769388721515152981701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56113846259147676768654467 84170769388721515152981701)
            ·
              refine ⟨15782019260385284091184069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84170769388721515152981701 15782019260385284091184069)
              ·
                refine ⟨2959128611322240767097013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15782019260385284091184069 2959128611322240767097013)
                ·
                  refine ⟨277418307311460071915345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2959128611322240767097013 277418307311460071915345)
                  ·
                    rfl

theorem cell21_1215608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_1215608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215608 prefixEnd_1215608 := by exact prefixLift 1215608
  have htrace : WordTrace (prefixWord ++ tailWord_1215608) baseStart_1215608 baseEnd_1215608 := by
    simpa [prefixWord, tailWord_1215608, baseEnd_1215608] using wordTrace_append hprefix tailTrace_1215608
  have hstable : (prefixWord ++ tailWord_1215608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215608).length < 2 ^ (prefixWord ++ tailWord_1215608).sum := by decide
  have hdescent : baseEnd_1215608 < baseStart_1215608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215701 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 5]
def baseStart_1215701 : Nat := 118140960795 + 1215701 * 2 ^ 59
def prefixEnd_1215701 : Nat := 4983230072969 + 3 ^ 40 * 1215701 * 2
def baseEnd_1215701 : Nat := 277439531178512576865155

theorem tailTrace_1215701 : CollatzResearch.WordTrace tailWord_1215701 prefixEnd_1215701 277439531178512576865155 := by
  unfold tailWord_1215701
  simp only [CollatzResearch.WordTrace]
  refine ⟨44340258168730377046022957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29560172112486918030681971 44340258168730377046022957)
  ·
    refine ⟨16627596813273891392258609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44340258168730377046022957 16627596813273891392258609)
    ·
      refine ⟨12470697609955418544193957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16627596813273891392258609 12470697609955418544193957)
      ·
        refine ⟨2338255801866640977036367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12470697609955418544193957 2338255801866640977036367)
        ·
          refine ⟨3507383702799961465554551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2338255801866640977036367 3507383702799961465554551)
          ·
            refine ⟨5261075554199942198331827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3507383702799961465554551 5261075554199942198331827)
            ·
              refine ⟨7891613331299913297497741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5261075554199942198331827 7891613331299913297497741)
              ·
                refine ⟨2959354999237467486561653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7891613331299913297497741 2959354999237467486561653)
                ·
                  refine ⟨277439531178512576865155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2959354999237467486561653 277439531178512576865155)
                  ·
                    rfl

theorem cell21_1215701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_1215701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215701 prefixEnd_1215701 := by exact prefixLift 1215701
  have htrace : WordTrace (prefixWord ++ tailWord_1215701) baseStart_1215701 baseEnd_1215701 := by
    simpa [prefixWord, tailWord_1215701, baseEnd_1215701] using wordTrace_append hprefix tailTrace_1215701
  have hstable : (prefixWord ++ tailWord_1215701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215701).length < 2 ^ (prefixWord ++ tailWord_1215701).sum := by decide
  have hdescent : baseEnd_1215701 < baseStart_1215701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215814 : List Nat := [6, 1, 1, 3, 2, 1, 1, 6]
def baseStart_1215814 : Nat := 118140960795 + 1215814 * 2 ^ 59
def prefixEnd_1215814 : Nat := 4983230072969 + 3 ^ 40 * 1215814 * 2
def baseEnd_1215814 : Nat := 92488439772683163827197

theorem tailTrace_1215814 : CollatzResearch.WordTrace tailWord_1215814 prefixEnd_1215814 92488439772683163827197 := by
  unfold tailWord_1215814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385761863041281167027703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29562919744880664896590997 1385761863041281167027703)
  ·
    refine ⟨2078642794561921750541555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1385761863041281167027703 2078642794561921750541555)
    ·
      refine ⟨3117964191842882625812333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2078642794561921750541555 3117964191842882625812333)
      ·
        refine ⟨1169236571941080984679625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3117964191842882625812333 1169236571941080984679625)
        ·
          refine ⟨876927428955810738509719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1169236571941080984679625 876927428955810738509719)
          ·
            refine ⟨1315391143433716107764579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876927428955810738509719 1315391143433716107764579)
            ·
              refine ⟨1973086715150574161646869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315391143433716107764579 1973086715150574161646869)
              ·
                refine ⟨92488439772683163827197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1973086715150574161646869 92488439772683163827197)
                ·
                  rfl

theorem cell21_1215814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_1215814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215814 prefixEnd_1215814 := by exact prefixLift 1215814
  have htrace : WordTrace (prefixWord ++ tailWord_1215814) baseStart_1215814 baseEnd_1215814 := by
    simpa [prefixWord, tailWord_1215814, baseEnd_1215814] using wordTrace_append hprefix tailTrace_1215814
  have hstable : (prefixWord ++ tailWord_1215814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215814).length < 2 ^ (prefixWord ++ tailWord_1215814).sum := by decide
  have hdescent : baseEnd_1215814 < baseStart_1215814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215884 : List Nat := [2, 2, 1, 2, 1, 3, 5, 1, 4]
def baseStart_1215884 : Nat := 118140960795 + 1215884 * 2 ^ 59
def prefixEnd_1215884 : Nat := 4983230072969 + 3 ^ 40 * 1215884 * 2
def baseEnd_1215884 : Nat := 277481294271744925314781

theorem tailTrace_1215884 : CollatzResearch.WordTrace tailWord_1215884 prefixEnd_1215884 277481294271744925314781 := by
  unfold tailWord_1215884
  simp only [CollatzResearch.WordTrace]
  refine ⟨22173466363533699649967353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29564621818044932866623137 22173466363533699649967353)
  ·
    refine ⟨16630099772650274737475515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22173466363533699649967353 16630099772650274737475515)
    ·
      refine ⟨24945149658975412106213273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16630099772650274737475515 24945149658975412106213273)
      ·
        refine ⟨18708862244231559079659955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24945149658975412106213273 18708862244231559079659955)
        ·
          refine ⟨28063293366347338619489933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18708862244231559079659955 28063293366347338619489933)
          ·
            refine ⟨10523735012380251982308725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28063293366347338619489933 10523735012380251982308725)
            ·
              refine ⟨986600157410648623341443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10523735012380251982308725 986600157410648623341443)
              ·
                refine ⟨1479900236115972935012165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986600157410648623341443 1479900236115972935012165)
                ·
                  refine ⟨277481294271744925314781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1479900236115972935012165 277481294271744925314781)
                  ·
                    rfl

theorem cell21_1215884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_1215884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215884 prefixEnd_1215884 := by exact prefixLift 1215884
  have htrace : WordTrace (prefixWord ++ tailWord_1215884) baseStart_1215884 baseEnd_1215884 := by
    simpa [prefixWord, tailWord_1215884, baseEnd_1215884] using wordTrace_append hprefix tailTrace_1215884
  have hstable : (prefixWord ++ tailWord_1215884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215884).length < 2 ^ (prefixWord ++ tailWord_1215884).sum := by decide
  have hdescent : baseEnd_1215884 < baseStart_1215884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215943 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 4]
def baseStart_1215943 : Nat := 118140960795 + 1215943 * 2 ^ 59
def prefixEnd_1215943 : Nat := 4983230072969 + 3 ^ 40 * 1215943 * 2
def baseEnd_1215943 : Nat := 277494758875573933831327

theorem tailTrace_1215943 : CollatzResearch.WordTrace tailWord_1215943 prefixEnd_1215943 277494758875573933831327 := by
  unfold tailWord_1215943
  simp only [CollatzResearch.WordTrace]
  refine ⟨44349084633853652376332483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29566056422569101584221655 44349084633853652376332483)
  ·
    refine ⟨66523626950780478564498725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44349084633853652376332483 66523626950780478564498725)
    ·
      refine ⟨12473180053271339730843511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66523626950780478564498725 12473180053271339730843511)
      ·
        refine ⟨18709770079907009596265267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12473180053271339730843511 18709770079907009596265267)
        ·
          refine ⟨28064655119860514394397901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18709770079907009596265267 28064655119860514394397901)
          ·
            refine ⟨10524245669947692897899213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28064655119860514394397901 10524245669947692897899213)
            ·
              refine ⟨3946592126230384836712205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10524245669947692897899213 3946592126230384836712205)
              ·
                refine ⟨1479972047336394313767077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3946592126230384836712205 1479972047336394313767077)
                ·
                  refine ⟨277494758875573933831327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1479972047336394313767077 277494758875573933831327)
                  ·
                    rfl

theorem cell21_1215943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 4].length) (baseStart_1215943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215943 prefixEnd_1215943 := by exact prefixLift 1215943
  have htrace : WordTrace (prefixWord ++ tailWord_1215943) baseStart_1215943 baseEnd_1215943 := by
    simpa [prefixWord, tailWord_1215943, baseEnd_1215943] using wordTrace_append hprefix tailTrace_1215943
  have hstable : (prefixWord ++ tailWord_1215943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215943).length < 2 ^ (prefixWord ++ tailWord_1215943).sum := by decide
  have hdescent : baseEnd_1215943 < baseStart_1215943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1215957 : List Nat := [1, 3, 2, 3, 1, 1, 1, 9]
def baseStart_1215957 : Nat := 118140960795 + 1215957 * 2 ^ 59
def prefixEnd_1215957 : Nat := 4983230072969 + 3 ^ 40 * 1215957 * 2
def baseEnd_1215957 : Nat := 92499317955437673532655

theorem tailTrace_1215957 : CollatzResearch.WordTrace tailWord_1215957 prefixEnd_1215957 92499317955437673532655 := by
  unfold tailWord_1215957
  simp only [CollatzResearch.WordTrace]
  refine ⟨44349595255802932767342125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29566396837201955178228083 44349595255802932767342125)
  ·
    refine ⟨16631098220926099787753297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44349595255802932767342125 16631098220926099787753297)
    ·
      refine ⟨12473323665694574840814973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16631098220926099787753297 12473323665694574840814973)
      ·
        refine ⟨4677496374635465565305615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12473323665694574840814973 4677496374635465565305615)
        ·
          refine ⟨7016244561953198347958423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4677496374635465565305615 7016244561953198347958423)
          ·
            refine ⟨10524366842929797521937635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7016244561953198347958423 10524366842929797521937635)
            ·
              refine ⟨15786550264394696282906453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10524366842929797521937635 15786550264394696282906453)
              ·
                refine ⟨92499317955437673532655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15786550264394696282906453 92499317955437673532655)
                ·
                  rfl

theorem cell21_1215957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 9].length) (baseStart_1215957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1215957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1215957 prefixEnd_1215957 := by exact prefixLift 1215957
  have htrace : WordTrace (prefixWord ++ tailWord_1215957) baseStart_1215957 baseEnd_1215957 := by
    simpa [prefixWord, tailWord_1215957, baseEnd_1215957] using wordTrace_append hprefix tailTrace_1215957
  have hstable : (prefixWord ++ tailWord_1215957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1215957).length < 2 ^ (prefixWord ++ tailWord_1215957).sum := by decide
  have hdescent : baseEnd_1215957 < baseStart_1215957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1215957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216033 : List Nat := [1, 2, 3, 2, 2, 3, 8]
def baseStart_1216033 : Nat := 118140960795 + 1216033 * 2 ^ 59
def prefixEnd_1216033 : Nat := 4983230072969 + 3 ^ 40 * 1216033 * 2
def baseEnd_1216033 : Nat := 30835033122417086370127

theorem tailTrace_1216033 : CollatzResearch.WordTrace tailWord_1216033 prefixEnd_1216033 30835033122417086370127 := by
  unfold tailWord_1216033
  simp only [CollatzResearch.WordTrace]
  refine ⟨44352367203527597747108753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29568244802351731831405835 44352367203527597747108753)
  ·
    refine ⟨33264275402645698310331565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44352367203527597747108753 33264275402645698310331565)
    ·
      refine ⟨12474103275992136866374337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33264275402645698310331565 12474103275992136866374337)
      ·
        refine ⟨9355577456994102649780753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12474103275992136866374337 9355577456994102649780753)
        ·
          refine ⟨7016683092745576987335565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9355577456994102649780753 7016683092745576987335565)
          ·
            refine ⟨2631256159779591370250837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7016683092745576987335565 2631256159779591370250837)
            ·
              refine ⟨30835033122417086370127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2631256159779591370250837 30835033122417086370127)
              ·
                rfl

theorem cell21_1216033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 8].length) (baseStart_1216033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216033 prefixEnd_1216033 := by exact prefixLift 1216033
  have htrace : WordTrace (prefixWord ++ tailWord_1216033) baseStart_1216033 baseEnd_1216033 := by
    simpa [prefixWord, tailWord_1216033, baseEnd_1216033] using wordTrace_append hprefix tailTrace_1216033
  have hstable : (prefixWord ++ tailWord_1216033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216033).length < 2 ^ (prefixWord ++ tailWord_1216033).sum := by decide
  have hdescent : baseEnd_1216033 < baseStart_1216033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216112 : List Nat := [2, 1, 1, 1, 6, 1, 4, 1, 4]
def baseStart_1216112 : Nat := 118140960795 + 1216112 * 2 ^ 59
def prefixEnd_1216112 : Nat := 4983230072969 + 3 ^ 40 * 1216112 * 2
def baseEnd_1216112 : Nat := 277533326978067195514315

theorem tailTrace_1216112 : CollatzResearch.WordTrace tailWord_1216112 prefixEnd_1216112 277533326978067195514315 := by
  unfold tailWord_1216112
  simp only [CollatzResearch.WordTrace]
  refine ⟨22177624285120697119617295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29570165713494262826156393 22177624285120697119617295)
  ·
    refine ⟨33266436427681045679425943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22177624285120697119617295 33266436427681045679425943)
    ·
      refine ⟨49899654641521568519138915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33266436427681045679425943 49899654641521568519138915)
      ·
        refine ⟨74849481962282352778708373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49899654641521568519138915 74849481962282352778708373)
        ·
          refine ⟨3508569466981985286501955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74849481962282352778708373 3508569466981985286501955)
          ·
            refine ⟨5262854200472977929752933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508569466981985286501955 5262854200472977929752933)
            ·
              refine ⟨986785162588683361828675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5262854200472977929752933 986785162588683361828675)
              ·
                refine ⟨1480177743883025042743013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 986785162588683361828675 1480177743883025042743013)
                ·
                  refine ⟨277533326978067195514315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480177743883025042743013 277533326978067195514315)
                  ·
                    rfl

theorem cell21_1216112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 4].length) (baseStart_1216112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216112 prefixEnd_1216112 := by exact prefixLift 1216112
  have htrace : WordTrace (prefixWord ++ tailWord_1216112) baseStart_1216112 baseEnd_1216112 := by
    simpa [prefixWord, tailWord_1216112, baseEnd_1216112] using wordTrace_append hprefix tailTrace_1216112
  have hstable : (prefixWord ++ tailWord_1216112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216112).length < 2 ^ (prefixWord ++ tailWord_1216112).sum := by decide
  have hdescent : baseEnd_1216112 < baseStart_1216112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216123 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 7]
def baseStart_1216123 : Nat := 118140960795 + 1216123 * 2 ^ 59
def prefixEnd_1216123 : Nat := 4983230072969 + 3 ^ 40 * 1216123 * 2
def baseEnd_1216123 : Nat := 277535837327933620830959

theorem tailTrace_1216123 : CollatzResearch.WordTrace tailWord_1216123 prefixEnd_1216123 277535837327933620830959 := by
  unfold tailWord_1216123
  simp only [CollatzResearch.WordTrace]
  refine ⟨44355649773201543117885023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29570433182134362078590015 44355649773201543117885023)
  ·
    refine ⟨66533474659802314676827535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44355649773201543117885023 66533474659802314676827535)
    ·
      refine ⟨99800211989703472015241303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66533474659802314676827535 99800211989703472015241303)
      ·
        refine ⟨149700317984555208022861955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99800211989703472015241303 149700317984555208022861955)
        ·
          refine ⟨224550476976832812034292933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149700317984555208022861955 224550476976832812034292933)
          ·
            refine ⟨42103214433156152256429925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224550476976832812034292933 42103214433156152256429925)
            ·
              refine ⟨7894352706216778548080611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42103214433156152256429925 7894352706216778548080611)
              ·
                refine ⟨11841529059325167822120917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7894352706216778548080611 11841529059325167822120917)
                ·
                  refine ⟨277535837327933620830959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11841529059325167822120917 277535837327933620830959)
                  ·
                    rfl

theorem cell21_1216123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_1216123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216123 prefixEnd_1216123 := by exact prefixLift 1216123
  have htrace : WordTrace (prefixWord ++ tailWord_1216123) baseStart_1216123 baseEnd_1216123 := by
    simpa [prefixWord, tailWord_1216123, baseEnd_1216123] using wordTrace_append hprefix tailTrace_1216123
  have hstable : (prefixWord ++ tailWord_1216123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216123).length < 2 ^ (prefixWord ++ tailWord_1216123).sum := by decide
  have hdescent : baseEnd_1216123 < baseStart_1216123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216174 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_1216174 : Nat := 118140960795 + 1216174 * 2 ^ 59
def prefixEnd_1216174 : Nat := 4983230072969 + 3 ^ 40 * 1216174 * 2
def baseEnd_1216174 : Nat := 277547476222768865480855

theorem tailTrace_1216174 : CollatzResearch.WordTrace tailWord_1216174 prefixEnd_1216174 277547476222768865480855 := by
  unfold tailWord_1216174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5544688737002097353498947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29571673264011185885327717 5544688737002097353498947)
  ·
    refine ⟨8317033105503146030248421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5544688737002097353498947 8317033105503146030248421)
    ·
      refine ⟨1559443707281839880671579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8317033105503146030248421 1559443707281839880671579)
      ·
        refine ⟨2339165560922759821007369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559443707281839880671579 2339165560922759821007369)
        ·
          refine ⟨1754374170692069865755527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2339165560922759821007369 1754374170692069865755527)
          ·
            refine ⟨2631561256038104798633291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754374170692069865755527 2631561256038104798633291)
            ·
              refine ⟨3947341884057157197949937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2631561256038104798633291 3947341884057157197949937)
              ·
                refine ⟨2960506413042867898462453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3947341884057157197949937 2960506413042867898462453)
                ·
                  refine ⟨277547476222768865480855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2960506413042867898462453 277547476222768865480855)
                  ·
                    rfl

theorem cell21_1216174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_1216174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216174 prefixEnd_1216174 := by exact prefixLift 1216174
  have htrace : WordTrace (prefixWord ++ tailWord_1216174) baseStart_1216174 baseEnd_1216174 := by
    simpa [prefixWord, tailWord_1216174, baseEnd_1216174] using wordTrace_append hprefix tailTrace_1216174
  have hstable : (prefixWord ++ tailWord_1216174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216174).length < 2 ^ (prefixWord ++ tailWord_1216174).sum := by decide
  have hdescent : baseEnd_1216174 < baseStart_1216174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216199 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 7]
def baseStart_1216199 : Nat := 118140960795 + 1216199 * 2 ^ 59
def prefixEnd_1216199 : Nat := 4983230072969 + 3 ^ 40 * 1216199 * 2
def baseEnd_1216199 : Nat := 277553181563374377564137

theorem tailTrace_1216199 : CollatzResearch.WordTrace tailWord_1216199 prefixEnd_1216199 277553181563374377564137 := by
  unfold tailWord_1216199
  simp only [CollatzResearch.WordTrace]
  refine ⟨44358421720926208097651651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29572281147284138731767767 44358421720926208097651651)
  ·
    refine ⟨66537632581389312146477477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44358421720926208097651651 66537632581389312146477477)
    ·
      refine ⟨12475806109010496027464527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66537632581389312146477477 12475806109010496027464527)
      ·
        refine ⟨18713709163515744041196791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12475806109010496027464527 18713709163515744041196791)
        ·
          refine ⟨28070563745273616061795187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18713709163515744041196791 28070563745273616061795187)
          ·
            refine ⟨42105845617910424092692781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28070563745273616061795187 42105845617910424092692781)
            ·
              refine ⟨15789692106716409034759793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42105845617910424092692781 15789692106716409034759793)
              ·
                refine ⟨11842269080037306776069845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15789692106716409034759793 11842269080037306776069845)
                ·
                  refine ⟨277553181563374377564137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11842269080037306776069845 277553181563374377564137)
                  ·
                    rfl

theorem cell21_1216199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 7].length) (baseStart_1216199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216199 prefixEnd_1216199 := by exact prefixLift 1216199
  have htrace : WordTrace (prefixWord ++ tailWord_1216199) baseStart_1216199 baseEnd_1216199 := by
    simpa [prefixWord, tailWord_1216199, baseEnd_1216199] using wordTrace_append hprefix tailTrace_1216199
  have hstable : (prefixWord ++ tailWord_1216199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216199).length < 2 ^ (prefixWord ++ tailWord_1216199).sum := by decide
  have hdescent : baseEnd_1216199 < baseStart_1216199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216205 : List Nat := [1, 6, 2, 1, 1, 1, 3, 2, 4]
def baseStart_1216205 : Nat := 118140960795 + 1216205 * 2 ^ 59
def prefixEnd_1216205 : Nat := 4983230072969 + 3 ^ 40 * 1216205 * 2
def baseEnd_1216205 : Nat := 277554550845119700464125

theorem tailTrace_1216205 : CollatzResearch.WordTrace tailWord_1216205 prefixEnd_1216205 277554550845119700464125 := by
  unfold tailWord_1216205
  simp only [CollatzResearch.WordTrace]
  refine ⟨44358640558904471122370069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29572427039269647414913379 44358640558904471122370069)
  ·
    refine ⟨2079311276198647083861097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44358640558904471122370069 2079311276198647083861097)
    ·
      refine ⟨1559483457148985312895823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2079311276198647083861097 1559483457148985312895823)
      ·
        refine ⟨2339225185723477969343735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559483457148985312895823 2339225185723477969343735)
        ·
          refine ⟨3508837778585216954015603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2339225185723477969343735 3508837778585216954015603)
          ·
            refine ⟨5263256667877825431023405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508837778585216954015603 5263256667877825431023405)
            ·
              refine ⟨1973721250454184536633777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5263256667877825431023405 1973721250454184536633777)
              ·
                refine ⟨1480290937840638402475333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973721250454184536633777 1480290937840638402475333)
                ·
                  refine ⟨277554550845119700464125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480290937840638402475333 277554550845119700464125)
                  ·
                    rfl

theorem cell21_1216205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_1216205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216205 prefixEnd_1216205 := by exact prefixLift 1216205
  have htrace : WordTrace (prefixWord ++ tailWord_1216205) baseStart_1216205 baseEnd_1216205 := by
    simpa [prefixWord, tailWord_1216205, baseEnd_1216205] using wordTrace_append hprefix tailTrace_1216205
  have hstable : (prefixWord ++ tailWord_1216205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216205).length < 2 ^ (prefixWord ++ tailWord_1216205).sum := by decide
  have hdescent : baseEnd_1216205 < baseStart_1216205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216216 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 5]
def baseStart_1216216 : Nat := 118140960795 + 1216216 * 2 ^ 59
def prefixEnd_1216216 : Nat := 4983230072969 + 3 ^ 40 * 1216216 * 2
def baseEnd_1216216 : Nat := 277557061194986125780769

theorem tailTrace_1216216 : CollatzResearch.WordTrace tailWord_1216216 prefixEnd_1216216 277557061194986125780769 := by
  unfold tailWord_1216216
  simp only [CollatzResearch.WordTrace]
  refine ⟨22179520880932310000510251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29572694507909746667347001 22179520880932310000510251)
  ·
    refine ⟨33269281321398465000765377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22179520880932310000510251 33269281321398465000765377)
    ·
      refine ⟨24951960991048848750574033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33269281321398465000765377 24951960991048848750574033)
      ·
        refine ⟨18713970743286636562930525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24951960991048848750574033 18713970743286636562930525)
        ·
          refine ⟨7017739028732488711098947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18713970743286636562930525 7017739028732488711098947)
          ·
            refine ⟨10526608543098733066648421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7017739028732488711098947 10526608543098733066648421)
            ·
              refine ⟨1973739101831012449996579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10526608543098733066648421 1973739101831012449996579)
              ·
                refine ⟨2960608652746518674994869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1973739101831012449996579 2960608652746518674994869)
                ·
                  refine ⟨277557061194986125780769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2960608652746518674994869 277557061194986125780769)
                  ·
                    rfl

theorem cell21_1216216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_1216216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216216 prefixEnd_1216216 := by exact prefixLift 1216216
  have htrace : WordTrace (prefixWord ++ tailWord_1216216) baseStart_1216216 baseEnd_1216216 := by
    simpa [prefixWord, tailWord_1216216, baseEnd_1216216] using wordTrace_append hprefix tailTrace_1216216
  have hstable : (prefixWord ++ tailWord_1216216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216216).length < 2 ^ (prefixWord ++ tailWord_1216216).sum := by decide
  have hdescent : baseEnd_1216216 < baseStart_1216216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216275 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 5]
def baseStart_1216275 : Nat := 118140960795 + 1216275 * 2 ^ 59
def prefixEnd_1216275 : Nat := 4983230072969 + 3 ^ 40 * 1216275 * 2
def baseEnd_1216275 : Nat := 277570525798815134297315

theorem tailTrace_1216275 : CollatzResearch.WordTrace tailWord_1216275 prefixEnd_1216275 277570525798815134297315 := by
  unfold tailWord_1216275
  simp only [CollatzResearch.WordTrace]
  refine ⟨44361193668650873077418279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29574129112433915384945519 44361193668650873077418279)
  ·
    refine ⟨66541790502976309616127419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44361193668650873077418279 66541790502976309616127419)
    ·
      refine ⟨99812685754464464424191129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66541790502976309616127419 99812685754464464424191129)
      ·
        refine ⟨74859514315848348318143347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99812685754464464424191129 74859514315848348318143347)
        ·
          refine ⟨112289271473772522477215021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74859514315848348318143347 112289271473772522477215021)
          ·
            refine ⟨42108476802664695928955633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112289271473772522477215021 42108476802664695928955633)
            ·
              refine ⟨31581357601998521946716725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42108476802664695928955633 31581357601998521946716725)
              ·
                refine ⟨2960752275187361432504693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31581357601998521946716725 2960752275187361432504693)
                ·
                  refine ⟨277570525798815134297315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2960752275187361432504693 277570525798815134297315)
                  ·
                    rfl

theorem cell21_1216275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 5].length) (baseStart_1216275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216275 prefixEnd_1216275 := by exact prefixLift 1216275
  have htrace : WordTrace (prefixWord ++ tailWord_1216275) baseStart_1216275 baseEnd_1216275 := by
    simpa [prefixWord, tailWord_1216275, baseEnd_1216275] using wordTrace_append hprefix tailTrace_1216275
  have hstable : (prefixWord ++ tailWord_1216275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216275).length < 2 ^ (prefixWord ++ tailWord_1216275).sum := by decide
  have hdescent : baseEnd_1216275 < baseStart_1216275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216323 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 4]
def baseStart_1216323 : Nat := 118140960795 + 1216323 * 2 ^ 59
def prefixEnd_1216323 : Nat := 4983230072969 + 3 ^ 40 * 1216323 * 2
def baseEnd_1216323 : Nat := 277581480052777717497217

theorem tailTrace_1216323 : CollatzResearch.WordTrace tailWord_1216323 prefixEnd_1216323 277581480052777717497217 := by
  unfold tailWord_1216323
  simp only [CollatzResearch.WordTrace]
  refine ⟨44362944372476977275165623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29575296248317984850110415 44362944372476977275165623)
  ·
    refine ⟨66544416558715465912748435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44362944372476977275165623 66544416558715465912748435)
    ·
      refine ⟨99816624838073198869122653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66544416558715465912748435 99816624838073198869122653)
      ·
        refine ⟨37431234314277449575920995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99816624838073198869122653 37431234314277449575920995)
        ·
          refine ⟨56146851471416174363881493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37431234314277449575920995 56146851471416174363881493)
          ·
            refine ⟨2631883662722633173306945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56146851471416174363881493 2631883662722633173306945)
            ·
              refine ⟨1973912747041974879980209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2631883662722633173306945 1973912747041974879980209)
              ·
                refine ⟨1480434560281481159985157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973912747041974879980209 1480434560281481159985157)
                ·
                  refine ⟨277581480052777717497217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480434560281481159985157 277581480052777717497217)
                  ·
                    rfl

theorem cell21_1216323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 4].length) (baseStart_1216323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216323 prefixEnd_1216323 := by exact prefixLift 1216323
  have htrace : WordTrace (prefixWord ++ tailWord_1216323) baseStart_1216323 baseEnd_1216323 := by
    simpa [prefixWord, tailWord_1216323, baseEnd_1216323] using wordTrace_append hprefix tailTrace_1216323
  have hstable : (prefixWord ++ tailWord_1216323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216323).length < 2 ^ (prefixWord ++ tailWord_1216323).sum := by decide
  have hdescent : baseEnd_1216323 < baseStart_1216323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216337 : List Nat := [1, 2, 2, 1, 5, 1, 3, 6]
def baseStart_1216337 : Nat := 118140960795 + 1216337 * 2 ^ 59
def prefixEnd_1216337 : Nat := 4983230072969 + 3 ^ 40 * 1216337 * 2
def baseEnd_1216337 : Nat := 92528225014505601421285

theorem tailTrace_1216337 : CollatzResearch.WordTrace tailWord_1216337 prefixEnd_1216337 92528225014505601421285 := by
  unfold tailWord_1216337
  simp only [CollatzResearch.WordTrace]
  refine ⟨44363454994426257666175265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29575636662950838444116843 44363454994426257666175265)
  ·
    refine ⟨33272591245819693249631449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44363454994426257666175265 33272591245819693249631449)
    ·
      refine ⟨24954443434364769937223587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33272591245819693249631449 24954443434364769937223587)
      ·
        refine ⟨37431665151547154905835381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24954443434364769937223587 37431665151547154905835381)
        ·
          refine ⟨3509218607957545772422067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37431665151547154905835381 3509218607957545772422067)
          ·
            refine ⟨5263827911936318658633101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3509218607957545772422067 5263827911936318658633101)
            ·
              refine ⟨1973935466976119496987413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5263827911936318658633101 1973935466976119496987413)
              ·
                refine ⟨92528225014505601421285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1973935466976119496987413 92528225014505601421285)
                ·
                  rfl

theorem cell21_1216337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 6].length) (baseStart_1216337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216337 prefixEnd_1216337 := by exact prefixLift 1216337
  have htrace : WordTrace (prefixWord ++ tailWord_1216337) baseStart_1216337 baseEnd_1216337 := by
    simpa [prefixWord, tailWord_1216337, baseEnd_1216337] using wordTrace_append hprefix tailTrace_1216337
  have hstable : (prefixWord ++ tailWord_1216337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216337).length < 2 ^ (prefixWord ++ tailWord_1216337).sum := by decide
  have hdescent : baseEnd_1216337 < baseStart_1216337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216351 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 7]
def baseStart_1216351 : Nat := 118140960795 + 1216351 * 2 ^ 59
def prefixEnd_1216351 : Nat := 4983230072969 + 3 ^ 40 * 1216351 * 2
def baseEnd_1216351 : Nat := 277587870034255891030493

theorem tailTrace_1216351 : CollatzResearch.WordTrace tailWord_1216351 prefixEnd_1216351 277587870034255891030493 := by
  unfold tailWord_1216351
  simp only [CollatzResearch.WordTrace]
  refine ⟨44363965616375538057184907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29575977077583692038123271 44363965616375538057184907)
  ·
    refine ⟨66545948424563307085777361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44363965616375538057184907 66545948424563307085777361)
    ·
      refine ⟨49909461318422480314333021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66545948424563307085777361 49909461318422480314333021)
      ·
        refine ⟨18716047994408430117874883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49909461318422480314333021 18716047994408430117874883)
        ·
          refine ⟨28074071991612645176812325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18716047994408430117874883 28074071991612645176812325)
          ·
            refine ⟨5263888498427370970652311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28074071991612645176812325 5263888498427370970652311)
            ·
              refine ⟨7895832747641056455978467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5263888498427370970652311 7895832747641056455978467)
              ·
                refine ⟨11843749121461584683967701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7895832747641056455978467 11843749121461584683967701)
                ·
                  refine ⟨277587870034255891030493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11843749121461584683967701 277587870034255891030493)
                  ·
                    rfl

theorem cell21_1216351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_1216351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216351 prefixEnd_1216351 := by exact prefixLift 1216351
  have htrace : WordTrace (prefixWord ++ tailWord_1216351) baseStart_1216351 baseEnd_1216351 := by
    simpa [prefixWord, tailWord_1216351, baseEnd_1216351] using wordTrace_append hprefix tailTrace_1216351
  have hstable : (prefixWord ++ tailWord_1216351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216351).length < 2 ^ (prefixWord ++ tailWord_1216351).sum := by decide
  have hdescent : baseEnd_1216351 < baseStart_1216351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216374 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1216374 : Nat := 118140960795 + 1216374 * 2 ^ 59
def prefixEnd_1216374 : Nat := 4983230072969 + 3 ^ 40 * 1216374 * 2
def baseEnd_1216374 : Nat := 277593118947612962147113

theorem tailTrace_1216374 : CollatzResearch.WordTrace tailWord_1216374 prefixEnd_1216374 277593118947612962147113 := by
  unfold tailWord_1216374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2772800280955763311579511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29576536330194808656848117 2772800280955763311579511)
  ·
    refine ⟨4159200421433644967369267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2772800280955763311579511 4159200421433644967369267)
    ·
      refine ⟨6238800632150467451053901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4159200421433644967369267 6238800632150467451053901)
      ·
        refine ⟨2339550237056425294145213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6238800632150467451053901 2339550237056425294145213)
        ·
          refine ⟨877331338896159485304455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2339550237056425294145213 877331338896159485304455)
          ·
            refine ⟨1315997008344239227956683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 877331338896159485304455 1315997008344239227956683)
            ·
              refine ⟨1973995512516358841935025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1315997008344239227956683 1973995512516358841935025)
              ·
                refine ⟨1480496634387269131451269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1973995512516358841935025 1480496634387269131451269)
                ·
                  refine ⟨277593118947612962147113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480496634387269131451269 277593118947612962147113)
                  ·
                    rfl

theorem cell21_1216374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1216374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216374 prefixEnd_1216374 := by exact prefixLift 1216374
  have htrace : WordTrace (prefixWord ++ tailWord_1216374) baseStart_1216374 baseEnd_1216374 := by
    simpa [prefixWord, tailWord_1216374, baseEnd_1216374] using wordTrace_append hprefix tailTrace_1216374
  have hstable : (prefixWord ++ tailWord_1216374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216374).length < 2 ^ (prefixWord ++ tailWord_1216374).sum := by decide
  have hdescent : baseEnd_1216374 < baseStart_1216374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216396 : List Nat := [2, 2, 1, 2, 1, 2, 1, 10]
def baseStart_1216396 : Nat := 118140960795 + 1216396 * 2 ^ 59
def prefixEnd_1216396 : Nat := 4983230072969 + 3 ^ 40 * 1216396 * 2
def baseEnd_1216396 : Nat := 92532713215781937593467

theorem tailTrace_1216396 : CollatzResearch.WordTrace tailWord_1216396 prefixEnd_1216396 92532713215781937593467 := by
  unfold tailWord_1216396
  simp only [CollatzResearch.WordTrace]
  refine ⟨22182803450606255371286521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29577071267475007161715361 22182803450606255371286521)
  ·
    refine ⟨16637102587954691528464891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22182803450606255371286521 16637102587954691528464891)
    ·
      refine ⟨24955653881932037292697337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16637102587954691528464891 24955653881932037292697337)
      ·
        refine ⟨18716740411449027969523003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24955653881932037292697337 18716740411449027969523003)
        ·
          refine ⟨28075110617173541954284505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18716740411449027969523003 28075110617173541954284505)
          ·
            refine ⟨21056332962880156465713379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28075110617173541954284505 21056332962880156465713379)
            ·
              refine ⟨31584499444320234698570069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21056332962880156465713379 31584499444320234698570069)
              ·
                refine ⟨92532713215781937593467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31584499444320234698570069 92532713215781937593467)
                ·
                  rfl

theorem cell21_1216396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 10].length) (baseStart_1216396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216396 prefixEnd_1216396 := by exact prefixLift 1216396
  have htrace : WordTrace (prefixWord ++ tailWord_1216396) baseStart_1216396 baseEnd_1216396 := by
    simpa [prefixWord, tailWord_1216396, baseEnd_1216396] using wordTrace_append hprefix tailTrace_1216396
  have hstable : (prefixWord ++ tailWord_1216396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216396).length < 2 ^ (prefixWord ++ tailWord_1216396).sum := by decide
  have hdescent : baseEnd_1216396 < baseStart_1216396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216413 : List Nat := [1, 4, 2, 1, 2, 3, 1, 7]
def baseStart_1216413 : Nat := 118140960795 + 1216413 * 2 ^ 59
def prefixEnd_1216413 : Nat := 4983230072969 + 3 ^ 40 * 1216413 * 2
def baseEnd_1216413 : Nat := 92534006426319186999011

theorem tailTrace_1216413 : CollatzResearch.WordTrace tailWord_1216413 prefixEnd_1216413 92534006426319186999011 := by
  unfold tailWord_1216413
  simp only [CollatzResearch.WordTrace]
  refine ⟨44366226942150922645941893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29577484628100615097294595 44366226942150922645941893)
  ·
    refine ⟨8318667551653297996114105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44366226942150922645941893 8318667551653297996114105)
    ·
      refine ⟨6239000663739973497085579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8318667551653297996114105 6239000663739973497085579)
      ·
        refine ⟨9358500995609960245628369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6239000663739973497085579 9358500995609960245628369)
        ·
          refine ⟨7018875746707470184221277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9358500995609960245628369 7018875746707470184221277)
          ·
            refine ⟨2632078405015301319082979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7018875746707470184221277 2632078405015301319082979)
            ·
              refine ⟨3948117607522951978624469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632078405015301319082979 3948117607522951978624469)
              ·
                refine ⟨92534006426319186999011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3948117607522951978624469 92534006426319186999011)
                ·
                  rfl

theorem cell21_1216413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 7].length) (baseStart_1216413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216413 prefixEnd_1216413 := by exact prefixLift 1216413
  have htrace : WordTrace (prefixWord ++ tailWord_1216413) baseStart_1216413 baseEnd_1216413 := by
    simpa [prefixWord, tailWord_1216413, baseEnd_1216413] using wordTrace_append hprefix tailTrace_1216413
  have hstable : (prefixWord ++ tailWord_1216413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216413).length < 2 ^ (prefixWord ++ tailWord_1216413).sum := by decide
  have hdescent : baseEnd_1216413 < baseStart_1216413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216436 : List Nat := [2, 5, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1216436 : Nat := 118140960795 + 1216436 * 2 ^ 59
def prefixEnd_1216436 : Nat := 4983230072969 + 3 ^ 40 * 1216436 * 2
def baseEnd_1216436 : Nat := 277607268192314632113653

theorem tailTrace_1216436 : CollatzResearch.WordTrace tailWord_1216436 prefixEnd_1216436 277607268192314632113653 := by
  unfold tailWord_1216436
  simp only [CollatzResearch.WordTrace]
  refine ⟨22183532910533798787014581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29578043880711731716019441 22183532910533798787014581)
  ·
    refine ⟨2079706210362543636282617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22183532910533798787014581 2079706210362543636282617)
    ·
      refine ⟨1559779657771907727211963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2079706210362543636282617 1559779657771907727211963)
      ·
        refine ⟨2339669486657861590817945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1559779657771907727211963 2339669486657861590817945)
        ·
          refine ⟨1754752114993396193113459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2339669486657861590817945 1754752114993396193113459)
          ·
            refine ⟨2632128172490094289670189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754752114993396193113459 2632128172490094289670189)
            ·
              refine ⟨987048064683785358626321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2632128172490094289670189 987048064683785358626321)
              ·
                refine ⟨740286048512839018969741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 987048064683785358626321 740286048512839018969741)
                ·
                  refine ⟨277607268192314632113653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740286048512839018969741 277607268192314632113653)
                  ·
                    rfl

theorem cell21_1216436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1216436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216436 prefixEnd_1216436 := by exact prefixLift 1216436
  have htrace : WordTrace (prefixWord ++ tailWord_1216436) baseStart_1216436 baseEnd_1216436 := by
    simpa [prefixWord, tailWord_1216436, baseEnd_1216436] using wordTrace_append hprefix tailTrace_1216436
  have hstable : (prefixWord ++ tailWord_1216436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216436).length < 2 ^ (prefixWord ++ tailWord_1216436).sum := by decide
  have hdescent : baseEnd_1216436 < baseStart_1216436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216472 : List Nat := [2, 1, 2, 2, 2, 2, 1, 9]
def baseStart_1216472 : Nat := 118140960795 + 1216472 * 2 ^ 59
def prefixEnd_1216472 : Nat := 4983230072969 + 3 ^ 40 * 1216472 * 2
def baseEnd_1216472 : Nat := 92538494627595523171193

theorem tailTrace_1216472 : CollatzResearch.WordTrace tailWord_1216472 prefixEnd_1216472 92538494627595523171193 := by
  unfold tailWord_1216472
  simp only [CollatzResearch.WordTrace]
  refine ⟨22184189424468587861169835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29578919232624783814893113 22184189424468587861169835)
  ·
    refine ⟨33276284136702881791754753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22184189424468587861169835 33276284136702881791754753)
    ·
      refine ⟨24957213102527161343816065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33276284136702881791754753 24957213102527161343816065)
      ·
        refine ⟨18717909826895371007862049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24957213102527161343816065 18717909826895371007862049)
        ·
          refine ⟨14038432370171528255896537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18717909826895371007862049 14038432370171528255896537)
          ·
            refine ⟨10528824277628646191922403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14038432370171528255896537 10528824277628646191922403)
            ·
              refine ⟨15793236416442969287883605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10528824277628646191922403 15793236416442969287883605)
              ·
                refine ⟨92538494627595523171193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15793236416442969287883605 92538494627595523171193)
                ·
                  rfl

theorem cell21_1216472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 9].length) (baseStart_1216472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216472 prefixEnd_1216472 := by exact prefixLift 1216472
  have htrace : WordTrace (prefixWord ++ tailWord_1216472) baseStart_1216472 baseEnd_1216472 := by
    simpa [prefixWord, tailWord_1216472, baseEnd_1216472] using wordTrace_append hprefix tailTrace_1216472
  have hstable : (prefixWord ++ tailWord_1216472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216472).length < 2 ^ (prefixWord ++ tailWord_1216472).sum := by decide
  have hdescent : baseEnd_1216472 < baseStart_1216472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216568 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 4]
def baseStart_1216568 : Nat := 118140960795 + 1216568 * 2 ^ 59
def prefixEnd_1216568 : Nat := 4983230072969 + 3 ^ 40 * 1216568 * 2
def baseEnd_1216568 : Nat := 277637392390711735913383

theorem tailTrace_1216568 : CollatzResearch.WordTrace tailWord_1216568 prefixEnd_1216568 277637392390711735913383 := by
  unfold tailWord_1216568
  simp only [CollatzResearch.WordTrace]
  refine ⟨22185940128294692058917179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29581253504392922745222905 22185940128294692058917179)
  ·
    refine ⟨33278910192442038088375769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22185940128294692058917179 33278910192442038088375769)
    ·
      refine ⟨24959182644331528566281827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33278910192442038088375769 24959182644331528566281827)
      ·
        refine ⟨37438773966497292849422741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24959182644331528566281827 37438773966497292849422741)
        ·
          refine ⟨1754942529679560602316691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37438773966497292849422741 1754942529679560602316691)
          ·
            refine ⟨2632413794519340903475037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1754942529679560602316691 2632413794519340903475037)
            ·
              refine ⟨987155172944752838803139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2632413794519340903475037 987155172944752838803139)
              ·
                refine ⟨1480732759417129258204709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987155172944752838803139 1480732759417129258204709)
                ·
                  refine ⟨277637392390711735913383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480732759417129258204709 277637392390711735913383)
                  ·
                    rfl

theorem cell21_1216568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_1216568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216568 prefixEnd_1216568 := by exact prefixLift 1216568
  have htrace : WordTrace (prefixWord ++ tailWord_1216568) baseStart_1216568 baseEnd_1216568 := by
    simpa [prefixWord, tailWord_1216568, baseEnd_1216568] using wordTrace_append hprefix tailTrace_1216568
  have hstable : (prefixWord ++ tailWord_1216568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216568).length < 2 ^ (prefixWord ++ tailWord_1216568).sum := by decide
  have hdescent : baseEnd_1216568 < baseStart_1216568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216582 : List Nat := [6, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1216582 : Nat := 118140960795 + 1216582 * 2 ^ 59
def prefixEnd_1216582 : Nat := 4983230072969 + 3 ^ 40 * 1216582 * 2
def baseEnd_1216582 : Nat := 92546862460483607560007

theorem tailTrace_1216582 : CollatzResearch.WordTrace tailWord_1216582 prefixEnd_1216582 92546862460483607560007 := by
  unfold tailWord_1216582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1386637214954333265901375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29581593919025776339229333 1386637214954333265901375)
  ·
    refine ⟨2079955822431499898852063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1386637214954333265901375 2079955822431499898852063)
    ·
      refine ⟨3119933733647249848278095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2079955822431499898852063 3119933733647249848278095)
      ·
        refine ⟨4679900600470874772417143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3119933733647249848278095 4679900600470874772417143)
        ·
          refine ⟨7019850900706312158625715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4679900600470874772417143 7019850900706312158625715)
          ·
            refine ⟨10529776351059468237938573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7019850900706312158625715 10529776351059468237938573)
            ·
              refine ⟨3948666131647300589226965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10529776351059468237938573 3948666131647300589226965)
              ·
                refine ⟨92546862460483607560007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3948666131647300589226965 92546862460483607560007)
                ·
                  rfl

theorem cell21_1216582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1216582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216582 prefixEnd_1216582 := by exact prefixLift 1216582
  have htrace : WordTrace (prefixWord ++ tailWord_1216582) baseStart_1216582 baseEnd_1216582 := by
    simpa [prefixWord, tailWord_1216582, baseEnd_1216582] using wordTrace_append hprefix tailTrace_1216582
  have hstable : (prefixWord ++ tailWord_1216582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216582).length < 2 ^ (prefixWord ++ tailWord_1216582).sum := by decide
  have hdescent : baseEnd_1216582 < baseStart_1216582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216624 : List Nat := [2, 1, 1, 1, 5, 2, 1, 8]
def baseStart_1216624 : Nat := 118140960795 + 1216624 * 2 ^ 59
def prefixEnd_1216624 : Nat := 4983230072969 + 3 ^ 40 * 1216624 * 2
def baseEnd_1216624 : Nat := 92550057451222694326645

theorem tailTrace_1216624 : CollatzResearch.WordTrace tailWord_1216624 prefixEnd_1216624 92550057451222694326645 := by
  unfold tailWord_1216624
  simp only [CollatzResearch.WordTrace]
  refine ⟨22186961372193252840936463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29582615162924337121248617 22186961372193252840936463)
  ·
    refine ⟨33280442058289879261404695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22186961372193252840936463 33280442058289879261404695)
    ·
      refine ⟨49920663087434818892107043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33280442058289879261404695 49920663087434818892107043)
      ·
        refine ⟨74880994631152228338160565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49920663087434818892107043 74880994631152228338160565)
        ·
          refine ⟨7020093246670521406702553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74880994631152228338160565 7020093246670521406702553)
          ·
            refine ⟨5265069935002891055026915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7020093246670521406702553 5265069935002891055026915)
            ·
              refine ⟨7897604902504336582540373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5265069935002891055026915 7897604902504336582540373)
              ·
                refine ⟨92550057451222694326645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7897604902504336582540373 92550057451222694326645)
                ·
                  rfl

theorem cell21_1216624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 8].length) (baseStart_1216624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216624 prefixEnd_1216624 := by exact prefixLift 1216624
  have htrace : WordTrace (prefixWord ++ tailWord_1216624) baseStart_1216624 baseEnd_1216624 := by
    simpa [prefixWord, tailWord_1216624, baseEnd_1216624] using wordTrace_append hprefix tailTrace_1216624
  have hstable : (prefixWord ++ tailWord_1216624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216624).length < 2 ^ (prefixWord ++ tailWord_1216624).sum := by decide
  have hdescent : baseEnd_1216624 < baseStart_1216624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216776 : List Nat := [2, 1, 3, 2, 3, 1, 9]
def baseStart_1216776 : Nat := 118140960795 + 1216776 * 2 ^ 59
def prefixEnd_1216776 : Nat := 4983230072969 + 3 ^ 40 * 1216776 * 2
def baseEnd_1216776 : Nat := 30853873424949955160699

theorem tailTrace_1216776 : CollatzResearch.WordTrace tailWord_1216776 prefixEnd_1216776 30853873424949955160699 := by
  unfold tailWord_1216776
  simp only [CollatzResearch.WordTrace]
  refine ⟨22189733319917917820703091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29586311093223890427604121 22189733319917917820703091)
  ·
    refine ⟨33284599979876876731054637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22189733319917917820703091 33284599979876876731054637)
    ·
      refine ⟨12481724992453828774145489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33284599979876876731054637 12481724992453828774145489)
      ·
        refine ⟨9361293744340371580609117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12481724992453828774145489 9361293744340371580609117)
        ·
          refine ⟨3510485154127639342728419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9361293744340371580609117 3510485154127639342728419)
          ·
            refine ⟨5265727731191459014092629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510485154127639342728419 5265727731191459014092629)
            ·
              refine ⟨30853873424949955160699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5265727731191459014092629 30853873424949955160699)
              ·
                rfl

theorem cell21_1216776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 9].length) (baseStart_1216776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216776 prefixEnd_1216776 := by exact prefixLift 1216776
  have htrace : WordTrace (prefixWord ++ tailWord_1216776) baseStart_1216776 baseEnd_1216776 := by
    simpa [prefixWord, tailWord_1216776, baseEnd_1216776] using wordTrace_append hprefix tailTrace_1216776
  have hstable : (prefixWord ++ tailWord_1216776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216776).length < 2 ^ (prefixWord ++ tailWord_1216776).sum := by decide
  have hdescent : baseEnd_1216776 < baseStart_1216776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216869 : List Nat := [1, 3, 1, 3, 1, 4, 3, 5]
def baseStart_1216869 : Nat := 118140960795 + 1216869 * 2 ^ 59
def prefixEnd_1216869 : Nat := 4983230072969 + 3 ^ 40 * 1216869 * 2
def baseEnd_1216869 : Nat := 92568694897200700465367

theorem tailTrace_1216869 : CollatzResearch.WordTrace tailWord_1216869 prefixEnd_1216869 92568694897200700465367 := by
  unfold tailWord_1216869
  simp only [CollatzResearch.WordTrace]
  refine ⟨44382858628498912524541661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29588572418999275016361107 44382858628498912524541661)
  ·
    refine ⟨16643571985687092196703123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44382858628498912524541661 16643571985687092196703123)
    ·
      refine ⟨24965357978530638295054685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16643571985687092196703123 24965357978530638295054685)
      ·
        refine ⟨9362009241948989360645507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24965357978530638295054685 9362009241948989360645507)
        ·
          refine ⟨14043013862923484040968261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9362009241948989360645507 14043013862923484040968261)
          ·
            refine ⟨2633065099298153257681549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14043013862923484040968261 2633065099298153257681549)
            ·
              refine ⟨987399412236807471630581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2633065099298153257681549 987399412236807471630581)
              ·
                refine ⟨92568694897200700465367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 987399412236807471630581 92568694897200700465367)
                ·
                  rfl

theorem cell21_1216869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 5].length) (baseStart_1216869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216869 prefixEnd_1216869 := by exact prefixLift 1216869
  have htrace : WordTrace (prefixWord ++ tailWord_1216869) baseStart_1216869 baseEnd_1216869 := by
    simpa [prefixWord, tailWord_1216869, baseEnd_1216869] using wordTrace_append hprefix tailTrace_1216869
  have hstable : (prefixWord ++ tailWord_1216869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216869).length < 2 ^ (prefixWord ++ tailWord_1216869).sum := by decide
  have hdescent : baseEnd_1216869 < baseStart_1216869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216886 : List Nat := [5, 1, 1, 4, 1, 1, 8]
def baseStart_1216886 : Nat := 118140960795 + 1216886 * 2 ^ 59
def prefixEnd_1216886 : Nat := 4983230072969 + 3 ^ 40 * 1216886 * 2
def baseEnd_1216886 : Nat := 30856662702579316623637

theorem tailTrace_1216886 : CollatzResearch.WordTrace tailWord_1216886 prefixEnd_1216886 30856662702579316623637 := by
  unfold tailWord_1216886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773967416839832776744407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29588985779624882951940341 2773967416839832776744407)
  ·
    refine ⟨4160951125259749165116611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2773967416839832776744407 4160951125259749165116611)
    ·
      refine ⟨6241426687889623747674917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4160951125259749165116611 6241426687889623747674917)
      ·
        refine ⟨1170267503979304452689047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6241426687889623747674917 1170267503979304452689047)
        ·
          refine ⟨1755401255968956679033571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170267503979304452689047 1755401255968956679033571)
          ·
            refine ⟨2633101883953435018550357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755401255968956679033571 2633101883953435018550357)
            ·
              refine ⟨30856662702579316623637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2633101883953435018550357 30856662702579316623637)
              ·
                rfl

theorem cell21_1216886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 8].length) (baseStart_1216886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216886 prefixEnd_1216886 := by exact prefixLift 1216886
  have htrace : WordTrace (prefixWord ++ tailWord_1216886) baseStart_1216886 baseEnd_1216886 := by
    simpa [prefixWord, tailWord_1216886, baseEnd_1216886] using wordTrace_append hprefix tailTrace_1216886
  have hstable : (prefixWord ++ tailWord_1216886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216886).length < 2 ^ (prefixWord ++ tailWord_1216886).sum := by decide
  have hdescent : baseEnd_1216886 < baseStart_1216886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216900 : List Nat := [2, 3, 2, 1, 1, 2, 1, 6, 3]
def baseStart_1216900 : Nat := 118140960795 + 1216900 * 2 ^ 59
def prefixEnd_1216900 : Nat := 4983230072969 + 3 ^ 40 * 1216900 * 2
def baseEnd_1216900 : Nat := 277713159313952936379371

theorem tailTrace_1216900 : CollatzResearch.WordTrace tailWord_1216900 prefixEnd_1216900 277713159313952936379371 := by
  unfold tailWord_1216900
  simp only [CollatzResearch.WordTrace]
  refine ⟨22191994645693302409460077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29589326194257736545946769 22191994645693302409460077)
  ·
    refine ⟨8321997992134988403547529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22191994645693302409460077 8321997992134988403547529)
    ·
      refine ⟨6241498494101241302660647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8321997992134988403547529 6241498494101241302660647)
      ·
        refine ⟨9362247741151861953990971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6241498494101241302660647 9362247741151861953990971)
        ·
          refine ⟨14043371611727792930986457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9362247741151861953990971 14043371611727792930986457)
          ·
            refine ⟨10532528708795844698239843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14043371611727792930986457 10532528708795844698239843)
            ·
              refine ⟨15798793063193767047359765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10532528708795844698239843 15798793063193767047359765)
              ·
                refine ⟨740568424837207830344989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15798793063193767047359765 740568424837207830344989)
                ·
                  refine ⟨277713159313952936379371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740568424837207830344989 277713159313952936379371)
                  ·
                    rfl

theorem cell21_1216900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_1216900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216900 prefixEnd_1216900 := by exact prefixLift 1216900
  have htrace : WordTrace (prefixWord ++ tailWord_1216900) baseStart_1216900 baseEnd_1216900 := by
    simpa [prefixWord, tailWord_1216900, baseEnd_1216900] using wordTrace_append hprefix tailTrace_1216900
  have hstable : (prefixWord ++ tailWord_1216900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216900).length < 2 ^ (prefixWord ++ tailWord_1216900).sum := by decide
  have hdescent : baseEnd_1216900 < baseStart_1216900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1216928 : List Nat := [2, 1, 1, 4, 1, 4, 1, 7]
def baseStart_1216928 : Nat := 118140960795 + 1216928 * 2 ^ 59
def prefixEnd_1216928 : Nat := 4983230072969 + 3 ^ 40 * 1216928 * 2
def baseEnd_1216928 : Nat := 92573183098477036637549

theorem tailTrace_1216928 : CollatzResearch.WordTrace tailWord_1216928 prefixEnd_1216928 92573183098477036637549 := by
  unfold tailWord_1216928
  simp only [CollatzResearch.WordTrace]
  refine ⟨22192505267642582800469719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29590007023523443733959625 22192505267642582800469719)
  ·
    refine ⟨33288757901463874200704579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22192505267642582800469719 33288757901463874200704579)
    ·
      refine ⟨49933136852195811301056869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33288757901463874200704579 49933136852195811301056869)
      ·
        refine ⟨9362463159786714618948163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49933136852195811301056869 9362463159786714618948163)
        ·
          refine ⟨14043694739680071928422245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9362463159786714618948163 14043694739680071928422245)
          ·
            refine ⟨2633192763690013486579171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14043694739680071928422245 2633192763690013486579171)
            ·
              refine ⟨3949789145535020229868757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633192763690013486579171 3949789145535020229868757)
              ·
                refine ⟨92573183098477036637549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3949789145535020229868757 92573183098477036637549)
                ·
                  rfl

theorem cell21_1216928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_1216928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1216928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1216928 prefixEnd_1216928 := by exact prefixLift 1216928
  have htrace : WordTrace (prefixWord ++ tailWord_1216928) baseStart_1216928 baseEnd_1216928 := by
    simpa [prefixWord, tailWord_1216928, baseEnd_1216928] using wordTrace_append hprefix tailTrace_1216928
  have hstable : (prefixWord ++ tailWord_1216928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1216928).length < 2 ^ (prefixWord ++ tailWord_1216928).sum := by decide
  have hdescent : baseEnd_1216928 < baseStart_1216928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1216928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217035 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 5]
def baseStart_1217035 : Nat := 118140960795 + 1217035 * 2 ^ 59
def prefixEnd_1217035 : Nat := 4983230072969 + 3 ^ 40 * 1217035 * 2
def baseEnd_1217035 : Nat := 277743968153222701629095

theorem tailTrace_1217035 : CollatzResearch.WordTrace tailWord_1217035 prefixEnd_1217035 277743968153222701629095 := by
  unfold tailWord_1217035
  simp only [CollatzResearch.WordTrace]
  refine ⟨44388913145897522875084559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29592608763931681916723039 44388913145897522875084559)
  ·
    refine ⟨66583369718846284312626839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44388913145897522875084559 66583369718846284312626839)
    ·
      refine ⟨99875054578269426468940259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66583369718846284312626839 99875054578269426468940259)
      ·
        refine ⟨149812581867404139703410389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99875054578269426468940259 149812581867404139703410389)
        ·
          refine ⟨3511232387517284524298681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 149812581867404139703410389 3511232387517284524298681)
          ·
            refine ⟨2633424290637963393224011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3511232387517284524298681 2633424290637963393224011)
            ·
              refine ⟨3950136435956945089836017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633424290637963393224011 3950136435956945089836017)
              ·
                refine ⟨2962602326967708817377013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3950136435956945089836017 2962602326967708817377013)
                ·
                  refine ⟨277743968153222701629095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2962602326967708817377013 277743968153222701629095)
                  ·
                    rfl

theorem cell21_1217035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 5].length) (baseStart_1217035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217035 prefixEnd_1217035 := by exact prefixLift 1217035
  have htrace : WordTrace (prefixWord ++ tailWord_1217035) baseStart_1217035 baseEnd_1217035 := by
    simpa [prefixWord, tailWord_1217035, baseEnd_1217035] using wordTrace_append hprefix tailTrace_1217035
  have hstable : (prefixWord ++ tailWord_1217035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217035).length < 2 ^ (prefixWord ++ tailWord_1217035).sum := by decide
  have hdescent : baseEnd_1217035 < baseStart_1217035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217052 : List Nat := [2, 2, 3, 1, 2, 2, 1, 5, 3]
def baseStart_1217052 : Nat := 118140960795 + 1217052 * 2 ^ 59
def prefixEnd_1217052 : Nat := 4983230072969 + 3 ^ 40 * 1217052 * 2
def baseEnd_1217052 : Nat := 277747847784834449845727

theorem tailTrace_1217052 : CollatzResearch.WordTrace tailWord_1217052 prefixEnd_1217052 277747847784834449845727 := by
  unfold tailWord_1217052
  simp only [CollatzResearch.WordTrace]
  refine ⟨22194766593417967389226705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29593022124557289852302273 22194766593417967389226705)
  ·
    refine ⟨16646074945063475541920029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22194766593417967389226705 16646074945063475541920029)
    ·
      refine ⟨6242278104398803328220011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16646074945063475541920029 6242278104398803328220011)
      ·
        refine ⟨9363417156598204992330017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6242278104398803328220011 9363417156598204992330017)
        ·
          refine ⟨7022562867448653744247513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9363417156598204992330017 7022562867448653744247513)
          ·
            refine ⟨5266922150586490308185635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7022562867448653744247513 5266922150586490308185635)
            ·
              refine ⟨7900383225879735462278453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5266922150586490308185635 7900383225879735462278453)
              ·
                refine ⟨740660927426225199588605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7900383225879735462278453 740660927426225199588605)
                ·
                  refine ⟨277747847784834449845727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740660927426225199588605 277747847784834449845727)
                  ·
                    rfl

theorem cell21_1217052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_1217052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217052 prefixEnd_1217052 := by exact prefixLift 1217052
  have htrace : WordTrace (prefixWord ++ tailWord_1217052) baseStart_1217052 baseEnd_1217052 := by
    simpa [prefixWord, tailWord_1217052, baseEnd_1217052] using wordTrace_append hprefix tailTrace_1217052
  have hstable : (prefixWord ++ tailWord_1217052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217052).length < 2 ^ (prefixWord ++ tailWord_1217052).sum := by decide
  have hdescent : baseEnd_1217052 < baseStart_1217052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217066 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 6]
def baseStart_1217066 : Nat := 118140960795 + 1217066 * 2 ^ 59
def prefixEnd_1217066 : Nat := 4983230072969 + 3 ^ 40 * 1217066 * 2
def baseEnd_1217066 : Nat := 277751042775573536612365

theorem tailTrace_1217066 : CollatzResearch.WordTrace tailWord_1217066 prefixEnd_1217066 277751042775573536612365 := by
  unfold tailWord_1217066
  simp only [CollatzResearch.WordTrace]
  refine ⟨11097510952196303792365763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29593362539190143446308701 11097510952196303792365763)
  ·
    refine ⟨16646266428294455688548645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11097510952196303792365763 16646266428294455688548645)
    ·
      refine ⟨3121174955305210441602871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16646266428294455688548645 3121174955305210441602871)
      ·
        refine ⟨4681762432957815662404307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3121174955305210441602871 4681762432957815662404307)
        ·
          refine ⟨7022643649436723493606461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4681762432957815662404307 7022643649436723493606461)
          ·
            refine ⟨2633491368538771310102423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7022643649436723493606461 2633491368538771310102423)
            ·
              refine ⟨3950237052808156965153635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633491368538771310102423 3950237052808156965153635)
              ·
                refine ⟨5925355579212235447730453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3950237052808156965153635 5925355579212235447730453)
                ·
                  refine ⟨277751042775573536612365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5925355579212235447730453 277751042775573536612365)
                  ·
                    rfl

theorem cell21_1217066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_1217066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217066 prefixEnd_1217066 := by exact prefixLift 1217066
  have htrace : WordTrace (prefixWord ++ tailWord_1217066) baseStart_1217066 baseEnd_1217066 := by
    simpa [prefixWord, tailWord_1217066, baseEnd_1217066] using wordTrace_append hprefix tailTrace_1217066
  have hstable : (prefixWord ++ tailWord_1217066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217066).length < 2 ^ (prefixWord ++ tailWord_1217066).sum := by decide
  have hdescent : baseEnd_1217066 < baseStart_1217066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217156 : List Nat := [2, 3, 2, 1, 3, 1, 2, 7]
def baseStart_1217156 : Nat := 118140960795 + 1217156 * 2 ^ 59
def prefixEnd_1217156 : Nat := 4983230072969 + 3 ^ 40 * 1217156 * 2
def baseEnd_1217156 : Nat := 92590527333917793370727

theorem tailTrace_1217156 : CollatzResearch.WordTrace tailWord_1217156 prefixEnd_1217156 92590527333917793370727 := by
  unfold tailWord_1217156
  simp only [CollatzResearch.WordTrace]
  refine ⟨22196663189229580270119661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29595550918972773693492881 22196663189229580270119661)
  ·
    refine ⟨8323748695961092601294873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22196663189229580270119661 8323748695961092601294873)
    ·
      refine ⟨6242811521970819450971155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8323748695961092601294873 6242811521970819450971155)
      ·
        refine ⟨9364217282956229176456733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6242811521970819450971155 9364217282956229176456733)
        ·
          refine ⟨3511581481108585941171275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9364217282956229176456733 3511581481108585941171275)
          ·
            refine ⟨5267372221662878911756913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3511581481108585941171275 5267372221662878911756913)
            ·
              refine ⟨3950529166247159183817685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5267372221662878911756913 3950529166247159183817685)
              ·
                refine ⟨92590527333917793370727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3950529166247159183817685 92590527333917793370727)
                ·
                  rfl

theorem cell21_1217156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 7].length) (baseStart_1217156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217156 prefixEnd_1217156 := by exact prefixLift 1217156
  have htrace : WordTrace (prefixWord ++ tailWord_1217156) baseStart_1217156 baseEnd_1217156 := by
    simpa [prefixWord, tailWord_1217156, baseEnd_1217156] using wordTrace_append hprefix tailTrace_1217156
  have hstable : (prefixWord ++ tailWord_1217156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217156).length < 2 ^ (prefixWord ++ tailWord_1217156).sum := by decide
  have hdescent : baseEnd_1217156 < baseStart_1217156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217308 : List Nat := [2, 2, 3, 1, 1, 4, 2, 6]
def baseStart_1217308 : Nat := 118140960795 + 1217308 * 2 ^ 59
def prefixEnd_1217308 : Nat := 4983230072969 + 3 ^ 40 * 1217308 * 2
def baseEnd_1217308 : Nat := 92602090157544964526179

theorem tailTrace_1217308 : CollatzResearch.WordTrace tailWord_1217308 prefixEnd_1217308 92602090157544964526179 := by
  unfold tailWord_1217308
  simp only [CollatzResearch.WordTrace]
  refine ⟨22199435136954245249886289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29599246849272326999848385 22199435136954245249886289)
  ·
    refine ⟨16649576352715683937414717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22199435136954245249886289 16649576352715683937414717)
    ·
      refine ⟨6243591132268381476530519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16649576352715683937414717 6243591132268381476530519)
      ·
        refine ⟨9365386698402572214795779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6243591132268381476530519 9365386698402572214795779)
        ·
          refine ⟨14048080047603858322193669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9365386698402572214795779 14048080047603858322193669)
          ·
            refine ⟨2634015008925723435411313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14048080047603858322193669 2634015008925723435411313)
            ·
              refine ⟨1975511256694292576558485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2634015008925723435411313 1975511256694292576558485)
              ·
                refine ⟨92602090157544964526179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1975511256694292576558485 92602090157544964526179)
                ·
                  rfl

theorem cell21_1217308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 6].length) (baseStart_1217308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217308 prefixEnd_1217308 := by exact prefixLift 1217308
  have htrace : WordTrace (prefixWord ++ tailWord_1217308) baseStart_1217308 baseEnd_1217308 := by
    simpa [prefixWord, tailWord_1217308, baseEnd_1217308] using wordTrace_append hprefix tailTrace_1217308
  have hstable : (prefixWord ++ tailWord_1217308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217308).length < 2 ^ (prefixWord ++ tailWord_1217308).sum := by decide
  have hdescent : baseEnd_1217308 < baseStart_1217308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217311 : List Nat := [1, 1, 2, 4, 2, 4, 2, 1, 4]
def baseStart_1217311 : Nat := 118140960795 + 1217311 * 2 ^ 59
def prefixEnd_1217311 : Nat := 4983230072969 + 3 ^ 40 * 1217311 * 2
def baseEnd_1217311 : Nat := 277806955113507555028531

theorem tailTrace_1217311 : CollatzResearch.WordTrace tailWord_1217311 prefixEnd_1217311 277806955113507555028531 := by
  unfold tailWord_1217311
  simp only [CollatzResearch.WordTrace]
  refine ⟨44398979692897622012131787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29599319795265081341421191 44398979692897622012131787)
  ·
    refine ⟨66598469539346433018197681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44398979692897622012131787 66598469539346433018197681)
    ·
      refine ⟨49948852154509824763648261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66598469539346433018197681 49948852154509824763648261)
      ·
        refine ⟨9365409778970592143184049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49948852154509824763648261 9365409778970592143184049)
        ·
          refine ⟨7024057334227944107388037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9365409778970592143184049 7024057334227944107388037)
          ·
            refine ⟨1317010750167739520135257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7024057334227944107388037 1317010750167739520135257)
            ·
              refine ⟨987758062625804640101443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317010750167739520135257 987758062625804640101443)
              ·
                refine ⟨1481637093938706960152165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987758062625804640101443 1481637093938706960152165)
                ·
                  refine ⟨277806955113507555028531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1481637093938706960152165 277806955113507555028531)
                  ·
                    rfl

theorem cell21_1217311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 4].length) (baseStart_1217311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217311 prefixEnd_1217311 := by exact prefixLift 1217311
  have htrace : WordTrace (prefixWord ++ tailWord_1217311) baseStart_1217311 baseEnd_1217311 := by
    simpa [prefixWord, tailWord_1217311, baseEnd_1217311] using wordTrace_append hprefix tailTrace_1217311
  have hstable : (prefixWord ++ tailWord_1217311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217311).length < 2 ^ (prefixWord ++ tailWord_1217311).sum := by decide
  have hdescent : baseEnd_1217311 < baseStart_1217311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217348 : List Nat := [2, 3, 4, 2, 2, 1, 2, 2, 3]
def baseStart_1217348 : Nat := 118140960795 + 1217348 * 2 ^ 59
def prefixEnd_1217348 : Nat := 4983230072969 + 3 ^ 40 * 1217348 * 2
def baseEnd_1217348 : Nat := 277815399017603712911789

theorem tailTrace_1217348 : CollatzResearch.WordTrace tailWord_1217348 prefixEnd_1217348 277815399017603712911789 := by
  unfold tailWord_1217348
  simp only [CollatzResearch.WordTrace]
  refine ⟨22200164596881788665614349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29600219462509051554152465 22200164596881788665614349)
  ·
    refine ⟨8325061723830670749605381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22200164596881788665614349 8325061723830670749605381)
    ·
      refine ⟨1560949073218250765551009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8325061723830670749605381 1560949073218250765551009)
      ·
        refine ⟨1170711804913688074163257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1560949073218250765551009 1170711804913688074163257)
        ·
          refine ⟨878033853685266055622443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1170711804913688074163257 878033853685266055622443)
          ·
            refine ⟨1317050780527899083433665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878033853685266055622443 1317050780527899083433665)
            ·
              refine ⟨987788085395924312575249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317050780527899083433665 987788085395924312575249)
              ·
                refine ⟨740841064046943234431437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 987788085395924312575249 740841064046943234431437)
                ·
                  refine ⟨277815399017603712911789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740841064046943234431437 277815399017603712911789)
                  ·
                    rfl

theorem cell21_1217348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_1217348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217348 prefixEnd_1217348 := by exact prefixLift 1217348
  have htrace : WordTrace (prefixWord ++ tailWord_1217348) baseStart_1217348 baseEnd_1217348 := by
    simpa [prefixWord, tailWord_1217348, baseEnd_1217348] using wordTrace_append hprefix tailTrace_1217348
  have hstable : (prefixWord ++ tailWord_1217348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217348).length < 2 ^ (prefixWord ++ tailWord_1217348).sum := by decide
  have hdescent : baseEnd_1217348 < baseStart_1217348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217353 : List Nat := [1, 2, 1, 1, 2, 5, 1, 4, 4]
def baseStart_1217353 : Nat := 118140960795 + 1217353 * 2 ^ 59
def prefixEnd_1217353 : Nat := 4983230072969 + 3 ^ 40 * 1217353 * 2
def baseEnd_1217353 : Nat := 277816540085724815328445

theorem tailTrace_1217353 : CollatzResearch.WordTrace tailWord_1217353 prefixEnd_1217353 277816540085724815328445 := by
  unfold tailWord_1217353
  simp only [CollatzResearch.WordTrace]
  refine ⟨44400511558745463185160713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29600341039163642123440475 44400511558745463185160713)
  ·
    refine ⟨33300383669059097388870535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44400511558745463185160713 33300383669059097388870535)
    ·
      refine ⟨49950575503588646083305803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33300383669059097388870535 49950575503588646083305803)
      ·
        refine ⟨74925863255382969124958705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49950575503588646083305803 74925863255382969124958705)
        ·
          refine ⟨56194397441537226843719029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74925863255382969124958705 56194397441537226843719029)
          ·
            refine ⟨5268224760144115016598659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56194397441537226843719029 5268224760144115016598659)
            ·
              refine ⟨7902337140216172524897989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5268224760144115016598659 7902337140216172524897989)
              ·
                refine ⟨1481688213790532348418373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7902337140216172524897989 1481688213790532348418373)
                ·
                  refine ⟨277816540085724815328445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1481688213790532348418373 277816540085724815328445)
                  ·
                    rfl

theorem cell21_1217353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_1217353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217353 prefixEnd_1217353 := by exact prefixLift 1217353
  have htrace : WordTrace (prefixWord ++ tailWord_1217353) baseStart_1217353 baseEnd_1217353 := by
    simpa [prefixWord, tailWord_1217353, baseEnd_1217353] using wordTrace_append hprefix tailTrace_1217353
  have hstable : (prefixWord ++ tailWord_1217353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217353).length < 2 ^ (prefixWord ++ tailWord_1217353).sum := by decide
  have hdescent : baseEnd_1217353 < baseStart_1217353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217356 : List Nat := [2, 2, 1, 3, 3, 2, 1, 4, 3]
def baseStart_1217356 : Nat := 118140960795 + 1217356 * 2 ^ 59
def prefixEnd_1217356 : Nat := 4983230072969 + 3 ^ 40 * 1217356 * 2
def baseEnd_1217356 : Nat := 277817224726597476778439

theorem tailTrace_1217356 : CollatzResearch.WordTrace tailWord_1217356 prefixEnd_1217356 277817224726597476778439 := by
  unfold tailWord_1217356
  simp only [CollatzResearch.WordTrace]
  refine ⟨22200310488867297348759961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29600413985156396465013281 22200310488867297348759961)
  ·
    refine ⟨16650232866650473011569971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22200310488867297348759961 16650232866650473011569971)
    ·
      refine ⟨24975349299975709517354957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16650232866650473011569971 24975349299975709517354957)
      ·
        refine ⟨9365755987490891069008109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24975349299975709517354957 9365755987490891069008109)
        ·
          refine ⟨3512158495309084150878041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9365755987490891069008109 3512158495309084150878041)
          ·
            refine ⟨2634118871481813113158531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3512158495309084150878041 2634118871481813113158531)
            ·
              refine ⟨3951178307222719669737797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2634118871481813113158531 3951178307222719669737797)
              ·
                refine ⟨740845932604259938075837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3951178307222719669737797 740845932604259938075837)
                ·
                  refine ⟨277817224726597476778439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740845932604259938075837 277817224726597476778439)
                  ·
                    rfl

theorem cell21_1217356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_1217356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217356 prefixEnd_1217356 := by exact prefixLift 1217356
  have htrace : WordTrace (prefixWord ++ tailWord_1217356) baseStart_1217356 baseEnd_1217356 := by
    simpa [prefixWord, tailWord_1217356, baseEnd_1217356] using wordTrace_append hprefix tailTrace_1217356
  have hstable : (prefixWord ++ tailWord_1217356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217356).length < 2 ^ (prefixWord ++ tailWord_1217356).sum := by decide
  have hdescent : baseEnd_1217356 < baseStart_1217356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217415 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 5]
def baseStart_1217415 : Nat := 118140960795 + 1217415 * 2 ^ 59
def prefixEnd_1217415 : Nat := 4983230072969 + 3 ^ 40 * 1217415 * 2
def baseEnd_1217415 : Nat := 277830689330426485294985

theorem tailTrace_1217415 : CollatzResearch.WordTrace tailWord_1217415 prefixEnd_1217415 277830689330426485294985 := by
  unfold tailWord_1217415
  simp only [CollatzResearch.WordTrace]
  refine ⟨44402772884520847773917699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29601848589680565182611799 44402772884520847773917699)
  ·
    refine ⟨66604159326781271660876549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44402772884520847773917699 66604159326781271660876549)
    ·
      refine ⟨12488279873771488436414353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66604159326781271660876549 12488279873771488436414353)
      ·
        refine ⟨9366209905328616327310765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12488279873771488436414353 9366209905328616327310765)
        ·
          refine ⟨3512328714498231122741537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9366209905328616327310765 3512328714498231122741537)
          ·
            refine ⟨2634246535873673342056153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3512328714498231122741537 2634246535873673342056153)
            ·
              refine ⟨1975684901905255006542115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2634246535873673342056153 1975684901905255006542115)
              ·
                refine ⟨2963527352857882509813173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1975684901905255006542115 2963527352857882509813173)
                ·
                  refine ⟨277830689330426485294985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2963527352857882509813173 277830689330426485294985)
                  ·
                    rfl

theorem cell21_1217415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 5].length) (baseStart_1217415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217415 prefixEnd_1217415 := by exact prefixLift 1217415
  have htrace : WordTrace (prefixWord ++ tailWord_1217415) baseStart_1217415 baseEnd_1217415 := by
    simpa [prefixWord, tailWord_1217415, baseEnd_1217415] using wordTrace_append hprefix tailTrace_1217415
  have hstable : (prefixWord ++ tailWord_1217415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217415).length < 2 ^ (prefixWord ++ tailWord_1217415).sum := by decide
  have hdescent : baseEnd_1217415 < baseStart_1217415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217480 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 4]
def baseStart_1217480 : Nat := 118140960795 + 1217480 * 2 ^ 59
def prefixEnd_1217480 : Nat := 4983230072969 + 3 ^ 40 * 1217480 * 2
def baseEnd_1217480 : Nat := 277845523216000816711519

theorem tailTrace_1217480 : CollatzResearch.WordTrace tailWord_1217480 prefixEnd_1217480 277845523216000816711519 := by
  unfold tailWord_1217480
  simp only [CollatzResearch.WordTrace]
  refine ⟨22202571814642681937516947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29603429086190242583355929 22202571814642681937516947)
  ·
    refine ⟨33303857721964022906275421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22202571814642681937516947 33303857721964022906275421)
    ·
      refine ⟨12488946645736508589853283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33303857721964022906275421 12488946645736508589853283)
      ·
        refine ⟨18733419968604762884779925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12488946645736508589853283 18733419968604762884779925)
        ·
          refine ⟨878129061028348260224059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18733419968604762884779925 878129061028348260224059)
          ·
            refine ⟨1317193591542522390336089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878129061028348260224059 1317193591542522390336089)
            ·
              refine ⟨987895193656891792752067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317193591542522390336089 987895193656891792752067)
              ·
                refine ⟨1481842790485337689128101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987895193656891792752067 1481842790485337689128101)
                ·
                  refine ⟨277845523216000816711519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1481842790485337689128101 277845523216000816711519)
                  ·
                    rfl

theorem cell21_1217480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 4].length) (baseStart_1217480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217480 prefixEnd_1217480 := by exact prefixLift 1217480
  have htrace : WordTrace (prefixWord ++ tailWord_1217480) baseStart_1217480 baseEnd_1217480 := by
    simpa [prefixWord, tailWord_1217480, baseEnd_1217480] using wordTrace_append hprefix tailTrace_1217480
  have hstable : (prefixWord ++ tailWord_1217480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217480).length < 2 ^ (prefixWord ++ tailWord_1217480).sum := by decide
  have hdescent : baseEnd_1217480 < baseStart_1217480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217550 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_1217550 : Nat := 118140960795 + 1217550 * 2 ^ 59
def prefixEnd_1217550 : Nat := 4983230072969 + 3 ^ 40 * 1217550 * 2
def baseEnd_1217550 : Nat := 277861498169696250544709

theorem tailTrace_1217550 : CollatzResearch.WordTrace tailWord_1217550 prefixEnd_1217550 277861498169696250544709 := by
  unfold tailWord_1217550
  simp only [CollatzResearch.WordTrace]
  refine ⟨5550962092378970728760263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29605131159354510553388069 5550962092378970728760263)
  ·
    refine ⟨8326443138568456093140395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5550962092378970728760263 8326443138568456093140395)
    ·
      refine ⟨12489664707852684139710593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8326443138568456093140395 12489664707852684139710593)
      ·
        refine ⟨9367248530889513104782945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12489664707852684139710593 9367248530889513104782945)
        ·
          refine ⟨7025436398167134828587209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9367248530889513104782945 7025436398167134828587209)
          ·
            refine ⟨5269077298625351121440407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7025436398167134828587209 5269077298625351121440407)
            ·
              refine ⟨7903615947938026682160611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5269077298625351121440407 7903615947938026682160611)
              ·
                refine ⟨11855423921907040023240917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7903615947938026682160611 11855423921907040023240917)
                ·
                  refine ⟨277861498169696250544709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11855423921907040023240917 277861498169696250544709)
                  ·
                    rfl

theorem cell21_1217550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_1217550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217550 prefixEnd_1217550 := by exact prefixLift 1217550
  have htrace : WordTrace (prefixWord ++ tailWord_1217550) baseStart_1217550 baseEnd_1217550 := by
    simpa [prefixWord, tailWord_1217550, baseEnd_1217550] using wordTrace_append hprefix tailTrace_1217550
  have hstable : (prefixWord ++ tailWord_1217550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217550).length < 2 ^ (prefixWord ++ tailWord_1217550).sum := by decide
  have hdescent : baseEnd_1217550 < baseStart_1217550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217567 : List Nat := [1, 1, 2, 4, 1, 3, 1, 5, 3]
def baseStart_1217567 : Nat := 118140960795 + 1217567 * 2 ^ 59
def prefixEnd_1217567 : Nat := 4983230072969 + 3 ^ 40 * 1217567 * 2
def baseEnd_1217567 : Nat := 277865377801307998761341

theorem tailTrace_1217567 : CollatzResearch.WordTrace tailWord_1217567 prefixEnd_1217567 277865377801307998761341 := by
  unfold tailWord_1217567
  simp only [CollatzResearch.WordTrace]
  refine ⟨44408316779970177733450955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29605544519980118488967303 44408316779970177733450955)
  ·
    refine ⟨66612475169955266600176433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44408316779970177733450955 66612475169955266600176433)
    ·
      refine ⟨49959356377466449950132325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66612475169955266600176433 49959356377466449950132325)
      ·
        refine ⟨9367379320774959365649811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49959356377466449950132325 9367379320774959365649811)
        ·
          refine ⟨14051068981162439048474717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9367379320774959365649811 14051068981162439048474717)
          ·
            refine ⟨5269150867935914643178019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14051068981162439048474717 5269150867935914643178019)
            ·
              refine ⟨7903726301903871964767029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5269150867935914643178019 7903726301903871964767029)
              ·
                refine ⟨740974340803487996696909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7903726301903871964767029 740974340803487996696909)
                ·
                  refine ⟨277865377801307998761341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740974340803487996696909 277865377801307998761341)
                  ·
                    rfl

theorem cell21_1217567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 5, 3].length) (baseStart_1217567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217567 prefixEnd_1217567 := by exact prefixLift 1217567
  have htrace : WordTrace (prefixWord ++ tailWord_1217567) baseStart_1217567 baseEnd_1217567 := by
    simpa [prefixWord, tailWord_1217567, baseEnd_1217567] using wordTrace_append hprefix tailTrace_1217567
  have hstable : (prefixWord ++ tailWord_1217567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217567).length < 2 ^ (prefixWord ++ tailWord_1217567).sum := by decide
  have hdescent : baseEnd_1217567 < baseStart_1217567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217609 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 7]
def baseStart_1217609 : Nat := 118140960795 + 1217609 * 2 ^ 59
def prefixEnd_1217609 : Nat := 4983230072969 + 3 ^ 40 * 1217609 * 2
def baseEnd_1217609 : Nat := 277874962773525259061255

theorem tailTrace_1217609 : CollatzResearch.WordTrace tailWord_1217609 prefixEnd_1217609 277874962773525259061255 := by
  unfold tailWord_1217609
  simp only [CollatzResearch.WordTrace]
  refine ⟨44409848645818018906479881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29606565763878679270986587 44409848645818018906479881)
  ·
    refine ⟨33307386484363514179859911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44409848645818018906479881 33307386484363514179859911)
    ·
      refine ⟨49961079726545271269789867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33307386484363514179859911 49961079726545271269789867)
      ·
        refine ⟨74941619589817906904684801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49961079726545271269789867 74941619589817906904684801)
        ·
          refine ⟨56206214692363430178513601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74941619589817906904684801 56206214692363430178513601)
          ·
            refine ⟨42154661019272572633885201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56206214692363430178513601 42154661019272572633885201)
            ·
              refine ⟨31615995764454429475413901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42154661019272572633885201 31615995764454429475413901)
              ·
                refine ⟨11855998411670411053280213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31615995764454429475413901 11855998411670411053280213)
                ·
                  refine ⟨277874962773525259061255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11855998411670411053280213 277874962773525259061255)
                  ·
                    rfl

theorem cell21_1217609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_1217609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217609 prefixEnd_1217609 := by exact prefixLift 1217609
  have htrace : WordTrace (prefixWord ++ tailWord_1217609) baseStart_1217609 baseEnd_1217609 := by
    simpa [prefixWord, tailWord_1217609, baseEnd_1217609] using wordTrace_append hprefix tailTrace_1217609
  have hstable : (prefixWord ++ tailWord_1217609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217609).length < 2 ^ (prefixWord ++ tailWord_1217609).sum := by decide
  have hdescent : baseEnd_1217609 < baseStart_1217609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217629 : List Nat := [1, 4, 4, 1, 2, 2, 7]
def baseStart_1217629 : Nat := 118140960795 + 1217629 * 2 ^ 59
def prefixEnd_1217629 : Nat := 4983230072969 + 3 ^ 40 * 1217629 * 2
def baseEnd_1217629 : Nat := 30875503005112185414209

theorem tailTrace_1217629 : CollatzResearch.WordTrace tailWord_1217629 prefixEnd_1217629 30875503005112185414209 := by
  unfold tailWord_1217629
  simp only [CollatzResearch.WordTrace]
  refine ⟨44410578105745562322207941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29607052070497041548138627 44410578105745562322207941)
  ·
    refine ⟨8326983394827292935413989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44410578105745562322207941 8326983394827292935413989)
    ·
      refine ⟨1561309386530117425390123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8326983394827292935413989 1561309386530117425390123)
      ·
        refine ⟨2341964079795176138085185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1561309386530117425390123 2341964079795176138085185)
        ·
          refine ⟨1756473059846382103563889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2341964079795176138085185 1756473059846382103563889)
          ·
            refine ⟨1317354794884786577672917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756473059846382103563889 1317354794884786577672917)
            ·
              refine ⟨30875503005112185414209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1317354794884786577672917 30875503005112185414209)
              ·
                rfl

theorem cell21_1217629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 7].length) (baseStart_1217629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217629 prefixEnd_1217629 := by exact prefixLift 1217629
  have htrace : WordTrace (prefixWord ++ tailWord_1217629) baseStart_1217629 baseEnd_1217629 := by
    simpa [prefixWord, tailWord_1217629, baseEnd_1217629] using wordTrace_append hprefix tailTrace_1217629
  have hstable : (prefixWord ++ tailWord_1217629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217629).length < 2 ^ (prefixWord ++ tailWord_1217629).sum := by decide
  have hdescent : baseEnd_1217629 < baseStart_1217629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217685 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 9]
def baseStart_1217685 : Nat := 118140960795 + 1217685 * 2 ^ 59
def prefixEnd_1217685 : Nat := 4983230072969 + 3 ^ 40 * 1217685 * 2
def baseEnd_1217685 : Nat := 277892307008966015794433

theorem tailTrace_1217685 : CollatzResearch.WordTrace tailWord_1217685 prefixEnd_1217685 277892307008966015794433 := by
  unfold tailWord_1217685
  simp only [CollatzResearch.WordTrace]
  refine ⟨44412620593542683886246509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29608413729028455924164339 44412620593542683886246509)
  ·
    refine ⟨16654732722578506457342441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44412620593542683886246509 16654732722578506457342441)
    ·
      refine ⟨12491049541933879843006831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16654732722578506457342441 12491049541933879843006831)
      ·
        refine ⟨18736574312900819764510247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12491049541933879843006831 18736574312900819764510247)
        ·
          refine ⟨28104861469351229646765371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18736574312900819764510247 28104861469351229646765371)
          ·
            refine ⟨42157292204026844470148057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28104861469351229646765371 42157292204026844470148057)
            ·
              refine ⟨31617969153020133352611043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42157292204026844470148057 31617969153020133352611043)
              ·
                refine ⟨47426953729530200028916565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31617969153020133352611043 47426953729530200028916565)
                ·
                  refine ⟨277892307008966015794433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47426953729530200028916565 277892307008966015794433)
                  ·
                    rfl

theorem cell21_1217685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_1217685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217685 prefixEnd_1217685 := by exact prefixLift 1217685
  have htrace : WordTrace (prefixWord ++ tailWord_1217685) baseStart_1217685 baseEnd_1217685 := by
    simpa [prefixWord, tailWord_1217685, baseEnd_1217685] using wordTrace_append hprefix tailTrace_1217685
  have hstable : (prefixWord ++ tailWord_1217685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217685).length < 2 ^ (prefixWord ++ tailWord_1217685).sum := by decide
  have hdescent : baseEnd_1217685 < baseStart_1217685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217694 : List Nat := [4, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_1217694 : Nat := 118140960795 + 1217694 * 2 ^ 59
def prefixEnd_1217694 : Nat := 4983230072969 + 3 ^ 40 * 1217694 * 2
def baseEnd_1217694 : Nat := 277894360931584000144415

theorem tailTrace_1217694 : CollatzResearch.WordTrace tailWord_1217694 prefixEnd_1217694 277894360931584000144415 := by
  unfold tailWord_1217694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5551618606313759802915517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29608632567006718948882757 5551618606313759802915517)
  ·
    refine ⟨2081856977367659926093319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5551618606313759802915517 2081856977367659926093319)
    ·
      refine ⟨3122785466051489889139979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2081856977367659926093319 3122785466051489889139979)
      ·
        refine ⟨4684178199077234833709969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3122785466051489889139979 4684178199077234833709969)
        ·
          refine ⟨3513133649307926125282477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4684178199077234833709969 3513133649307926125282477)
          ·
            refine ⟨1317425118490472296980929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3513133649307926125282477 1317425118490472296980929)
            ·
              refine ⟨988068838867854222735697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317425118490472296980929 988068838867854222735697)
              ·
                refine ⟨741051629150890667051773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988068838867854222735697 741051629150890667051773)
                ·
                  refine ⟨277894360931584000144415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741051629150890667051773 277894360931584000144415)
                  ·
                    rfl

theorem cell21_1217694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_1217694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217694 prefixEnd_1217694 := by exact prefixLift 1217694
  have htrace : WordTrace (prefixWord ++ tailWord_1217694) baseStart_1217694 baseEnd_1217694 := by
    simpa [prefixWord, tailWord_1217694, baseEnd_1217694] using wordTrace_append hprefix tailTrace_1217694
  have hstable : (prefixWord ++ tailWord_1217694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217694).length < 2 ^ (prefixWord ++ tailWord_1217694).sum := by decide
  have hdescent : baseEnd_1217694 < baseStart_1217694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217767 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 4]
def baseStart_1217767 : Nat := 118140960795 + 1217767 * 2 ^ 59
def prefixEnd_1217767 : Nat := 4983230072969 + 3 ^ 40 * 1217767 * 2
def baseEnd_1217767 : Nat := 277911020526152095427599

theorem tailTrace_1217767 : CollatzResearch.WordTrace tailWord_1217767 prefixEnd_1217767 277911020526152095427599 := by
  unfold tailWord_1217767
  simp only [CollatzResearch.WordTrace]
  refine ⟨44415611379245611890731555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29610407586163741260487703 44415611379245611890731555)
  ·
    refine ⟨66623417068868417836097333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44415611379245611890731555 66623417068868417836097333)
    ·
      refine ⟨6245945350206414172134125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66623417068868417836097333 6245945350206414172134125)
      ·
        refine ⟨2342229506327405314550297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6245945350206414172134125 2342229506327405314550297)
        ·
          refine ⟨1756672129745553985912723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2342229506327405314550297 1756672129745553985912723)
          ·
            refine ⟨2635008194618330978869085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756672129745553985912723 2635008194618330978869085)
            ·
              refine ⟨988128072981874117075907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2635008194618330978869085 988128072981874117075907)
              ·
                refine ⟨1482192109472811175613861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988128072981874117075907 1482192109472811175613861)
                ·
                  refine ⟨277911020526152095427599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1482192109472811175613861 277911020526152095427599)
                  ·
                    rfl

theorem cell21_1217767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 4].length) (baseStart_1217767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217767 prefixEnd_1217767 := by exact prefixLift 1217767
  have htrace : WordTrace (prefixWord ++ tailWord_1217767) baseStart_1217767 baseEnd_1217767 := by
    simpa [prefixWord, tailWord_1217767, baseEnd_1217767] using wordTrace_append hprefix tailTrace_1217767
  have hstable : (prefixWord ++ tailWord_1217767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217767).length < 2 ^ (prefixWord ++ tailWord_1217767).sum := by decide
  have hdescent : baseEnd_1217767 < baseStart_1217767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217795 : List Nat := [1, 1, 1, 3, 2, 4, 3, 3, 3]
def baseStart_1217795 : Nat := 118140960795 + 1217795 * 2 ^ 59
def prefixEnd_1217795 : Nat := 4983230072969 + 3 ^ 40 * 1217795 * 2
def baseEnd_1217795 : Nat := 277917410507630268960875

theorem tailTrace_1217795 : CollatzResearch.WordTrace tailWord_1217795 prefixEnd_1217795 277917410507630268960875 := by
  unfold tailWord_1217795
  simp only [CollatzResearch.WordTrace]
  refine ⟨44416632623144172672750839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29611088415429448448500559 44416632623144172672750839)
  ·
    refine ⟨66624948934716259009126259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44416632623144172672750839 66624948934716259009126259)
    ·
      refine ⟨99937423402074388513689389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66624948934716259009126259 99937423402074388513689389)
      ·
        refine ⟨37476533775777895692633521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99937423402074388513689389 37476533775777895692633521)
        ·
          refine ⟨28107400331833421769475141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37476533775777895692633521 28107400331833421769475141)
          ·
            refine ⟨5270137562218766581776589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28107400331833421769475141 5270137562218766581776589)
            ·
              refine ⟨1976301585832037468166221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5270137562218766581776589 1976301585832037468166221)
              ·
                refine ⟨741113094687014050562333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1976301585832037468166221 741113094687014050562333)
                ·
                  refine ⟨277917410507630268960875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741113094687014050562333 277917410507630268960875)
                  ·
                    rfl

theorem cell21_1217795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 3, 3].length) (baseStart_1217795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217795 prefixEnd_1217795 := by exact prefixLift 1217795
  have htrace : WordTrace (prefixWord ++ tailWord_1217795) baseStart_1217795 baseEnd_1217795 := by
    simpa [prefixWord, tailWord_1217795, baseEnd_1217795] using wordTrace_append hprefix tailTrace_1217795
  have hstable : (prefixWord ++ tailWord_1217795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217795).length < 2 ^ (prefixWord ++ tailWord_1217795).sum := by decide
  have hdescent : baseEnd_1217795 < baseStart_1217795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217826 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1217826 : Nat := 118140960795 + 1217826 * 2 ^ 59
def prefixEnd_1217826 : Nat := 4983230072969 + 3 ^ 40 * 1217826 * 2
def baseEnd_1217826 : Nat := 277924485129981103944145

theorem tailTrace_1217826 : CollatzResearch.WordTrace tailWord_1217826 prefixEnd_1217826 277924485129981103944145 := by
  unfold tailWord_1217826
  simp only [CollatzResearch.WordTrace]
  refine ⟨11104440821507966241782333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29611842190687909978086221 11104440821507966241782333)
  ·
    refine ⟨4164165308065487340668375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11104440821507966241782333 4164165308065487340668375)
    ·
      refine ⟨6246247962098231011002563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4164165308065487340668375 6246247962098231011002563)
      ·
        refine ⟨9369371943147346516503845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6246247962098231011002563 9369371943147346516503845)
        ·
          refine ⟨1756757239340127471844471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9369371943147346516503845 1756757239340127471844471)
          ·
            refine ⟨2635135859010191207766707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1756757239340127471844471 2635135859010191207766707)
            ·
              refine ⟨3952703788515286811650061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2635135859010191207766707 3952703788515286811650061)
              ·
                refine ⟨1482263920693232554368773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3952703788515286811650061 1482263920693232554368773)
                ·
                  refine ⟨277924485129981103944145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1482263920693232554368773 277924485129981103944145)
                  ·
                    rfl

theorem cell21_1217826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1217826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217826 prefixEnd_1217826 := by exact prefixLift 1217826
  have htrace : WordTrace (prefixWord ++ tailWord_1217826) baseStart_1217826 baseEnd_1217826 := by
    simpa [prefixWord, tailWord_1217826, baseEnd_1217826] using wordTrace_append hprefix tailTrace_1217826
  have hstable : (prefixWord ++ tailWord_1217826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217826).length < 2 ^ (prefixWord ++ tailWord_1217826).sum := by decide
  have hdescent : baseEnd_1217826 < baseStart_1217826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1217950 : List Nat := [4, 3, 1, 2, 2, 2, 2, 5]
def baseStart_1217950 : Nat := 118140960795 + 1217950 * 2 ^ 59
def prefixEnd_1217950 : Nat := 4983230072969 + 3 ^ 40 * 1217950 * 2
def baseEnd_1217950 : Nat := 92650927873128147959075

theorem tailTrace_1217950 : CollatzResearch.WordTrace tailWord_1217950 prefixEnd_1217950 92650927873128147959075 := by
  unfold tailWord_1217950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5552785742197829268080413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29614857291721756096428869 5552785742197829268080413)
  ·
    refine ⟨2082294653324185975530155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5552785742197829268080413 2082294653324185975530155)
    ·
      refine ⟨3123441979986278963295233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082294653324185975530155 3123441979986278963295233)
      ·
        refine ⟨2342581484989709222471425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3123441979986278963295233 2342581484989709222471425)
        ·
          refine ⟨1756936113742281916853569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2342581484989709222471425 1756936113742281916853569)
          ·
            refine ⟨1317702085306711437640177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756936113742281916853569 1317702085306711437640177)
            ·
              refine ⟨988276563980033578230133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317702085306711437640177 988276563980033578230133)
              ·
                refine ⟨92650927873128147959075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 988276563980033578230133 92650927873128147959075)
                ·
                  rfl

theorem cell21_1217950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_1217950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1217950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1217950 prefixEnd_1217950 := by exact prefixLift 1217950
  have htrace : WordTrace (prefixWord ++ tailWord_1217950) baseStart_1217950 baseEnd_1217950 := by
    simpa [prefixWord, tailWord_1217950, baseEnd_1217950] using wordTrace_append hprefix tailTrace_1217950
  have hstable : (prefixWord ++ tailWord_1217950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1217950).length < 2 ^ (prefixWord ++ tailWord_1217950).sum := by decide
  have hdescent : baseEnd_1217950 < baseStart_1217950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1217950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218040 : List Nat := [2, 1, 2, 1, 1, 7, 2, 2, 3]
def baseStart_1218040 : Nat := 118140960795 + 1218040 * 2 ^ 59
def prefixEnd_1218040 : Nat := 4983230072969 + 3 ^ 40 * 1218040 * 2
def baseEnd_1218040 : Nat := 277973322845564287377041

theorem tailTrace_1218040 : CollatzResearch.WordTrace tailWord_1218040 prefixEnd_1218040 277973322845564287377041 := by
  unfold tailWord_1218040
  simp only [CollatzResearch.WordTrace]
  refine ⟨22212784253628289757709787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29617045671504386343613049 22212784253628289757709787)
  ·
    refine ⟨33319176380442434636564681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22212784253628289757709787 33319176380442434636564681)
    ·
      refine ⟨24989382285331825977423511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33319176380442434636564681 24989382285331825977423511)
      ·
        refine ⟨37484073427997738966135267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24989382285331825977423511 37484073427997738966135267)
        ·
          refine ⟨56226110141996608449202901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37484073427997738966135267 56226110141996608449202901)
          ·
            refine ⟨1317799456453045510528193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 56226110141996608449202901 1317799456453045510528193)
            ·
              refine ⟨988349592339784132896145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1317799456453045510528193 988349592339784132896145)
              ·
                refine ⟨741262194254838099672109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988349592339784132896145 741262194254838099672109)
                ·
                  refine ⟨277973322845564287377041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741262194254838099672109 277973322845564287377041)
                  ·
                    rfl

theorem cell21_1218040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 3].length) (baseStart_1218040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218040 prefixEnd_1218040 := by exact prefixLift 1218040
  have htrace : WordTrace (prefixWord ++ tailWord_1218040) baseStart_1218040 baseEnd_1218040 := by
    simpa [prefixWord, tailWord_1218040, baseEnd_1218040] using wordTrace_append hprefix tailTrace_1218040
  have hstable : (prefixWord ++ tailWord_1218040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218040).length < 2 ^ (prefixWord ++ tailWord_1218040).sum := by decide
  have hdescent : baseEnd_1218040 < baseStart_1218040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218065 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 5]
def baseStart_1218065 : Nat := 118140960795 + 1218065 * 2 ^ 59
def prefixEnd_1218065 : Nat := 4983230072969 + 3 ^ 40 * 1218065 * 2
def baseEnd_1218065 : Nat := 277979028186169799460323

theorem tailTrace_1218065 : CollatzResearch.WordTrace tailWord_1218065 prefixEnd_1218065 277979028186169799460323 := by
  unfold tailWord_1218065
  simp only [CollatzResearch.WordTrace]
  refine ⟨44426480332166008785079649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29617653554777339190053099 44426480332166008785079649)
  ·
    refine ⟨33319860249124506588809737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44426480332166008785079649 33319860249124506588809737)
    ·
      refine ⟨24989895186843379941607303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33319860249124506588809737 24989895186843379941607303)
      ·
        refine ⟨37484842780265069912410955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24989895186843379941607303 37484842780265069912410955)
        ·
          refine ⟨56227264170397604868616433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37484842780265069912410955 56227264170397604868616433)
          ·
            refine ⟨42170448127798203651462325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56227264170397604868616433 42170448127798203651462325)
            ·
              refine ⟨3953479511981081592324593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42170448127798203651462325 3953479511981081592324593)
              ·
                refine ⟨2965109633985811194243445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3953479511981081592324593 2965109633985811194243445)
                ·
                  refine ⟨277979028186169799460323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2965109633985811194243445 277979028186169799460323)
                  ·
                    rfl

theorem cell21_1218065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_1218065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218065 prefixEnd_1218065 := by exact prefixLift 1218065
  have htrace : WordTrace (prefixWord ++ tailWord_1218065) baseStart_1218065 baseEnd_1218065 := by
    simpa [prefixWord, tailWord_1218065, baseEnd_1218065] using wordTrace_append hprefix tailTrace_1218065
  have hstable : (prefixWord ++ tailWord_1218065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218065).length < 2 ^ (prefixWord ++ tailWord_1218065).sum := by decide
  have hdescent : baseEnd_1218065 < baseStart_1218065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218206 : List Nat := [4, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_1218206 : Nat := 118140960795 + 1218206 * 2 ^ 59
def prefixEnd_1218206 : Nat := 4983230072969 + 3 ^ 40 * 1218206 * 2
def baseEnd_1218206 : Nat := 278011206307184887610035

theorem tailTrace_1218206 : CollatzResearch.WordTrace tailWord_1218206 prefixEnd_1218206 278011206307184887610035 := by
  unfold tailWord_1218206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5553952878081898733245309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29621082016436793243974981 5553952878081898733245309)
  ·
    refine ⟨2082732329280712024966991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5553952878081898733245309 2082732329280712024966991)
    ·
      refine ⟨3124098493921068037450487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2082732329280712024966991 3124098493921068037450487)
      ·
        refine ⟨4686147740881602056175731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3124098493921068037450487 4686147740881602056175731)
        ·
          refine ⟨7029221611322403084263597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4686147740881602056175731 7029221611322403084263597)
          ·
            refine ⟨2635958104245901156598849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7029221611322403084263597 2635958104245901156598849)
            ·
              refine ⟨1976968578184425867449137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2635958104245901156598849 1976968578184425867449137)
              ·
                refine ⟨1482726433638319400586853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1976968578184425867449137 1482726433638319400586853)
                ·
                  refine ⟨278011206307184887610035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1482726433638319400586853 278011206307184887610035)
                  ·
                    rfl

theorem cell21_1218206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_1218206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218206 prefixEnd_1218206 := by exact prefixLift 1218206
  have htrace : WordTrace (prefixWord ++ tailWord_1218206) baseStart_1218206 baseEnd_1218206 := by
    simpa [prefixWord, tailWord_1218206, baseEnd_1218206] using wordTrace_append hprefix tailTrace_1218206
  have hstable : (prefixWord ++ tailWord_1218206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218206).length < 2 ^ (prefixWord ++ tailWord_1218206).sum := by decide
  have hdescent : baseEnd_1218206 < baseStart_1218206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218265 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 4]
def baseStart_1218265 : Nat := 118140960795 + 1218265 * 2 ^ 59
def prefixEnd_1218265 : Nat := 4983230072969 + 3 ^ 40 * 1218265 * 2
def baseEnd_1218265 : Nat := 278024670911013896126581

theorem tailTrace_1218265 : CollatzResearch.WordTrace tailWord_1218265 prefixEnd_1218265 278024670911013896126581 := by
  unfold tailWord_1218265
  simp only [CollatzResearch.WordTrace]
  refine ⟨44433774931441442942360249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29622516620960961961573499 44433774931441442942360249)
  ·
    refine ⟨33325331198581082206770187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44433774931441442942360249 33325331198581082206770187)
    ·
      refine ⟨49987996797871623310155281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33325331198581082206770187 49987996797871623310155281)
      ·
        refine ⟨37490997598403717482616461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49987996797871623310155281 37490997598403717482616461)
        ·
          refine ⟨14059124099401394055981173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37490997598403717482616461 14059124099401394055981173)
          ·
            refine ⟨1318042884318880692748235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14059124099401394055981173 1318042884318880692748235)
            ·
              refine ⟨1977064326478321039122353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318042884318880692748235 1977064326478321039122353)
              ·
                refine ⟨1482798244858740779341765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1977064326478321039122353 1482798244858740779341765)
                ·
                  refine ⟨278024670911013896126581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1482798244858740779341765 278024670911013896126581)
                  ·
                    rfl

theorem cell21_1218265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_1218265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218265 prefixEnd_1218265 := by exact prefixLift 1218265
  have htrace : WordTrace (prefixWord ++ tailWord_1218265) baseStart_1218265 baseEnd_1218265 := by
    simpa [prefixWord, tailWord_1218265, baseEnd_1218265] using wordTrace_append hprefix tailTrace_1218265
  have hstable : (prefixWord ++ tailWord_1218265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218265).length < 2 ^ (prefixWord ++ tailWord_1218265).sum := by decide
  have hdescent : baseEnd_1218265 < baseStart_1218265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218307 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 6]
def baseStart_1218307 : Nat := 118140960795 + 1218307 * 2 ^ 59
def prefixEnd_1218307 : Nat := 4983230072969 + 3 ^ 40 * 1218307 * 2
def baseEnd_1218307 : Nat := 278034255883231156426495

theorem tailTrace_1218307 : CollatzResearch.WordTrace tailWord_1218307 prefixEnd_1218307 278034255883231156426495 := by
  unfold tailWord_1218307
  simp only [CollatzResearch.WordTrace]
  refine ⟨44435306797289284115389175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29623537864859522743592783 44435306797289284115389175)
  ·
    refine ⟨66652960195933926173083763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44435306797289284115389175 66652960195933926173083763)
    ·
      refine ⟨99979440293900889259625645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66652960195933926173083763 99979440293900889259625645)
      ·
        refine ⟨37492290110212833472359617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99979440293900889259625645 37492290110212833472359617)
        ·
          refine ⟨28119217582659625104269713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37492290110212833472359617 28119217582659625104269713)
          ·
            refine ⟨21089413186994718828202285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28119217582659625104269713 21089413186994718828202285)
            ·
              refine ⟨7908529945123019560575857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21089413186994718828202285 7908529945123019560575857)
              ·
                refine ⟨5931397458842264670431893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7908529945123019560575857 5931397458842264670431893)
                ·
                  refine ⟨278034255883231156426495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5931397458842264670431893 278034255883231156426495)
                  ·
                    rfl

theorem cell21_1218307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_1218307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218307 prefixEnd_1218307 := by exact prefixLift 1218307
  have htrace : WordTrace (prefixWord ++ tailWord_1218307) baseStart_1218307 baseEnd_1218307 := by
    simpa [prefixWord, tailWord_1218307, baseEnd_1218307] using wordTrace_append hprefix tailTrace_1218307
  have hstable : (prefixWord ++ tailWord_1218307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218307).length < 2 ^ (prefixWord ++ tailWord_1218307).sum := by decide
  have hdescent : baseEnd_1218307 < baseStart_1218307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218341 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 4]
def baseStart_1218341 : Nat := 118140960795 + 1218341 * 2 ^ 59
def prefixEnd_1218341 : Nat := 4983230072969 + 3 ^ 40 * 1218341 * 2
def baseEnd_1218341 : Nat := 278042015146454652859759

theorem tailTrace_1218341 : CollatzResearch.WordTrace tailWord_1218341 prefixEnd_1218341 278042015146454652859759 := by
  unfold tailWord_1218341
  simp only [CollatzResearch.WordTrace]
  refine ⟨44436546879166107922126877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29624364586110738614751251 44436546879166107922126877)
  ·
    refine ⟨16663705079687290470797579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44436546879166107922126877 16663705079687290470797579)
    ·
      refine ⟨24995557619530935706196369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16663705079687290470797579 24995557619530935706196369)
      ·
        refine ⟨18746668214648201779647277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24995557619530935706196369 18746668214648201779647277)
        ·
          refine ⟨7030000580493075667367729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18746668214648201779647277 7030000580493075667367729)
          ·
            refine ⟨5272500435369806750525797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7030000580493075667367729 5272500435369806750525797)
            ·
              refine ⟨988593831631838765723587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5272500435369806750525797 988593831631838765723587)
              ·
                refine ⟨1482890747447758148585381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 988593831631838765723587 1482890747447758148585381)
                ·
                  refine ⟨278042015146454652859759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1482890747447758148585381 278042015146454652859759)
                  ·
                    rfl

theorem cell21_1218341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_1218341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218341 prefixEnd_1218341 := by exact prefixLift 1218341
  have htrace : WordTrace (prefixWord ++ tailWord_1218341) baseStart_1218341 baseEnd_1218341 := by
    simpa [prefixWord, tailWord_1218341, baseEnd_1218341] using wordTrace_append hprefix tailTrace_1218341
  have hstable : (prefixWord ++ tailWord_1218341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218341).length < 2 ^ (prefixWord ++ tailWord_1218341).sum := by decide
  have hdescent : baseEnd_1218341 < baseStart_1218341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218400 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 4]
def baseStart_1218400 : Nat := 118140960795 + 1218400 * 2 ^ 59
def prefixEnd_1218400 : Nat := 4983230072969 + 3 ^ 40 * 1218400 * 2
def baseEnd_1218400 : Nat := 278055479750283661376305

theorem tailTrace_1218400 : CollatzResearch.WordTrace tailWord_1218400 prefixEnd_1218400 278055479750283661376305 := by
  unfold tailWord_1218400
  simp only [CollatzResearch.WordTrace]
  refine ⟨22219349392976180499262327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29625799190634907332349769 22219349392976180499262327)
  ·
    refine ⟨33329024089464270748893491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22219349392976180499262327 33329024089464270748893491)
    ·
      refine ⟨49993536134196406123340237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33329024089464270748893491 49993536134196406123340237)
      ·
        refine ⟨18747576050323652296252589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49993536134196406123340237 18747576050323652296252589)
        ·
          refine ⟨7030341018871369611094721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18747576050323652296252589 7030341018871369611094721)
          ·
            refine ⟨5272755764153527208321041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7030341018871369611094721 5272755764153527208321041)
            ·
              refine ⟨3954566823115145406240781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5272755764153527208321041 3954566823115145406240781)
              ·
                refine ⟨1482962558668179527340293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3954566823115145406240781 1482962558668179527340293)
                ·
                  refine ⟨278055479750283661376305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1482962558668179527340293 278055479750283661376305)
                  ·
                    rfl

theorem cell21_1218400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 4].length) (baseStart_1218400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218400 prefixEnd_1218400 := by exact prefixLift 1218400
  have htrace : WordTrace (prefixWord ++ tailWord_1218400) baseStart_1218400 baseEnd_1218400 := by
    simpa [prefixWord, tailWord_1218400, baseEnd_1218400] using wordTrace_append hprefix tailTrace_1218400
  have hstable : (prefixWord ++ tailWord_1218400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218400).length < 2 ^ (prefixWord ++ tailWord_1218400).sum := by decide
  have hdescent : baseEnd_1218400 < baseStart_1218400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218465 : List Nat := [1, 2, 3, 4, 3, 1, 2, 5]
def baseStart_1218465 : Nat := 118140960795 + 1218465 * 2 ^ 59
def prefixEnd_1218465 : Nat := 4983230072969 + 3 ^ 40 * 1218465 * 2
def baseEnd_1218465 : Nat := 92690104545285997597613

theorem tailTrace_1218465 : CollatzResearch.WordTrace tailWord_1218465 prefixEnd_1218465 92690104545285997597613 := by
  unfold tailWord_1218465
  simp only [CollatzResearch.WordTrace]
  refine ⟨44441069530716877099640849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29627379687144584733093899 44441069530716877099640849)
  ·
    refine ⟨33330802148037657824730637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44441069530716877099640849 33330802148037657824730637)
    ·
      refine ⟨12499050805514121684273989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33330802148037657824730637 12499050805514121684273989)
      ·
        refine ⟨2343572026033897815801373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12499050805514121684273989 2343572026033897815801373)
        ·
          refine ⟨878839509762711680925515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2343572026033897815801373 878839509762711680925515)
          ·
            refine ⟨1318259264644067521388273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878839509762711680925515 1318259264644067521388273)
            ·
              refine ⟨988694448483050641041205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318259264644067521388273 988694448483050641041205)
              ·
                refine ⟨92690104545285997597613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 988694448483050641041205 92690104545285997597613)
                ·
                  rfl

theorem cell21_1218465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 5].length) (baseStart_1218465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218465 prefixEnd_1218465 := by exact prefixLift 1218465
  have htrace : WordTrace (prefixWord ++ tailWord_1218465) baseStart_1218465 baseEnd_1218465 := by
    simpa [prefixWord, tailWord_1218465, baseEnd_1218465] using wordTrace_append hprefix tailTrace_1218465
  have hstable : (prefixWord ++ tailWord_1218465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218465).length < 2 ^ (prefixWord ++ tailWord_1218465).sum := by decide
  have hdescent : baseEnd_1218465 < baseStart_1218465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218538 : List Nat := [3, 1, 3, 1, 2, 1, 2, 5, 3]
def baseStart_1218538 : Nat := 118140960795 + 1218538 * 2 ^ 59
def prefixEnd_1218538 : Nat := 4983230072969 + 3 ^ 40 * 1218538 * 2
def baseEnd_1218538 : Nat := 278086973230426088076023

theorem tailTrace_1218538 : CollatzResearch.WordTrace tailWord_1218538 prefixEnd_1218538 278086973230426088076023 := by
  unfold tailWord_1218538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11110933014863102641762067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29629154706301607044698845 11110933014863102641762067)
  ·
    refine ⟨16666399522294653962643101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11110933014863102641762067 16666399522294653962643101)
    ·
      refine ⟨6249899820860495235991163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16666399522294653962643101 6249899820860495235991163)
      ·
        refine ⟨9374849731290742853986745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6249899820860495235991163 9374849731290742853986745)
        ·
          refine ⟨7031137298468057140490059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9374849731290742853986745 7031137298468057140490059)
          ·
            refine ⟨10546705947702085710735089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7031137298468057140490059 10546705947702085710735089)
            ·
              refine ⟨7910029460776564283051317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10546705947702085710735089 7910029460776564283051317)
              ·
                refine ⟨741565261947802901536061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7910029460776564283051317 741565261947802901536061)
                ·
                  refine ⟨278086973230426088076023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741565261947802901536061 278086973230426088076023)
                  ·
                    rfl

theorem cell21_1218538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_1218538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218538 prefixEnd_1218538 := by exact prefixLift 1218538
  have htrace : WordTrace (prefixWord ++ tailWord_1218538) baseStart_1218538 baseEnd_1218538 := by
    simpa [prefixWord, tailWord_1218538, baseEnd_1218538] using wordTrace_append hprefix tailTrace_1218538
  have hstable : (prefixWord ++ tailWord_1218538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218538).length < 2 ^ (prefixWord ++ tailWord_1218538).sum := by decide
  have hdescent : baseEnd_1218538 < baseStart_1218538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218614 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1218614 : Nat := 118140960795 + 1218614 * 2 ^ 59
def prefixEnd_1218614 : Nat := 4983230072969 + 3 ^ 40 * 1218614 * 2
def baseEnd_1218614 : Nat := 278104317465866844809201

theorem tailTrace_1218614 : CollatzResearch.WordTrace tailWord_1218614 prefixEnd_1218614 278104317465866844809201 := by
  unfold tailWord_1218614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777906500448567221675931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29631002671451383697876597 2777906500448567221675931)
  ·
    refine ⟨4166859750672850832513897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2777906500448567221675931 4166859750672850832513897)
    ·
      refine ⟨3125144813004638124385423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4166859750672850832513897 3125144813004638124385423)
      ·
        refine ⟨4687717219506957186578135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125144813004638124385423 4687717219506957186578135)
        ·
          refine ⟨7031575829260435779867203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4687717219506957186578135 7031575829260435779867203)
          ·
            refine ⟨10547363743890653669800805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7031575829260435779867203 10547363743890653669800805)
            ·
              refine ⟨1977630701979497563087651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10547363743890653669800805 1977630701979497563087651)
              ·
                refine ⟨2966446052969246344631477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977630701979497563087651 2966446052969246344631477)
                ·
                  refine ⟨278104317465866844809201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2966446052969246344631477 278104317465866844809201)
                  ·
                    rfl

theorem cell21_1218614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1218614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218614 prefixEnd_1218614 := by exact prefixLift 1218614
  have htrace : WordTrace (prefixWord ++ tailWord_1218614) baseStart_1218614 baseEnd_1218614 := by
    simpa [prefixWord, tailWord_1218614, baseEnd_1218614] using wordTrace_append hprefix tailTrace_1218614
  have hstable : (prefixWord ++ tailWord_1218614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218614).length < 2 ^ (prefixWord ++ tailWord_1218614).sum := by decide
  have hdescent : baseEnd_1218614 < baseStart_1218614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218710 : List Nat := [5, 3, 2, 1, 2, 8]
def baseStart_1218710 : Nat := 118140960795 + 1218710 * 2 ^ 59
def prefixEnd_1218710 : Nat := 4983230072969 + 3 ^ 40 * 1218710 * 2
def baseEnd_1218710 : Nat := 10300971332362667081815

theorem tailTrace_1218710 : CollatzResearch.WordTrace tailWord_1218710 prefixEnd_1218710 10300971332362667081815 := by
  unfold tailWord_1218710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778125338426830246394349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29633336943219522628206389 2778125338426830246394349)
  ·
    refine ⟨1041797001910061342397881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2778125338426830246394349 1041797001910061342397881)
    ·
      refine ⟨781347751432546006798411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1041797001910061342397881 781347751432546006798411)
      ·
        refine ⟨1172021627148819010197617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 781347751432546006798411 1172021627148819010197617)
        ·
          refine ⟨879016220361614257648213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1172021627148819010197617 879016220361614257648213)
          ·
            refine ⟨10300971332362667081815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 879016220361614257648213 10300971332362667081815)
            ·
              rfl

theorem cell21_1218710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 8].length) (baseStart_1218710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218710 prefixEnd_1218710 := by exact prefixLift 1218710
  have htrace : WordTrace (prefixWord ++ tailWord_1218710) baseStart_1218710 baseEnd_1218710 := by
    simpa [prefixWord, tailWord_1218710, baseEnd_1218710] using wordTrace_append hprefix tailTrace_1218710
  have hstable : (prefixWord ++ tailWord_1218710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218710).length < 2 ^ (prefixWord ++ tailWord_1218710).sum := by decide
  have hdescent : baseEnd_1218710 < baseStart_1218710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218718 : List Nat := [4, 3, 1, 1, 12]
def baseStart_1218718 : Nat := 118140960795 + 1218718 * 2 ^ 59
def prefixEnd_1218718 : Nat := 4983230072969 + 3 ^ 40 * 1218718 * 2
def baseEnd_1218718 : Nat := 3433679650404762655255

theorem tailTrace_1218718 : CollatzResearch.WordTrace tailWord_1218718 prefixEnd_1218718 3433679650404762655255 := by
  unfold tailWord_1218718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5556287149850037663575101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29633531465866867539067205 5556287149850037663575101)
  ·
    refine ⟨2083607681193764123840663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5556287149850037663575101 2083607681193764123840663)
    ·
      refine ⟨3125411521790646185760995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2083607681193764123840663 3125411521790646185760995)
      ·
        refine ⟨4688117282685969278641493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125411521790646185760995 4688117282685969278641493)
        ·
          refine ⟨3433679650404762655255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4688117282685969278641493 3433679650404762655255)
          ·
            rfl

theorem cell21_1218718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 12].length) (baseStart_1218718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218718 prefixEnd_1218718 := by exact prefixLift 1218718
  have htrace : WordTrace (prefixWord ++ tailWord_1218718) baseStart_1218718 baseEnd_1218718 := by
    simpa [prefixWord, tailWord_1218718, baseEnd_1218718] using wordTrace_append hprefix tailTrace_1218718
  have hstable : (prefixWord ++ tailWord_1218718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218718).length < 2 ^ (prefixWord ++ tailWord_1218718).sum := by decide
  have hdescent : baseEnd_1218718 < baseStart_1218718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218724 : List Nat := [2, 3, 1, 2, 4, 2, 2, 2, 3]
def baseStart_1218724 : Nat := 118140960795 + 1218724 * 2 ^ 59
def prefixEnd_1218724 : Nat := 4983230072969 + 3 ^ 40 * 1218724 * 2
def baseEnd_1218724 : Nat := 278129420964531097975643

theorem tailTrace_1218724 : CollatzResearch.WordTrace tailWord_1218724 prefixEnd_1218724 278129420964531097975643 := by
  unfold tailWord_1218724
  simp only [CollatzResearch.WordTrace]
  refine ⟨22225258018389282166659613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29633677357852376222212817 22225258018389282166659613)
  ·
    refine ⟨8334471756895980812497355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22225258018389282166659613 8334471756895980812497355)
    ·
      refine ⟨12501707635343971218746033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8334471756895980812497355 12501707635343971218746033)
      ·
        refine ⟨9376280726507978414059525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12501707635343971218746033 9376280726507978414059525)
        ·
          refine ⟨1758052636220245952636161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9376280726507978414059525 1758052636220245952636161)
          ·
            refine ⟨1318539477165184464477121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758052636220245952636161 1318539477165184464477121)
            ·
              refine ⟨988904607873888348357841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318539477165184464477121 988904607873888348357841)
              ·
                refine ⟨741678455905416261268381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 988904607873888348357841 741678455905416261268381)
                ·
                  refine ⟨278129420964531097975643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741678455905416261268381 278129420964531097975643)
                  ·
                    rfl

theorem cell21_1218724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_1218724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218724 prefixEnd_1218724 := by exact prefixLift 1218724
  have htrace : WordTrace (prefixWord ++ tailWord_1218724) baseStart_1218724 baseEnd_1218724 := by
    simpa [prefixWord, tailWord_1218724, baseEnd_1218724] using wordTrace_append hprefix tailTrace_1218724
  have hstable : (prefixWord ++ tailWord_1218724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218724).length < 2 ^ (prefixWord ++ tailWord_1218724).sum := by decide
  have hdescent : baseEnd_1218724 < baseStart_1218724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218766 : List Nat := [4, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_1218766 : Nat := 118140960795 + 1218766 * 2 ^ 59
def prefixEnd_1218766 : Nat := 4983230072969 + 3 ^ 40 * 1218766 * 2
def baseEnd_1218766 : Nat := 278139005936748358275557

theorem tailTrace_1218766 : CollatzResearch.WordTrace tailWord_1218766 prefixEnd_1218766 278139005936748358275557 := by
  unfold tailWord_1218766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5556505987828300688293519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29634698601750937004232101 5556505987828300688293519)
  ·
    refine ⟨8334758981742451032440279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5556505987828300688293519 8334758981742451032440279)
    ·
      refine ⟨12502138472613676548660419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8334758981742451032440279 12502138472613676548660419)
      ·
        refine ⟨18753207708920514822990629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12502138472613676548660419 18753207708920514822990629)
        ·
          refine ⟨3516226445422596529310743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18753207708920514822990629 3516226445422596529310743)
          ·
            refine ⟨5274339668133894793966115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3516226445422596529310743 5274339668133894793966115)
            ·
              refine ⟨7911509502200842190949173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274339668133894793966115 7911509502200842190949173)
              ·
                refine ⟨741704015831328955401485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7911509502200842190949173 741704015831328955401485)
                ·
                  refine ⟨278139005936748358275557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741704015831328955401485 278139005936748358275557)
                  ·
                    rfl

theorem cell21_1218766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_1218766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218766 prefixEnd_1218766 := by exact prefixLift 1218766
  have htrace : WordTrace (prefixWord ++ tailWord_1218766) baseStart_1218766 baseEnd_1218766 := by
    simpa [prefixWord, tailWord_1218766, baseEnd_1218766] using wordTrace_append hprefix tailTrace_1218766
  have hstable : (prefixWord ++ tailWord_1218766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218766).length < 2 ^ (prefixWord ++ tailWord_1218766).sum := by decide
  have hdescent : baseEnd_1218766 < baseStart_1218766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218839 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 6]
def baseStart_1218839 : Nat := 118140960795 + 1218839 * 2 ^ 59
def prefixEnd_1218839 : Nat := 4983230072969 + 3 ^ 40 * 1218839 * 2
def baseEnd_1218839 : Nat := 278155665531316453558741

theorem tailTrace_1218839 : CollatzResearch.WordTrace tailWord_1218839 prefixEnd_1218839 278155665531316453558741 := by
  unfold tailWord_1218839
  simp only [CollatzResearch.WordTrace]
  refine ⟨44454710431361938973755571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29636473620907959315837047 44454710431361938973755571)
  ·
    refine ⟨66682065647042908460633357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44454710431361938973755571 66682065647042908460633357)
    ·
      refine ⟨25005774617641090672737509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66682065647042908460633357 25005774617641090672737509)
      ·
        refine ⟨4688582740807704501138283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25005774617641090672737509 4688582740807704501138283)
        ·
          refine ⟨7032874111211556751707425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4688582740807704501138283 7032874111211556751707425)
          ·
            refine ⟨5274655583408667563780569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7032874111211556751707425 5274655583408667563780569)
            ·
              refine ⟨3955991687556500672835427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5274655583408667563780569 3955991687556500672835427)
              ·
                refine ⟨5933987531334751009253141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3955991687556500672835427 5933987531334751009253141)
                ·
                  refine ⟨278155665531316453558741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5933987531334751009253141 278155665531316453558741)
                  ·
                    rfl

theorem cell21_1218839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_1218839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218839 prefixEnd_1218839 := by exact prefixLift 1218839
  have htrace : WordTrace (prefixWord ++ tailWord_1218839) baseStart_1218839 baseEnd_1218839 := by
    simpa [prefixWord, tailWord_1218839, baseEnd_1218839] using wordTrace_append hprefix tailTrace_1218839
  have hstable : (prefixWord ++ tailWord_1218839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218839).length < 2 ^ (prefixWord ++ tailWord_1218839).sum := by decide
  have hdescent : baseEnd_1218839 < baseStart_1218839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218842 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 5]
def baseStart_1218842 : Nat := 118140960795 + 1218842 * 2 ^ 59
def prefixEnd_1218842 : Nat := 4983230072969 + 3 ^ 40 * 1218842 * 2
def baseEnd_1218842 : Nat := 278156350172189115008735

theorem tailTrace_1218842 : CollatzResearch.WordTrace tailWord_1218842 prefixEnd_1218842 278156350172189115008735 := by
  unfold tailWord_1218842
  simp only [CollatzResearch.WordTrace]
  refine ⟨11113704962587767621528695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29636546566900713657409853 11113704962587767621528695)
  ·
    refine ⟨16670557443881651432293043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11113704962587767621528695 16670557443881651432293043)
    ·
      refine ⟨25005836165822477148439565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16670557443881651432293043 25005836165822477148439565)
      ·
        refine ⟨9377188562183428930664837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25005836165822477148439565 9377188562183428930664837)
        ·
          refine ⟨1758222855409392924499657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9377188562183428930664837 1758222855409392924499657)
          ·
            refine ⟨1318667141557044693374743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758222855409392924499657 1318667141557044693374743)
            ·
              refine ⟨1978000712335567040062115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318667141557044693374743 1978000712335567040062115)
              ·
                refine ⟨2967001068503350560093173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1978000712335567040062115 2967001068503350560093173)
                ·
                  refine ⟨278156350172189115008735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2967001068503350560093173 278156350172189115008735)
                  ·
                    rfl

theorem cell21_1218842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_1218842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218842 prefixEnd_1218842 := by exact prefixLift 1218842
  have htrace : WordTrace (prefixWord ++ tailWord_1218842) baseStart_1218842 baseEnd_1218842 := by
    simpa [prefixWord, tailWord_1218842, baseEnd_1218842] using wordTrace_append hprefix tailTrace_1218842
  have hstable : (prefixWord ++ tailWord_1218842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218842).length < 2 ^ (prefixWord ++ tailWord_1218842).sum := by decide
  have hdescent : baseEnd_1218842 < baseStart_1218842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218915 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 4]
def baseStart_1218915 : Nat := 118140960795 + 1218915 * 2 ^ 59
def prefixEnd_1218915 : Nat := 4983230072969 + 3 ^ 40 * 1218915 * 2
def baseEnd_1218915 : Nat := 278173009766757210291919

theorem tailTrace_1218915 : CollatzResearch.WordTrace tailWord_1218915 prefixEnd_1218915 278173009766757210291919 := by
  unfold tailWord_1218915
  simp only [CollatzResearch.WordTrace]
  refine ⟨44457482379086603953522199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29638321586057735969014799 44457482379086603953522199)
  ·
    refine ⟨66686223568629905930283299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44457482379086603953522199 66686223568629905930283299)
    ·
      refine ⟨100029335352944858895424949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66686223568629905930283299 100029335352944858895424949)
      ·
        refine ⟨9377750189338580521446089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100029335352944858895424949 9377750189338580521446089)
        ·
          refine ⟨7033312642003935391084567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9377750189338580521446089 7033312642003935391084567)
          ·
            refine ⟨10549968963005903086626851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7033312642003935391084567 10549968963005903086626851)
            ·
              refine ⟨15824953444508854629940277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10549968963005903086626851 15824953444508854629940277)
              ·
                refine ⟨1483589385422705121556901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15824953444508854629940277 1483589385422705121556901)
                ·
                  refine ⟨278173009766757210291919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1483589385422705121556901 278173009766757210291919)
                  ·
                    rfl

theorem cell21_1218915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 4].length) (baseStart_1218915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218915 prefixEnd_1218915 := by exact prefixLift 1218915
  have htrace : WordTrace (prefixWord ++ tailWord_1218915) baseStart_1218915 baseEnd_1218915 := by
    simpa [prefixWord, tailWord_1218915, baseEnd_1218915] using wordTrace_append hprefix tailTrace_1218915
  have hstable : (prefixWord ++ tailWord_1218915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218915).length < 2 ^ (prefixWord ++ tailWord_1218915).sum := by decide
  have hdescent : baseEnd_1218915 < baseStart_1218915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1218986 : List Nat := [3, 1, 6, 1, 2, 1, 1, 3, 3]
def baseStart_1218986 : Nat := 118140960795 + 1218986 * 2 ^ 59
def prefixEnd_1218986 : Nat := 4983230072969 + 3 ^ 40 * 1218986 * 2
def baseEnd_1218986 : Nat := 278189212934076864608441

theorem tailTrace_1218986 : CollatzResearch.WordTrace tailWord_1218986 prefixEnd_1218986 278189212934076864608441 := by
  unfold tailWord_1218986
  simp only [CollatzResearch.WordTrace]
  refine ⟨11115017990457345769839203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29640047974552922052904541 11115017990457345769839203)
  ·
    refine ⟨16672526985686018654758805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11115017990457345769839203 16672526985686018654758805)
    ·
      refine ⟨781524702454032124441819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16672526985686018654758805 781524702454032124441819)
      ·
        refine ⟨1172287053681048186662729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 781524702454032124441819 1172287053681048186662729)
        ·
          refine ⟨879215290260786139997047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1172287053681048186662729 879215290260786139997047)
          ·
            refine ⟨1318822935391179209995571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879215290260786139997047 1318822935391179209995571)
            ·
              refine ⟨1978234403086768814993357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318822935391179209995571 1978234403086768814993357)
              ·
                refine ⟨741837901157538305622509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1978234403086768814993357 741837901157538305622509)
                ·
                  refine ⟨278189212934076864608441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741837901157538305622509 278189212934076864608441)
                  ·
                    rfl

theorem cell21_1218986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 3].length) (baseStart_1218986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1218986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1218986 prefixEnd_1218986 := by exact prefixLift 1218986
  have htrace : WordTrace (prefixWord ++ tailWord_1218986) baseStart_1218986 baseEnd_1218986 := by
    simpa [prefixWord, tailWord_1218986, baseEnd_1218986] using wordTrace_append hprefix tailTrace_1218986
  have hstable : (prefixWord ++ tailWord_1218986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1218986).length < 2 ^ (prefixWord ++ tailWord_1218986).sum := by decide
  have hdescent : baseEnd_1218986 < baseStart_1218986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1218986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219005 : List Nat := [1, 4, 1, 2, 2, 2, 9]
def baseStart_1219005 : Nat := 118140960795 + 1219005 * 2 ^ 59
def prefixEnd_1219005 : Nat := 4983230072969 + 3 ^ 40 * 1219005 * 2
def baseEnd_1219005 : Nat := 30910394332548561532415

theorem tailTrace_1219005 : CollatzResearch.WordTrace tailWord_1219005 prefixEnd_1219005 30910394332548561532415 := by
  unfold tailWord_1219005
  simp only [CollatzResearch.WordTrace]
  refine ⟨44460764948760549324298469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29640509965840366216198979 44460764948760549324298469)
  ·
    refine ⟨8336393427892602998305963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44460764948760549324298469 8336393427892602998305963)
    ·
      refine ⟨12504590141838904497458945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8336393427892602998305963 12504590141838904497458945)
      ·
        refine ⟨9378442606379178373094209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12504590141838904497458945 9378442606379178373094209)
        ·
          refine ⟨7033831954784383779820657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9378442606379178373094209 7033831954784383779820657)
          ·
            refine ⟨5275373966088287834865493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7033831954784383779820657 5275373966088287834865493)
            ·
              refine ⟨30910394332548561532415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5275373966088287834865493 30910394332548561532415)
              ·
                rfl

theorem cell21_1219005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 9].length) (baseStart_1219005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219005 prefixEnd_1219005 := by exact prefixLift 1219005
  have htrace : WordTrace (prefixWord ++ tailWord_1219005) baseStart_1219005 baseEnd_1219005 := by
    simpa [prefixWord, tailWord_1219005, baseEnd_1219005] using wordTrace_append hprefix tailTrace_1219005
  have hstable : (prefixWord ++ tailWord_1219005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219005).length < 2 ^ (prefixWord ++ tailWord_1219005).sum := by decide
  have hdescent : baseEnd_1219005 < baseStart_1219005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219118 : List Nat := [4, 1, 3, 1, 4, 1, 1, 2, 4]
def baseStart_1219118 : Nat := 118140960795 + 1219118 * 2 ^ 59
def prefixEnd_1219118 : Nat := 4983230072969 + 3 ^ 40 * 1219118 * 2
def baseEnd_1219118 : Nat := 278219337132473968408171

theorem tailTrace_1219118 : CollatzResearch.WordTrace tailWord_1219118 prefixEnd_1219118 278219337132473968408171 := by
  unfold tailWord_1219118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5558110799668896202895251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29643257598234113082108005 5558110799668896202895251)
  ·
    refine ⟨8337166199503344304342877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5558110799668896202895251 8337166199503344304342877)
    ·
      refine ⟨3126437324813754114128579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8337166199503344304342877 3126437324813754114128579)
      ·
        refine ⟨4689655987220631171192869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3126437324813754114128579 4689655987220631171192869)
        ·
          refine ⟨879310497603868344598663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4689655987220631171192869 879310497603868344598663)
          ·
            refine ⟨1318965746405802516897995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879310497603868344598663 1318965746405802516897995)
            ·
              refine ⟨1978448619608703775346993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1318965746405802516897995 1978448619608703775346993)
              ·
                refine ⟨1483836464706527831510245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1978448619608703775346993 1483836464706527831510245)
                ·
                  refine ⟨278219337132473968408171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1483836464706527831510245 278219337132473968408171)
                  ·
                    rfl

theorem cell21_1219118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_1219118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219118 prefixEnd_1219118 := by exact prefixLift 1219118
  have htrace : WordTrace (prefixWord ++ tailWord_1219118) baseStart_1219118 baseEnd_1219118 := by
    simpa [prefixWord, tailWord_1219118, baseEnd_1219118] using wordTrace_append hprefix tailTrace_1219118
  have hstable : (prefixWord ++ tailWord_1219118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219118).length < 2 ^ (prefixWord ++ tailWord_1219118).sum := by decide
  have hdescent : baseEnd_1219118 < baseStart_1219118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219129 : List Nat := [1, 2, 1, 5, 1, 1, 1, 6, 3]
def baseStart_1219129 : Nat := 118140960795 + 1219129 * 2 ^ 59
def prefixEnd_1219129 : Nat := 4983230072969 + 3 ^ 40 * 1219129 * 2
def baseEnd_1219129 : Nat := 278221847482340393724815

theorem tailTrace_1219129 : CollatzResearch.WordTrace tailWord_1219129 prefixEnd_1219129 278221847482340393724815 := by
  unfold tailWord_1219129
  simp only [CollatzResearch.WordTrace]
  refine ⟨44465287600311318501812441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29643525066874212334541627 44465287600311318501812441)
  ·
    refine ⟨33348965700233488876359331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44465287600311318501812441 33348965700233488876359331)
    ·
      refine ⟨50023448550350233314538997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33348965700233488876359331 50023448550350233314538997)
      ·
        refine ⟨4689698301595334373238031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50023448550350233314538997 4689698301595334373238031)
        ·
          refine ⟨7034547452393001559857047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4689698301595334373238031 7034547452393001559857047)
          ·
            refine ⟨10551821178589502339785571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7034547452393001559857047 10551821178589502339785571)
            ·
              refine ⟨15827731767884253509678357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10551821178589502339785571 15827731767884253509678357)
              ·
                refine ⟨741924926619574383266173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15827731767884253509678357 741924926619574383266173)
                ·
                  refine ⟨278221847482340393724815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741924926619574383266173 278221847482340393724815)
                  ·
                    rfl

theorem cell21_1219129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 3].length) (baseStart_1219129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219129 prefixEnd_1219129 := by exact prefixLift 1219129
  have htrace : WordTrace (prefixWord ++ tailWord_1219129) baseStart_1219129 baseEnd_1219129 := by
    simpa [prefixWord, tailWord_1219129, baseEnd_1219129] using wordTrace_append hprefix tailTrace_1219129
  have hstable : (prefixWord ++ tailWord_1219129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219129).length < 2 ^ (prefixWord ++ tailWord_1219129).sum := by decide
  have hdescent : baseEnd_1219129 < baseStart_1219129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219233 : List Nat := [1, 2, 3, 3, 3, 9]
def baseStart_1219233 : Nat := 118140960795 + 1219233 * 2 ^ 59
def prefixEnd_1219233 : Nat := 4983230072969 + 3 ^ 40 * 1219233 * 2
def baseEnd_1219233 : Nat := 10305391914787382370047

theorem tailTrace_1219233 : CollatzResearch.WordTrace tailWord_1219233 prefixEnd_1219233 10305391914787382370047 := by
  unfold tailWord_1219233
  simp only [CollatzResearch.WordTrace]
  refine ⟨44469080791934544263598353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29646053861289696175732235 44469080791934544263598353)
  ·
    refine ⟨33351810593950908197698765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44469080791934544263598353 33351810593950908197698765)
    ·
      refine ⟨12506928972731590574137037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33351810593950908197698765 12506928972731590574137037)
      ·
        refine ⟨4690098364774346465301389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12506928972731590574137037 4690098364774346465301389)
        ·
          refine ⟨1758786886790379924488021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4690098364774346465301389 1758786886790379924488021)
          ·
            refine ⟨10305391914787382370047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1758786886790379924488021 10305391914787382370047)
            ·
              rfl

theorem cell21_1219233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 9].length) (baseStart_1219233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219233 prefixEnd_1219233 := by exact prefixLift 1219233
  have htrace : WordTrace (prefixWord ++ tailWord_1219233) baseStart_1219233 baseEnd_1219233 := by
    simpa [prefixWord, tailWord_1219233, baseEnd_1219233] using wordTrace_append hprefix tailTrace_1219233
  have hstable : (prefixWord ++ tailWord_1219233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219233).length < 2 ^ (prefixWord ++ tailWord_1219233).sum := by decide
  have hdescent : baseEnd_1219233 < baseStart_1219233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219239 : List Nat := [1, 1, 6, 3, 1, 1, 1, 4, 3]
def baseStart_1219239 : Nat := 118140960795 + 1219239 * 2 ^ 59
def prefixEnd_1219239 : Nat := 4983230072969 + 3 ^ 40 * 1219239 * 2
def baseEnd_1219239 : Nat := 278246950981004646891257

theorem tailTrace_1219239 : CollatzResearch.WordTrace tailWord_1219239 prefixEnd_1219239 278246950981004646891257 := by
  unfold tailWord_1219239
  simp only [CollatzResearch.WordTrace]
  refine ⟨44469299629912807288316771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29646199753275204858877847 44469299629912807288316771)
  ·
    refine ⟨66703949444869210932475157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44469299629912807288316771 66703949444869210932475157)
    ·
      refine ⟨3126747630228244262459773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66703949444869210932475157 3126747630228244262459773)
      ·
        refine ⟨1172530361335591598422415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3126747630228244262459773 1172530361335591598422415)
        ·
          refine ⟨1758795542003387397633623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172530361335591598422415 1758795542003387397633623)
          ·
            refine ⟨2638193313005081096450435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758795542003387397633623 2638193313005081096450435)
            ·
              refine ⟨3957289969507621644675653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638193313005081096450435 3957289969507621644675653)
              ·
                refine ⟨741991869282679058376685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3957289969507621644675653 741991869282679058376685)
                ·
                  refine ⟨278246950981004646891257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 741991869282679058376685 278246950981004646891257)
                  ·
                    rfl

theorem cell21_1219239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 3].length) (baseStart_1219239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219239 prefixEnd_1219239 := by exact prefixLift 1219239
  have htrace : WordTrace (prefixWord ++ tailWord_1219239) baseStart_1219239 baseEnd_1219239 := by
    simpa [prefixWord, tailWord_1219239, baseEnd_1219239] using wordTrace_append hprefix tailTrace_1219239
  have hstable : (prefixWord ++ tailWord_1219239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219239).length < 2 ^ (prefixWord ++ tailWord_1219239).sum := by decide
  have hdescent : baseEnd_1219239 < baseStart_1219239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219264 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 5]
def baseStart_1219264 : Nat := 118140960795 + 1219264 * 2 ^ 59
def prefixEnd_1219264 : Nat := 4983230072969 + 3 ^ 40 * 1219264 * 2
def baseEnd_1219264 : Nat := 278252656321610158974539

theorem tailTrace_1219264 : CollatzResearch.WordTrace tailWord_1219264 prefixEnd_1219264 278252656321610158974539 := by
  unfold tailWord_1219264
  simp only [CollatzResearch.WordTrace]
  refine ⟨22235105727411118278988423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29646807636548157705317897 22235105727411118278988423)
  ·
    refine ⟨33352658591116677418482635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22235105727411118278988423 33352658591116677418482635)
    ·
      refine ⟨50028987886675016127723953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33352658591116677418482635 50028987886675016127723953)
      ·
        refine ⟨37521740915006262095792965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50028987886675016127723953 37521740915006262095792965)
        ·
          refine ⟨7035326421563674142961181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37521740915006262095792965 7035326421563674142961181)
          ·
            refine ⟨2638247408086377803610443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7035326421563674142961181 2638247408086377803610443)
            ·
              refine ⟨3957371112129566705415665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638247408086377803610443 3957371112129566705415665)
              ·
                refine ⟨2968028334097175029061749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3957371112129566705415665 2968028334097175029061749)
                ·
                  refine ⟨278252656321610158974539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2968028334097175029061749 278252656321610158974539)
                  ·
                    rfl

theorem cell21_1219264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_1219264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219264 prefixEnd_1219264 := by exact prefixLift 1219264
  have htrace : WordTrace (prefixWord ++ tailWord_1219264) baseStart_1219264 baseEnd_1219264 := by
    simpa [prefixWord, tailWord_1219264, baseEnd_1219264] using wordTrace_append hprefix tailTrace_1219264
  have hstable : (prefixWord ++ tailWord_1219264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219264).length < 2 ^ (prefixWord ++ tailWord_1219264).sum := by decide
  have hdescent : baseEnd_1219264 < baseStart_1219264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219281 : List Nat := [1, 2, 2, 1, 2, 3, 4, 3, 3]
def baseStart_1219281 : Nat := 118140960795 + 1219281 * 2 ^ 59
def prefixEnd_1219281 : Nat := 4983230072969 + 3 ^ 40 * 1219281 * 2
def baseEnd_1219281 : Nat := 278256535953221907191171

theorem tailTrace_1219281 : CollatzResearch.WordTrace tailWord_1219281 prefixEnd_1219281 278256535953221907191171 := by
  unfold tailWord_1219281
  simp only [CollatzResearch.WordTrace]
  refine ⟨44470831495760648461345697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29647220997173765640897131 44470831495760648461345697)
  ·
    refine ⟨33353123621820486346009273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44470831495760648461345697 33353123621820486346009273)
    ·
      refine ⟨25014842716365364759506955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33353123621820486346009273 25014842716365364759506955)
      ·
        refine ⟨37522264074548047139260433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25014842716365364759506955 37522264074548047139260433)
        ·
          refine ⟨28141698055911035354445325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37522264074548047139260433 28141698055911035354445325)
          ·
            refine ⟨10553136770966638257916997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28141698055911035354445325 10553136770966638257916997)
            ·
              refine ⟨1978713144556244673359437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10553136770966638257916997 1978713144556244673359437)
              ·
                refine ⟨742017429208591752509789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1978713144556244673359437 742017429208591752509789)
                ·
                  refine ⟨278256535953221907191171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742017429208591752509789 278256535953221907191171)
                  ·
                    rfl

theorem cell21_1219281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 3, 3].length) (baseStart_1219281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219281 prefixEnd_1219281 := by exact prefixLift 1219281
  have htrace : WordTrace (prefixWord ++ tailWord_1219281) baseStart_1219281 baseEnd_1219281 := by
    simpa [prefixWord, tailWord_1219281, baseEnd_1219281] using wordTrace_append hprefix tailTrace_1219281
  have hstable : (prefixWord ++ tailWord_1219281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219281).length < 2 ^ (prefixWord ++ tailWord_1219281).sum := by decide
  have hdescent : baseEnd_1219281 < baseStart_1219281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219295 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 4]
def baseStart_1219295 : Nat := 118140960795 + 1219295 * 2 ^ 59
def prefixEnd_1219295 : Nat := 4983230072969 + 3 ^ 40 * 1219295 * 2
def baseEnd_1219295 : Nat := 278259730943960993957809

theorem tailTrace_1219295 : CollatzResearch.WordTrace tailWord_1219295 prefixEnd_1219295 278259730943960993957809 := by
  unfold tailWord_1219295
  simp only [CollatzResearch.WordTrace]
  refine ⟨44471342117709928852355339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29647561411806619234903559 44471342117709928852355339)
  ·
    refine ⟨66707013176564893278533009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44471342117709928852355339 66707013176564893278533009)
    ·
      refine ⟨50030259882423669958899757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66707013176564893278533009 50030259882423669958899757)
      ·
        refine ⟨18761347455908876234587409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50030259882423669958899757 18761347455908876234587409)
        ·
          refine ⟨14071010591931657175940557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18761347455908876234587409 14071010591931657175940557)
          ·
            refine ⟨5276628971974371440977709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14071010591931657175940557 5276628971974371440977709)
            ·
              refine ⟨1978735864490389290366641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5276628971974371440977709 1978735864490389290366641)
              ·
                refine ⟨1484051898367791967774981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1978735864490389290366641 1484051898367791967774981)
                ·
                  refine ⟨278259730943960993957809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484051898367791967774981 278259730943960993957809)
                  ·
                    rfl

theorem cell21_1219295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 4].length) (baseStart_1219295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219295 prefixEnd_1219295 := by exact prefixLift 1219295
  have htrace : WordTrace (prefixWord ++ tailWord_1219295) baseStart_1219295 baseEnd_1219295 := by
    simpa [prefixWord, tailWord_1219295, baseEnd_1219295] using wordTrace_append hprefix tailTrace_1219295
  have hstable : (prefixWord ++ tailWord_1219295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219295).length < 2 ^ (prefixWord ++ tailWord_1219295).sum := by decide
  have hdescent : baseEnd_1219295 < baseStart_1219295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219309 : List Nat := [1, 5, 1, 2, 1, 1, 2, 8]
def baseStart_1219309 : Nat := 118140960795 + 1219309 * 2 ^ 59
def prefixEnd_1219309 : Nat := 4983230072969 + 3 ^ 40 * 1219309 * 2
def baseEnd_1219309 : Nat := 92754308644900026908149

theorem tailTrace_1219309 : CollatzResearch.WordTrace tailWord_1219309 prefixEnd_1219309 92754308644900026908149 := by
  unfold tailWord_1219309
  simp only [CollatzResearch.WordTrace]
  refine ⟨44471852739659209243364981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29647901826439472828909987 44471852739659209243364981)
  ·
    refine ⟨4169236194343050866565467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44471852739659209243364981 4169236194343050866565467)
    ·
      refine ⟨6253854291514576299848201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4169236194343050866565467 6253854291514576299848201)
      ·
        refine ⟨4690390718635932224886151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6253854291514576299848201 4690390718635932224886151)
        ·
          refine ⟨7035586077953898337329227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4690390718635932224886151 7035586077953898337329227)
          ·
            refine ⟨10553379116930847505993841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7035586077953898337329227 10553379116930847505993841)
            ·
              refine ⟨7915034337698135629495381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10553379116930847505993841 7915034337698135629495381)
              ·
                refine ⟨92754308644900026908149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7915034337698135629495381 92754308644900026908149)
                ·
                  rfl

theorem cell21_1219309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 8].length) (baseStart_1219309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219309 prefixEnd_1219309 := by exact prefixLift 1219309
  have htrace : WordTrace (prefixWord ++ tailWord_1219309) baseStart_1219309 baseEnd_1219309 := by
    simpa [prefixWord, tailWord_1219309, baseEnd_1219309] using wordTrace_append hprefix tailTrace_1219309
  have hstable : (prefixWord ++ tailWord_1219309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219309).length < 2 ^ (prefixWord ++ tailWord_1219309).sum := by decide
  have hdescent : baseEnd_1219309 < baseStart_1219309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219326 : List Nat := [4, 2, 2, 1, 2, 2, 1, 7]
def baseStart_1219326 : Nat := 118140960795 + 1219326 * 2 ^ 59
def prefixEnd_1219326 : Nat := 4983230072969 + 3 ^ 40 * 1219326 * 2
def baseEnd_1219326 : Nat := 92755601855437276313693

theorem tailTrace_1219326 : CollatzResearch.WordTrace tailWord_1219326 prefixEnd_1219326 92755601855437276313693 := by
  unfold tailWord_1219326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5559059097574702643341729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29648315187065080764489221 5559059097574702643341729)
  ·
    refine ⟨4169294323181026982506297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5559059097574702643341729 4169294323181026982506297)
    ·
      refine ⟨3126970742385770236879723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4169294323181026982506297 3126970742385770236879723)
      ·
        refine ⟨4690456113578655355319585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3126970742385770236879723 4690456113578655355319585)
        ·
          refine ⟨3517842085183991516489689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4690456113578655355319585 3517842085183991516489689)
          ·
            refine ⟨2638381563887993637367267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3517842085183991516489689 2638381563887993637367267)
            ·
              refine ⟨3957572345831990456050901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638381563887993637367267 3957572345831990456050901)
              ·
                refine ⟨92755601855437276313693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3957572345831990456050901 92755601855437276313693)
                ·
                  rfl

theorem cell21_1219326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_1219326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219326 prefixEnd_1219326 := by exact prefixLift 1219326
  have htrace : WordTrace (prefixWord ++ tailWord_1219326) baseStart_1219326 baseEnd_1219326 := by
    simpa [prefixWord, tailWord_1219326, baseEnd_1219326] using wordTrace_append hprefix tailTrace_1219326
  have hstable : (prefixWord ++ tailWord_1219326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219326).length < 2 ^ (prefixWord ++ tailWord_1219326).sum := by decide
  have hdescent : baseEnd_1219326 < baseStart_1219326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219354 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_1219354 : Nat := 118140960795 + 1219354 * 2 ^ 59
def prefixEnd_1219354 : Nat := 4983230072969 + 3 ^ 40 * 1219354 * 2
def baseEnd_1219354 : Nat := 278273195547790002474355

theorem tailTrace_1219354 : CollatzResearch.WordTrace tailWord_1219354 prefixEnd_1219354 278273195547790002474355 := by
  unfold tailWord_1219354
  simp only [CollatzResearch.WordTrace]
  refine ⟨11118373506124045482188279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29648996016330787952502077 11118373506124045482188279)
  ·
    refine ⟨16677560259186068223282419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11118373506124045482188279 16677560259186068223282419)
    ·
      refine ⟨25016340388779102334923629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16677560259186068223282419 25016340388779102334923629)
      ·
        refine ⟨9381127645792163375596361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25016340388779102334923629 9381127645792163375596361)
        ·
          refine ⟨7035845734344122531697271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9381127645792163375596361 7035845734344122531697271)
          ·
            refine ⟨10553768601516183797545907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7035845734344122531697271 10553768601516183797545907)
            ·
              refine ⟨15830652902274275696318861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10553768601516183797545907 15830652902274275696318861)
              ·
                refine ⟨5936494838352853386119573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15830652902274275696318861 5936494838352853386119573)
                ·
                  refine ⟨278273195547790002474355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5936494838352853386119573 278273195547790002474355)
                  ·
                    rfl

theorem cell21_1219354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_1219354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219354 prefixEnd_1219354 := by exact prefixLift 1219354
  have htrace : WordTrace (prefixWord ++ tailWord_1219354) baseStart_1219354 baseEnd_1219354 := by
    simpa [prefixWord, tailWord_1219354, baseEnd_1219354] using wordTrace_append hprefix tailTrace_1219354
  have hstable : (prefixWord ++ tailWord_1219354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219354).length < 2 ^ (prefixWord ++ tailWord_1219354).sum := by decide
  have hdescent : baseEnd_1219354 < baseStart_1219354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219405 : List Nat := [1, 6, 1, 2, 2, 1, 2, 2, 4]
def baseStart_1219405 : Nat := 118140960795 + 1219405 * 2 ^ 59
def prefixEnd_1219405 : Nat := 4983230072969 + 3 ^ 40 * 1219405 * 2
def baseEnd_1219405 : Nat := 278284834442625247124251

theorem tailTrace_1219405 : CollatzResearch.WordTrace tailWord_1219405 prefixEnd_1219405 278284834442625247124251 := by
  unfold tailWord_1219405
  simp only [CollatzResearch.WordTrace]
  refine ⟨44475354147311417638859669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29650236098207611759239779 44475354147311417638859669)
  ·
    refine ⟨2084782225655222701821547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44475354147311417638859669 2084782225655222701821547)
    ·
      refine ⟨3127173338482834052732321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2084782225655222701821547 3127173338482834052732321)
      ·
        refine ⟨2345380003862125539549241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3127173338482834052732321 2345380003862125539549241)
        ·
          refine ⟨1759035002896594154661931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2345380003862125539549241 1759035002896594154661931)
          ·
            refine ⟨2638552504344891231992897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1759035002896594154661931 2638552504344891231992897)
            ·
              refine ⟨1978914378258668423994673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2638552504344891231992897 1978914378258668423994673)
              ·
                refine ⟨1484185783694001317996005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1978914378258668423994673 1484185783694001317996005)
                ·
                  refine ⟨278284834442625247124251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484185783694001317996005 278284834442625247124251)
                  ·
                    rfl

theorem cell21_1219405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_1219405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219405 prefixEnd_1219405 := by exact prefixLift 1219405
  have htrace : WordTrace (prefixWord ++ tailWord_1219405) baseStart_1219405 baseEnd_1219405 := by
    simpa [prefixWord, tailWord_1219405, baseEnd_1219405] using wordTrace_append hprefix tailTrace_1219405
  have hstable : (prefixWord ++ tailWord_1219405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219405).length < 2 ^ (prefixWord ++ tailWord_1219405).sum := by decide
  have hdescent : baseEnd_1219405 < baseStart_1219405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219464 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 4]
def baseStart_1219464 : Nat := 118140960795 + 1219464 * 2 ^ 59
def prefixEnd_1219464 : Nat := 4983230072969 + 3 ^ 40 * 1219464 * 2
def baseEnd_1219464 : Nat := 278298299046454255640797

theorem tailTrace_1219464 : CollatzResearch.WordTrace tailWord_1219464 prefixEnd_1219464 278298299046454255640797 := by
  unfold tailWord_1219464
  simp only [CollatzResearch.WordTrace]
  refine ⟨22238753027048835357628723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29651670702731780476838297 22238753027048835357628723)
  ·
    refine ⟨33358129540573253036443085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22238753027048835357628723 33358129540573253036443085)
    ·
      refine ⟨12509298577714969888666157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33358129540573253036443085 12509298577714969888666157)
      ·
        refine ⟨4690986966643113708249809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12509298577714969888666157 4690986966643113708249809)
        ·
          refine ⟨3518240224982335281187357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4690986966643113708249809 3518240224982335281187357)
          ·
            refine ⟨1319340084368375730445259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3518240224982335281187357 1319340084368375730445259)
            ·
              refine ⟨1979010126552563595667889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319340084368375730445259 1979010126552563595667889)
              ·
                refine ⟨1484257594914422696750917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1979010126552563595667889 1484257594914422696750917)
                ·
                  refine ⟨278298299046454255640797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484257594914422696750917 278298299046454255640797)
                  ·
                    rfl

theorem cell21_1219464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_1219464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219464 prefixEnd_1219464 := by exact prefixLift 1219464
  have htrace : WordTrace (prefixWord ++ tailWord_1219464) baseStart_1219464 baseEnd_1219464 := by
    simpa [prefixWord, tailWord_1219464, baseEnd_1219464] using wordTrace_append hprefix tailTrace_1219464
  have hstable : (prefixWord ++ tailWord_1219464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219464).length < 2 ^ (prefixWord ++ tailWord_1219464).sum := by decide
  have hdescent : baseEnd_1219464 < baseStart_1219464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219495 : List Nat := [1, 1, 6, 1, 3, 2, 2, 5]
def baseStart_1219495 : Nat := 118140960795 + 1219495 * 2 ^ 59
def prefixEnd_1219495 : Nat := 4983230072969 + 3 ^ 40 * 1219495 * 2
def baseEnd_1219495 : Nat := 92768457889601696874689

theorem tailTrace_1219495 : CollatzResearch.WordTrace tailWord_1219495 prefixEnd_1219495 92768457889601696874689 := by
  unfold tailWord_1219495
  simp only [CollatzResearch.WordTrace]
  refine ⟨44478636716985363009635939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29652424477990242006423959 44478636716985363009635939)
  ·
    refine ⟨66717955075478044514453909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44478636716985363009635939 66717955075478044514453909)
    ·
      refine ⟨3127404144163033336615027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66717955075478044514453909 3127404144163033336615027)
      ·
        refine ⟨4691106216244550004922541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3127404144163033336615027 4691106216244550004922541)
        ·
          refine ⟨1759164831091706251845953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4691106216244550004922541 1759164831091706251845953)
          ·
            refine ⟨1319373623318779688884465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1759164831091706251845953 1319373623318779688884465)
            ·
              refine ⟨989530217489084766663349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1319373623318779688884465 989530217489084766663349)
              ·
                refine ⟨92768457889601696874689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 989530217489084766663349 92768457889601696874689)
                ·
                  rfl

theorem cell21_1219495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 5].length) (baseStart_1219495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219495 prefixEnd_1219495 := by exact prefixLift 1219495
  have htrace : WordTrace (prefixWord ++ tailWord_1219495) baseStart_1219495 baseEnd_1219495 := by
    simpa [prefixWord, tailWord_1219495, baseEnd_1219495] using wordTrace_append hprefix tailTrace_1219495
  have hstable : (prefixWord ++ tailWord_1219495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219495).length < 2 ^ (prefixWord ++ tailWord_1219495).sum := by decide
  have hdescent : baseEnd_1219495 < baseStart_1219495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219520 : List Nat := [2, 1, 1, 2, 3, 3, 9]
def baseStart_1219520 : Nat := 118140960795 + 1219520 * 2 ^ 59
def prefixEnd_1219520 : Nat := 4983230072969 + 3 ^ 40 * 1219520 * 2
def baseEnd_1219520 : Nat := 30923453223267844745261

theorem tailTrace_1219520 : CollatzResearch.WordTrace tailWord_1219520 prefixEnd_1219520 30923453223267844745261 := by
  unfold tailWord_1219520
  simp only [CollatzResearch.WordTrace]
  refine ⟨22239774270947396139648007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29653032361263194852864009 22239774270947396139648007)
  ·
    refine ⟨33359661406421094209472011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22239774270947396139648007 33359661406421094209472011)
    ·
      refine ⟨50039492109631641314208017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33359661406421094209472011 50039492109631641314208017)
      ·
        refine ⟨37529619082223730985656013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50039492109631641314208017 37529619082223730985656013)
        ·
          refine ⟨14073607155833899119621005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37529619082223730985656013 14073607155833899119621005)
          ·
            refine ⟨5277602683437712169857877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14073607155833899119621005 5277602683437712169857877)
            ·
              refine ⟨30923453223267844745261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5277602683437712169857877 30923453223267844745261)
              ·
                rfl

theorem cell21_1219520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 9].length) (baseStart_1219520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219520 prefixEnd_1219520 := by exact prefixLift 1219520
  have htrace : WordTrace (prefixWord ++ tailWord_1219520) baseStart_1219520 baseEnd_1219520 := by
    simpa [prefixWord, tailWord_1219520, baseEnd_1219520] using wordTrace_append hprefix tailTrace_1219520
  have hstable : (prefixWord ++ tailWord_1219520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219520).length < 2 ^ (prefixWord ++ tailWord_1219520).sum := by decide
  have hdescent : baseEnd_1219520 < baseStart_1219520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219540 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 4]
def baseStart_1219540 : Nat := 118140960795 + 1219540 * 2 ^ 59
def prefixEnd_1219540 : Nat := 4983230072969 + 3 ^ 40 * 1219540 * 2
def baseEnd_1219540 : Nat := 278315643281895012373975

theorem tailTrace_1219540 : CollatzResearch.WordTrace tailWord_1219540 prefixEnd_1219540 278315643281895012373975 := by
  unfold tailWord_1219540
  simp only [CollatzResearch.WordTrace]
  refine ⟨22240139000911167847512037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29653518667881557130016049 22240139000911167847512037)
  ·
    refine ⟨4170026062670843971408507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22240139000911167847512037 4170026062670843971408507)
    ·
      refine ⟨6255039094006265957112761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4170026062670843971408507 6255039094006265957112761)
      ·
        refine ⟨4691279320504699467834571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6255039094006265957112761 4691279320504699467834571)
        ·
          refine ⟨7036918980757049201751857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4691279320504699467834571 7036918980757049201751857)
          ·
            refine ⟨5277689235567786901313893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7036918980757049201751857 5277689235567786901313893)
            ·
              refine ⟨989566731668960043996355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5277689235567786901313893 989566731668960043996355)
              ·
                refine ⟨1484350097503440065994533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989566731668960043996355 1484350097503440065994533)
                ·
                  refine ⟨278315643281895012373975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484350097503440065994533 278315643281895012373975)
                  ·
                    rfl

theorem cell21_1219540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_1219540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219540 prefixEnd_1219540 := by exact prefixLift 1219540
  have htrace : WordTrace (prefixWord ++ tailWord_1219540) baseStart_1219540 baseEnd_1219540 := by
    simpa [prefixWord, tailWord_1219540, baseEnd_1219540] using wordTrace_append hprefix tailTrace_1219540
  have hstable : (prefixWord ++ tailWord_1219540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219540).length < 2 ^ (prefixWord ++ tailWord_1219540).sum := by decide
  have hdescent : baseEnd_1219540 < baseStart_1219540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219554 : List Nat := [3, 3, 3, 1, 1, 1, 2, 7]
def baseStart_1219554 : Nat := 118140960795 + 1219554 * 2 ^ 59
def prefixEnd_1219554 : Nat := 4983230072969 + 3 ^ 40 * 1219554 * 2
def baseEnd_1219554 : Nat := 92772946090878033046871

theorem tailTrace_1219554 : CollatzResearch.WordTrace tailWord_1219554 prefixEnd_1219554 92772946090878033046871 := by
  unfold tailWord_1219554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11120197155942904021508429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29653859082514410724022477 11120197155942904021508429)
  ·
    refine ⟨4170073933478589008065661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11120197155942904021508429 4170073933478589008065661)
    ·
      refine ⟨1563777725054470878024623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4170073933478589008065661 1563777725054470878024623)
      ·
        refine ⟨2345666587581706317036935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1563777725054470878024623 2345666587581706317036935)
        ·
          refine ⟨3518499881372559475555403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2345666587581706317036935 3518499881372559475555403)
          ·
            refine ⟨5277749822058839213333105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3518499881372559475555403 5277749822058839213333105)
            ·
              refine ⟨3958312366544129409999829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5277749822058839213333105 3958312366544129409999829)
              ·
                refine ⟨92772946090878033046871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3958312366544129409999829 92772946090878033046871)
                ·
                  rfl

theorem cell21_1219554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_1219554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219554 prefixEnd_1219554 := by exact prefixLift 1219554
  have htrace : WordTrace (prefixWord ++ tailWord_1219554) baseStart_1219554 baseEnd_1219554 := by
    simpa [prefixWord, tailWord_1219554, baseEnd_1219554] using wordTrace_append hprefix tailTrace_1219554
  have hstable : (prefixWord ++ tailWord_1219554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219554).length < 2 ^ (prefixWord ++ tailWord_1219554).sum := by decide
  have hdescent : baseEnd_1219554 < baseStart_1219554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219568 : List Nat := [2, 1, 1, 1, 3, 2, 1, 7, 3]
def baseStart_1219568 : Nat := 118140960795 + 1219568 * 2 ^ 59
def prefixEnd_1219568 : Nat := 4983230072969 + 3 ^ 40 * 1219568 * 2
def baseEnd_1219568 : Nat := 278322033263373185907251

theorem tailTrace_1219568 : CollatzResearch.WordTrace tailWord_1219568 prefixEnd_1219568 278322033263373185907251 := by
  unfold tailWord_1219568
  simp only [CollatzResearch.WordTrace]
  refine ⟨22240649622860448238521679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29654199497147264318028905 22240649622860448238521679)
  ·
    refine ⟨33360974434290672357782519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22240649622860448238521679 33360974434290672357782519)
    ·
      refine ⟨50041461651436008536673779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33360974434290672357782519 50041461651436008536673779)
      ·
        refine ⟨75062192477154012805010669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50041461651436008536673779 75062192477154012805010669)
        ·
          refine ⟨28148322178932754801879001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75062192477154012805010669 28148322178932754801879001)
          ·
            refine ⟨21111241634199566101409251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28148322178932754801879001 21111241634199566101409251)
            ·
              refine ⟨31666862451299349152113877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21111241634199566101409251 31666862451299349152113877)
              ·
                refine ⟨742192088702328495752669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31666862451299349152113877 742192088702328495752669)
                ·
                  refine ⟨278322033263373185907251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742192088702328495752669 278322033263373185907251)
                  ·
                    rfl

theorem cell21_1219568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 7, 3].length) (baseStart_1219568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219568 prefixEnd_1219568 := by exact prefixLift 1219568
  have htrace : WordTrace (prefixWord ++ tailWord_1219568) baseStart_1219568 baseEnd_1219568 := by
    simpa [prefixWord, tailWord_1219568, baseEnd_1219568] using wordTrace_append hprefix tailTrace_1219568
  have hstable : (prefixWord ++ tailWord_1219568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219568).length < 2 ^ (prefixWord ++ tailWord_1219568).sum := by decide
  have hdescent : baseEnd_1219568 < baseStart_1219568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219585 : List Nat := [1, 2, 4, 1, 2, 3, 1, 4, 3]
def baseStart_1219585 : Nat := 118140960795 + 1219585 * 2 ^ 59
def prefixEnd_1219585 : Nat := 4983230072969 + 3 ^ 40 * 1219585 * 2
def baseEnd_1219585 : Nat := 278325912894984934123883

theorem tailTrace_1219585 : CollatzResearch.WordTrace tailWord_1219585 prefixEnd_1219585 278325912894984934123883 := by
  unfold tailWord_1219585
  simp only [CollatzResearch.WordTrace]
  refine ⟨44481919286659308380412209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29654612857772872253608139 44481919286659308380412209)
  ·
    refine ⟨33361439464994481285309157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44481919286659308380412209 33361439464994481285309157)
    ·
      refine ⟨6255269899686465240995467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33361439464994481285309157 6255269899686465240995467)
      ·
        refine ⟨9382904849529697861493201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6255269899686465240995467 9382904849529697861493201)
        ·
          refine ⟨7037178637147273396119901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9382904849529697861493201 7037178637147273396119901)
          ·
            refine ⟨2638941988930227523544963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7037178637147273396119901 2638941988930227523544963)
            ·
              refine ⟨3958412983395341285317445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638941988930227523544963 3958412983395341285317445)
              ·
                refine ⟨742202434386626490997021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3958412983395341285317445 742202434386626490997021)
                ·
                  refine ⟨278325912894984934123883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742202434386626490997021 278325912894984934123883)
                  ·
                    rfl

theorem cell21_1219585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 3].length) (baseStart_1219585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219585 prefixEnd_1219585 := by exact prefixLift 1219585
  have htrace : WordTrace (prefixWord ++ tailWord_1219585) baseStart_1219585 baseEnd_1219585 := by
    simpa [prefixWord, tailWord_1219585, baseEnd_1219585] using wordTrace_append hprefix tailTrace_1219585
  have hstable : (prefixWord ++ tailWord_1219585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219585).length < 2 ^ (prefixWord ++ tailWord_1219585).sum := by decide
  have hdescent : baseEnd_1219585 < baseStart_1219585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219644 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 5]
def baseStart_1219644 : Nat := 118140960795 + 1219644 * 2 ^ 59
def prefixEnd_1219644 : Nat := 4983230072969 + 3 ^ 40 * 1219644 * 2
def baseEnd_1219644 : Nat := 278339377498813942640429

theorem tailTrace_1219644 : CollatzResearch.WordTrace tailWord_1219644 prefixEnd_1219644 278339377498813942640429 := by
  unfold tailWord_1219644
  simp only [CollatzResearch.WordTrace]
  refine ⟨22242035596722780728404993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29656047462297040971206657 22242035596722780728404993)
  ·
    refine ⟨16681526697542085546303745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22242035596722780728404993 16681526697542085546303745)
    ·
      refine ⟨12511145023156564159727809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16681526697542085546303745 12511145023156564159727809)
      ·
        refine ⟨9383358767367423119795857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12511145023156564159727809 9383358767367423119795857)
        ·
          refine ⟨7037519075525567339846893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9383358767367423119795857 7037519075525567339846893)
          ·
            refine ⟨2639069653322087752442585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7037519075525567339846893 2639069653322087752442585)
            ·
              refine ⟨1979302239991565814331939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2639069653322087752442585 1979302239991565814331939)
              ·
                refine ⟨2968953359987348721497909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979302239991565814331939 2968953359987348721497909)
                ·
                  refine ⟨278339377498813942640429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2968953359987348721497909 278339377498813942640429)
                  ·
                    rfl

theorem cell21_1219644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_1219644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219644 prefixEnd_1219644 := by exact prefixLift 1219644
  have htrace : WordTrace (prefixWord ++ tailWord_1219644) baseStart_1219644 baseEnd_1219644 := by
    simpa [prefixWord, tailWord_1219644, baseEnd_1219644] using wordTrace_append hprefix tailTrace_1219644
  have hstable : (prefixWord ++ tailWord_1219644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219644).length < 2 ^ (prefixWord ++ tailWord_1219644).sum := by decide
  have hdescent : baseEnd_1219644 < baseStart_1219644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219658 : List Nat := [3, 1, 2, 1, 1, 2, 2, 5, 4]
def baseStart_1219658 : Nat := 118140960795 + 1219658 * 2 ^ 59
def prefixEnd_1219658 : Nat := 4983230072969 + 3 ^ 40 * 1219658 * 2
def baseEnd_1219658 : Nat := 278342572489553029407067

theorem tailTrace_1219658 : CollatzResearch.WordTrace tailWord_1219658 prefixEnd_1219658 278342572489553029407067 := by
  unfold tailWord_1219658
  simp only [CollatzResearch.WordTrace]
  refine ⟨11121145453848710461954907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29656387876929894565213085 11121145453848710461954907)
  ·
    refine ⟨16681718180773065692932361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11121145453848710461954907 16681718180773065692932361)
    ·
      refine ⟨12511288635579799269699271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16681718180773065692932361 12511288635579799269699271)
      ·
        refine ⟨18766932953369698904548907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12511288635579799269699271 18766932953369698904548907)
        ·
          refine ⟨28150399430054548356823361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18766932953369698904548907 28150399430054548356823361)
          ·
            refine ⟨21112799572540911267617521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28150399430054548356823361 21112799572540911267617521)
            ·
              refine ⟨15834599679405683450713141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21112799572540911267617521 15834599679405683450713141)
              ·
                refine ⟨1484493719944282823504357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15834599679405683450713141 1484493719944282823504357)
                ·
                  refine ⟨278342572489553029407067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484493719944282823504357 278342572489553029407067)
                  ·
                    rfl

theorem cell21_1219658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 4].length) (baseStart_1219658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219658 prefixEnd_1219658 := by exact prefixLift 1219658
  have htrace : WordTrace (prefixWord ++ tailWord_1219658) baseStart_1219658 baseEnd_1219658 := by
    simpa [prefixWord, tailWord_1219658, baseEnd_1219658] using wordTrace_append hprefix tailTrace_1219658
  have hstable : (prefixWord ++ tailWord_1219658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219658).length < 2 ^ (prefixWord ++ tailWord_1219658).sum := by decide
  have hdescent : baseEnd_1219658 < baseStart_1219658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219672 : List Nat := [2, 1, 2, 2, 1, 3, 3, 7]
def baseStart_1219672 : Nat := 118140960795 + 1219672 * 2 ^ 59
def prefixEnd_1219672 : Nat := 4983230072969 + 3 ^ 40 * 1219672 * 2
def baseEnd_1219672 : Nat := 92781922493430705391235

theorem tailTrace_1219672 : CollatzResearch.WordTrace tailWord_1219672 prefixEnd_1219672 92781922493430705391235 := by
  unfold tailWord_1219672
  simp only [CollatzResearch.WordTrace]
  refine ⟨22242546218672061119414635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29656728291562748159219513 22242546218672061119414635)
  ·
    refine ⟨33363819328008091679121953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22242546218672061119414635 33363819328008091679121953)
    ·
      refine ⟨25022864496006068759341465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33363819328008091679121953 25022864496006068759341465)
      ·
        refine ⟨18767148372004551569506099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25022864496006068759341465 18767148372004551569506099)
        ·
          refine ⟨28150722558006827354259149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18767148372004551569506099 28150722558006827354259149)
          ·
            refine ⟨10556520959252560257847181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28150722558006827354259149 10556520959252560257847181)
            ·
              refine ⟨3958695359719710096692693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10556520959252560257847181 3958695359719710096692693)
              ·
                refine ⟨92781922493430705391235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3958695359719710096692693 92781922493430705391235)
                ·
                  rfl

theorem cell21_1219672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_1219672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219672 prefixEnd_1219672 := by exact prefixLift 1219672
  have htrace : WordTrace (prefixWord ++ tailWord_1219672) baseStart_1219672 baseEnd_1219672 := by
    simpa [prefixWord, tailWord_1219672, baseEnd_1219672] using wordTrace_append hprefix tailTrace_1219672
  have hstable : (prefixWord ++ tailWord_1219672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219672).length < 2 ^ (prefixWord ++ tailWord_1219672).sum := by decide
  have hdescent : baseEnd_1219672 < baseStart_1219672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219748 : List Nat := [2, 3, 1, 2, 3, 10]
def baseStart_1219748 : Nat := 118140960795 + 1219748 * 2 ^ 59
def prefixEnd_1219748 : Nat := 4983230072969 + 3 ^ 40 * 1219748 * 2
def baseEnd_1219748 : Nat := 10309744878360476774329

theorem tailTrace_1219748 : CollatzResearch.WordTrace tailWord_1219748 prefixEnd_1219748 10309744878360476774329 := by
  unfold tailWord_1219748
  simp only [CollatzResearch.WordTrace]
  refine ⟨22243932192534393609297949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29658576256712524812397265 22243932192534393609297949)
  ·
    refine ⟨8341474572200397603486731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22243932192534393609297949 8341474572200397603486731)
    ·
      refine ⟨12512211858300596405230097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8341474572200397603486731 12512211858300596405230097)
      ·
        refine ⟨9384158893725447303922573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12512211858300596405230097 9384158893725447303922573)
        ·
          refine ⟨3519059585147042738970965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9384158893725447303922573 3519059585147042738970965)
          ·
            refine ⟨10309744878360476774329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3519059585147042738970965 10309744878360476774329)
            ·
              rfl

theorem cell21_1219748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 10].length) (baseStart_1219748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219748 prefixEnd_1219748 := by exact prefixLift 1219748
  have htrace : WordTrace (prefixWord ++ tailWord_1219748) baseStart_1219748 baseEnd_1219748 := by
    simpa [prefixWord, tailWord_1219748, baseEnd_1219748] using wordTrace_append hprefix tailTrace_1219748
  have hstable : (prefixWord ++ tailWord_1219748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219748).length < 2 ^ (prefixWord ++ tailWord_1219748).sum := by decide
  have hdescent : baseEnd_1219748 < baseStart_1219748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219751 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 4]
def baseStart_1219751 : Nat := 118140960795 + 1219751 * 2 ^ 59
def prefixEnd_1219751 : Nat := 4983230072969 + 3 ^ 40 * 1219751 * 2
def baseEnd_1219751 : Nat := 278363796356605534356877

theorem tailTrace_1219751 : CollatzResearch.WordTrace tailWord_1219751 prefixEnd_1219751 278363796356605534356877 := by
  unfold tailWord_1219751
  simp only [CollatzResearch.WordTrace]
  refine ⟨44487973804057918730955107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29658649202705279153970071 44487973804057918730955107)
  ·
    refine ⟨66731960706086878096432661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44487973804057918730955107 66731960706086878096432661)
    ·
      refine ⟨3128060658097822410770281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66731960706086878096432661 3128060658097822410770281)
      ·
        refine ⟨2346045493573366808077711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3128060658097822410770281 2346045493573366808077711)
        ·
          refine ⟨3519068240360050212116567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346045493573366808077711 3519068240360050212116567)
          ·
            refine ⟨5278602360540075318174851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519068240360050212116567 5278602360540075318174851)
            ·
              refine ⟨7917903540810112977262277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5278602360540075318174851 7917903540810112977262277)
              ·
                refine ⟨1484606913901896183236677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7917903540810112977262277 1484606913901896183236677)
                ·
                  refine ⟨278363796356605534356877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484606913901896183236677 278363796356605534356877)
                  ·
                    rfl

theorem cell21_1219751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 4].length) (baseStart_1219751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219751 prefixEnd_1219751 := by exact prefixLift 1219751
  have htrace : WordTrace (prefixWord ++ tailWord_1219751) baseStart_1219751 baseEnd_1219751 := by
    simpa [prefixWord, tailWord_1219751, baseEnd_1219751] using wordTrace_append hprefix tailTrace_1219751
  have hstable : (prefixWord ++ tailWord_1219751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219751).length < 2 ^ (prefixWord ++ tailWord_1219751).sum := by decide
  have hdescent : baseEnd_1219751 < baseStart_1219751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219754 : List Nat := [3, 1, 5, 1, 1, 2, 1, 4, 3]
def baseStart_1219754 : Nat := 118140960795 + 1219754 * 2 ^ 59
def prefixEnd_1219754 : Nat := 4983230072969 + 3 ^ 40 * 1219754 * 2
def baseEnd_1219754 : Nat := 278364480997478195806871

theorem tailTrace_1219754 : CollatzResearch.WordTrace tailWord_1219754 prefixEnd_1219754 278364480997478195806871 := by
  unfold tailWord_1219754
  simp only [CollatzResearch.WordTrace]
  refine ⟨11122020805761762560828579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29658722148698033495542877 11122020805761762560828579)
  ·
    refine ⟨16683031208642643841242869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11122020805761762560828579 16683031208642643841242869)
    ·
      refine ⟨1564034175810247860116519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16683031208642643841242869 1564034175810247860116519)
      ·
        refine ⟨2346051263715371790174779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1564034175810247860116519 2346051263715371790174779)
        ·
          refine ⟨3519076895573057685262169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346051263715371790174779 3519076895573057685262169)
          ·
            refine ⟨2639307671679793263946627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3519076895573057685262169 2639307671679793263946627)
            ·
              refine ⟨3958961507519689895919941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2639307671679793263946627 3958961507519689895919941)
              ·
                refine ⟨742305282659941855484989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3958961507519689895919941 742305282659941855484989)
                ·
                  refine ⟨278364480997478195806871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742305282659941855484989 278364480997478195806871)
                  ·
                    rfl

theorem cell21_1219754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_1219754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219754 prefixEnd_1219754 := by exact prefixLift 1219754
  have htrace : WordTrace (prefixWord ++ tailWord_1219754) baseStart_1219754 baseEnd_1219754 := by
    simpa [prefixWord, tailWord_1219754, baseEnd_1219754] using wordTrace_append hprefix tailTrace_1219754
  have hstable : (prefixWord ++ tailWord_1219754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219754).length < 2 ^ (prefixWord ++ tailWord_1219754).sum := by decide
  have hdescent : baseEnd_1219754 < baseStart_1219754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219793 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 6]
def baseStart_1219793 : Nat := 118140960795 + 1219793 * 2 ^ 59
def prefixEnd_1219793 : Nat := 4983230072969 + 3 ^ 40 * 1219793 * 2
def baseEnd_1219793 : Nat := 278373381328822794656791

theorem tailTrace_1219793 : CollatzResearch.WordTrace tailWord_1219793 prefixEnd_1219793 278373381328822794656791 := by
  unfold tailWord_1219793
  simp only [CollatzResearch.WordTrace]
  refine ⟨44489505669905759903984033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29659670446603839935989355 44489505669905759903984033)
  ·
    refine ⟨33367129252429319927988025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44489505669905759903984033 33367129252429319927988025)
    ·
      refine ⟨25025346939321989945991019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33367129252429319927988025 25025346939321989945991019)
      ·
        refine ⟨37538020408982984918986529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25025346939321989945991019 37538020408982984918986529)
        ·
          refine ⟨28153515306737238689239897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37538020408982984918986529 28153515306737238689239897)
          ·
            refine ⟨21115136480052929016929923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28153515306737238689239897 21115136480052929016929923)
            ·
              refine ⟨31672704720079393525394885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21115136480052929016929923 31672704720079393525394885)
              ·
                refine ⟨5938632135014886286011541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31672704720079393525394885 5938632135014886286011541)
                ·
                  refine ⟨278373381328822794656791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5938632135014886286011541 278373381328822794656791)
                  ·
                    rfl

theorem cell21_1219793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_1219793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219793 prefixEnd_1219793 := by exact prefixLift 1219793
  have htrace : WordTrace (prefixWord ++ tailWord_1219793) baseStart_1219793 baseEnd_1219793 := by
    simpa [prefixWord, tailWord_1219793, baseEnd_1219793] using wordTrace_append hprefix tailTrace_1219793
  have hstable : (prefixWord ++ tailWord_1219793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219793).length < 2 ^ (prefixWord ++ tailWord_1219793).sum := by decide
  have hdescent : baseEnd_1219793 < baseStart_1219793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219827 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 4]
def baseStart_1219827 : Nat := 118140960795 + 1219827 * 2 ^ 59
def prefixEnd_1219827 : Nat := 4983230072969 + 3 ^ 40 * 1219827 * 2
def baseEnd_1219827 : Nat := 278381140592046291090055

theorem tailTrace_1219827 : CollatzResearch.WordTrace tailWord_1219827 prefixEnd_1219827 278381140592046291090055 := by
  unfold tailWord_1219827
  simp only [CollatzResearch.WordTrace]
  refine ⟨44490745751782583710721735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29660497167855055807147823 44490745751782583710721735)
  ·
    refine ⟨66736118627673875566082603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44490745751782583710721735 66736118627673875566082603)
    ·
      refine ⟨100104177941510813349123905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66736118627673875566082603 100104177941510813349123905)
      ·
        refine ⟨75078133456133110011842929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100104177941510813349123905 75078133456133110011842929)
        ·
          refine ⟨56308600092099832508882197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75078133456133110011842929 56308600092099832508882197)
          ·
            refine ⟨2639465629317179648853853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 56308600092099832508882197 2639465629317179648853853)
            ·
              refine ⟨989799610993942368320195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2639465629317179648853853 989799610993942368320195)
              ·
                refine ⟨1484699416490913552480293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 989799610993942368320195 1484699416490913552480293)
                ·
                  refine ⟨278381140592046291090055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1484699416490913552480293 278381140592046291090055)
                  ·
                    rfl

theorem cell21_1219827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 4].length) (baseStart_1219827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219827 prefixEnd_1219827 := by exact prefixLift 1219827
  have htrace : WordTrace (prefixWord ++ tailWord_1219827) baseStart_1219827 baseEnd_1219827 := by
    simpa [prefixWord, tailWord_1219827, baseEnd_1219827] using wordTrace_append hprefix tailTrace_1219827
  have hstable : (prefixWord ++ tailWord_1219827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219827).length < 2 ^ (prefixWord ++ tailWord_1219827).sum := by decide
  have hdescent : baseEnd_1219827 < baseStart_1219827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219841 : List Nat := [1, 2, 4, 1, 1, 3, 4, 5]
def baseStart_1219841 : Nat := 118140960795 + 1219841 * 2 ^ 59
def prefixEnd_1219841 : Nat := 4983230072969 + 3 ^ 40 * 1219841 * 2
def baseEnd_1219841 : Nat := 92794778527595125952231

theorem tailTrace_1219841 : CollatzResearch.WordTrace tailWord_1219841 prefixEnd_1219841 92794778527595125952231 := by
  unfold tailWord_1219841
  simp only [CollatzResearch.WordTrace]
  refine ⟨44491256373731864101731377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29660837582487909401154251 44491256373731864101731377)
  ·
    refine ⟨33368442280298898076298533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44491256373731864101731377 33368442280298898076298533)
    ·
      refine ⟨6256582927556043389305975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33368442280298898076298533 6256582927556043389305975)
      ·
        refine ⟨9384874391334065083958963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6256582927556043389305975 9384874391334065083958963)
        ·
          refine ⟨14077311587001097625938445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9384874391334065083958963 14077311587001097625938445)
          ·
            refine ⟨5278991845125411609726917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14077311587001097625938445 5278991845125411609726917)
            ·
              refine ⟨989810970961014676823797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5278991845125411609726917 989810970961014676823797)
              ·
                refine ⟨92794778527595125952231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 989810970961014676823797 92794778527595125952231)
                ·
                  rfl

theorem cell21_1219841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 5].length) (baseStart_1219841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219841 prefixEnd_1219841 := by exact prefixLift 1219841
  have htrace : WordTrace (prefixWord ++ tailWord_1219841) baseStart_1219841 baseEnd_1219841 := by
    simpa [prefixWord, tailWord_1219841, baseEnd_1219841] using wordTrace_append hprefix tailTrace_1219841
  have hstable : (prefixWord ++ tailWord_1219841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219841).length < 2 ^ (prefixWord ++ tailWord_1219841).sum := by decide
  have hdescent : baseEnd_1219841 < baseStart_1219841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219900 : List Nat := [2, 2, 2, 2, 1, 3, 2, 7]
def baseStart_1219900 : Nat := 118140960795 + 1219900 * 2 ^ 59
def prefixEnd_1219900 : Nat := 4983230072969 + 3 ^ 40 * 1219900 * 2
def baseEnd_1219900 : Nat := 92799266728871462124413

theorem tailTrace_1219900 : CollatzResearch.WordTrace tailWord_1219900 prefixEnd_1219900 92799266728871462124413 := by
  unfold tailWord_1219900
  simp only [CollatzResearch.WordTrace]
  refine ⟨22246704140259058589064577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29662272187012078118752769 22246704140259058589064577)
  ·
    refine ⟨16685028105194293941798433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22246704140259058589064577 16685028105194293941798433)
    ·
      refine ⟨12513771078895720456348825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16685028105194293941798433 12513771078895720456348825)
      ·
        refine ⟨9385328309171790342261619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12513771078895720456348825 9385328309171790342261619)
        ·
          refine ⟨14077992463757685513392429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9385328309171790342261619 14077992463757685513392429)
          ·
            refine ⟨5279247173909132067522161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14077992463757685513392429 5279247173909132067522161)
            ·
              refine ⟨3959435380431849050641621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5279247173909132067522161 3959435380431849050641621)
              ·
                refine ⟨92799266728871462124413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3959435380431849050641621 92799266728871462124413)
                ·
                  rfl

theorem cell21_1219900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_1219900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219900 prefixEnd_1219900 := by exact prefixLift 1219900
  have htrace : WordTrace (prefixWord ++ tailWord_1219900) baseStart_1219900 baseEnd_1219900 := by
    simpa [prefixWord, tailWord_1219900, baseEnd_1219900] using wordTrace_append hprefix tailTrace_1219900
  have hstable : (prefixWord ++ tailWord_1219900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219900).length < 2 ^ (prefixWord ++ tailWord_1219900).sum := by decide
  have hdescent : baseEnd_1219900 < baseStart_1219900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219917 : List Nat := [1, 6, 1, 3, 10]
def baseStart_1219917 : Nat := 118140960795 + 1219917 * 2 ^ 59
def prefixEnd_1219917 : Nat := 4983230072969 + 3 ^ 40 * 1219917 * 2
def baseEnd_1219917 : Nat := 3437057775533655982591

theorem tailTrace_1219917 : CollatzResearch.WordTrace tailWord_1219917 prefixEnd_1219917 3437057775533655982591 := by
  unfold tailWord_1219917
  simp only [CollatzResearch.WordTrace]
  refine ⟨44494028321456529081498005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29662685547637686054332003 44494028321456529081498005)
  ·
    refine ⟨2085657577568274800695219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44494028321456529081498005 2085657577568274800695219)
    ·
      refine ⟨3128486366352412201042829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2085657577568274800695219 3128486366352412201042829)
      ·
        refine ⟨1173182387382154575391061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3128486366352412201042829 1173182387382154575391061)
        ·
          refine ⟨3437057775533655982591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1173182387382154575391061 3437057775533655982591)
          ·
            rfl

theorem cell21_1219917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 10].length) (baseStart_1219917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219917 prefixEnd_1219917 := by exact prefixLift 1219917
  have htrace : WordTrace (prefixWord ++ tailWord_1219917) baseStart_1219917 baseEnd_1219917 := by
    simpa [prefixWord, tailWord_1219917, baseEnd_1219917] using wordTrace_append hprefix tailTrace_1219917
  have hstable : (prefixWord ++ tailWord_1219917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219917).length < 2 ^ (prefixWord ++ tailWord_1219917).sum := by decide
  have hdescent : baseEnd_1219917 < baseStart_1219917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1219976 : List Nat := [2, 1, 3, 3, 1, 3, 8]
def baseStart_1219976 : Nat := 118140960795 + 1219976 * 2 ^ 59
def prefixEnd_1219976 : Nat := 4983230072969 + 3 ^ 40 * 1219976 * 2
def baseEnd_1219976 : Nat := 30935016046895015900713

theorem tailTrace_1219976 : CollatzResearch.WordTrace tailWord_1219976 prefixEnd_1219976 30935016046895015900713 := by
  unfold tailWord_1219976
  simp only [CollatzResearch.WordTrace]
  refine ⟨22248090114121391078947891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29664120152161854771930521 22248090114121391078947891)
  ·
    refine ⟨33372135171182086618421837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22248090114121391078947891 33372135171182086618421837)
    ·
      refine ⟨12514550689193282481908189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33372135171182086618421837 12514550689193282481908189)
      ·
        refine ⟨4692956508447480930715571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12514550689193282481908189 4692956508447480930715571)
        ·
          refine ⟨7039434762671221396073357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4692956508447480930715571 7039434762671221396073357)
          ·
            refine ⟨2639788036001708023527509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7039434762671221396073357 2639788036001708023527509)
            ·
              refine ⟨30935016046895015900713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2639788036001708023527509 30935016046895015900713)
              ·
                rfl

theorem cell21_1219976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 8].length) (baseStart_1219976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1219976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1219976 prefixEnd_1219976 := by exact prefixLift 1219976
  have htrace : WordTrace (prefixWord ++ tailWord_1219976) baseStart_1219976 baseEnd_1219976 := by
    simpa [prefixWord, tailWord_1219976, baseEnd_1219976] using wordTrace_append hprefix tailTrace_1219976
  have hstable : (prefixWord ++ tailWord_1219976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1219976).length < 2 ^ (prefixWord ++ tailWord_1219976).sum := by decide
  have hdescent : baseEnd_1219976 < baseStart_1219976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1219976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220007 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 5]
def baseStart_1220007 : Nat := 118140960795 + 1220007 * 2 ^ 59
def prefixEnd_1220007 : Nat := 4983230072969 + 3 ^ 40 * 1220007 * 2
def baseEnd_1220007 : Nat := 278422219044405978089687

theorem tailTrace_1220007 : CollatzResearch.WordTrace tailWord_1220007 prefixEnd_1220007 278422219044405978089687 := by
  unfold tailWord_1220007
  simp only [CollatzResearch.WordTrace]
  refine ⟨44497310891130474452274275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29664873927420316301516183 44497310891130474452274275)
  ·
    refine ⟨66745966336695711678411413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44497310891130474452274275 66745966336695711678411413)
    ·
      refine ⟨3128717172032611484925535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66745966336695711678411413 3128717172032611484925535)
      ·
        refine ⟨4693075758048917227388303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3128717172032611484925535 4693075758048917227388303)
        ·
          refine ⟨7039613637073375841082455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4693075758048917227388303 7039613637073375841082455)
          ·
            refine ⟨10559420455610063761623683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7039613637073375841082455 10559420455610063761623683)
            ·
              refine ⟨15839130683415095642435525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10559420455610063761623683 15839130683415095642435525)
              ·
                refine ⟨2969837003140330432956661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15839130683415095642435525 2969837003140330432956661)
                ·
                  refine ⟨278422219044405978089687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2969837003140330432956661 278422219044405978089687)
                  ·
                    rfl

theorem cell21_1220007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_1220007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220007 prefixEnd_1220007 := by exact prefixLift 1220007
  have htrace : WordTrace (prefixWord ++ tailWord_1220007) baseStart_1220007 baseEnd_1220007 := by
    simpa [prefixWord, tailWord_1220007, baseEnd_1220007] using wordTrace_append hprefix tailTrace_1220007
  have hstable : (prefixWord ++ tailWord_1220007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220007).length < 2 ^ (prefixWord ++ tailWord_1220007).sum := by decide
  have hdescent : baseEnd_1220007 < baseStart_1220007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220024 : List Nat := [2, 1, 2, 1, 2, 2, 5, 3, 3]
def baseStart_1220024 : Nat := 118140960795 + 1220024 * 2 ^ 59
def prefixEnd_1220024 : Nat := 4983230072969 + 3 ^ 40 * 1220024 * 2
def baseEnd_1220024 : Nat := 278426098676017726306319

theorem tailTrace_1220024 : CollatzResearch.WordTrace tailWord_1220024 prefixEnd_1220024 278426098676017726306319 := by
  unfold tailWord_1220024
  simp only [CollatzResearch.WordTrace]
  refine ⟨22248965466034443177821563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29665287288045924237095417 22248965466034443177821563)
  ·
    refine ⟨33373448199051664766732345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22248965466034443177821563 33373448199051664766732345)
    ·
      refine ⟨25030086149288748575049259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33373448199051664766732345 25030086149288748575049259)
      ·
        refine ⟨37545129223933122862573889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25030086149288748575049259 37545129223933122862573889)
        ·
          refine ⟨28158846917949842146930417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37545129223933122862573889 28158846917949842146930417)
          ·
            refine ⟨21119135188462381610197813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28158846917949842146930417 21119135188462381610197813)
            ·
              refine ⟨1979918923918348275956045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21119135188462381610197813 1979918923918348275956045)
              ·
                refine ⟨742469596469380603483517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1979918923918348275956045 742469596469380603483517)
                ·
                  refine ⟨278426098676017726306319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742469596469380603483517 278426098676017726306319)
                  ·
                    rfl

theorem cell21_1220024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 3, 3].length) (baseStart_1220024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220024 prefixEnd_1220024 := by exact prefixLift 1220024
  have htrace : WordTrace (prefixWord ++ tailWord_1220024) baseStart_1220024 baseEnd_1220024 := by
    simpa [prefixWord, tailWord_1220024, baseEnd_1220024] using wordTrace_append hprefix tailTrace_1220024
  have hstable : (prefixWord ++ tailWord_1220024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220024).length < 2 ^ (prefixWord ++ tailWord_1220024).sum := by decide
  have hdescent : baseEnd_1220024 < baseStart_1220024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220035 : List Nat := [1, 1, 1, 3, 1, 1, 13]
def baseStart_1220035 : Nat := 118140960795 + 1220035 * 2 ^ 59
def prefixEnd_1220035 : Nat := 4983230072969 + 3 ^ 40 * 1220035 * 2
def baseEnd_1220035 : Nat := 30936512113987127958107

theorem tailTrace_1220035 : CollatzResearch.WordTrace tailWord_1220035 prefixEnd_1220035 30936512113987127958107 := by
  unfold tailWord_1220035
  simp only [CollatzResearch.WordTrace]
  refine ⟨44498332135029035234293559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29665554756686023489529039 44498332135029035234293559)
  ·
    refine ⟨66747498202543552851440339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44498332135029035234293559 66747498202543552851440339)
    ·
      refine ⟨100121247303815329277160509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66747498202543552851440339 100121247303815329277160509)
      ·
        refine ⟨37545467738930748478935191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100121247303815329277160509 37545467738930748478935191)
        ·
          refine ⟨56318201608396122718402787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37545467738930748478935191 56318201608396122718402787)
          ·
            refine ⟨84477302412594184077604181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56318201608396122718402787 84477302412594184077604181)
            ·
              refine ⟨30936512113987127958107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 84477302412594184077604181 30936512113987127958107)
              ·
                rfl

theorem cell21_1220035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 13].length) (baseStart_1220035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220035 prefixEnd_1220035 := by exact prefixLift 1220035
  have htrace : WordTrace (prefixWord ++ tailWord_1220035) baseStart_1220035 baseEnd_1220035 := by
    simpa [prefixWord, tailWord_1220035, baseEnd_1220035] using wordTrace_append hprefix tailTrace_1220035
  have hstable : (prefixWord ++ tailWord_1220035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220035).length < 2 ^ (prefixWord ++ tailWord_1220035).sum := by decide
  have hdescent : baseEnd_1220035 < baseStart_1220035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220159 : List Nat := [1, 1, 2, 2, 3, 4, 2, 1, 5]
def baseStart_1220159 : Nat := 118140960795 + 1220159 * 2 ^ 59
def prefixEnd_1220159 : Nat := 4983230072969 + 3 ^ 40 * 1220159 * 2
def baseEnd_1220159 : Nat := 278456907515287491556043

theorem tailTrace_1220159 : CollatzResearch.WordTrace tailWord_1220159 prefixEnd_1220159 278456907515287491556043 := by
  unfold tailWord_1220159
  simp only [CollatzResearch.WordTrace]
  refine ⟨44502854786579804411807531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29668569857719869607871687 44502854786579804411807531)
  ·
    refine ⟨66754282179869706617711297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44502854786579804411807531 66754282179869706617711297)
    ·
      refine ⟨50065711634902279963283473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66754282179869706617711297 50065711634902279963283473)
      ·
        refine ⟨37549283726176709972462605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50065711634902279963283473 37549283726176709972462605)
        ·
          refine ⟨14080981397316266239673477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37549283726176709972462605 14080981397316266239673477)
          ·
            refine ⟨2640184011996799919938777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14080981397316266239673477 2640184011996799919938777)
            ·
              refine ⟨1980138008997599939954083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2640184011996799919938777 1980138008997599939954083)
              ·
                refine ⟨2970207013496399909931125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1980138008997599939954083 2970207013496399909931125)
                ·
                  refine ⟨278456907515287491556043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2970207013496399909931125 278456907515287491556043)
                  ·
                    rfl

theorem cell21_1220159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 5].length) (baseStart_1220159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220159 prefixEnd_1220159 := by exact prefixLift 1220159
  have htrace : WordTrace (prefixWord ++ tailWord_1220159) baseStart_1220159 baseEnd_1220159 := by
    simpa [prefixWord, tailWord_1220159, baseEnd_1220159] using wordTrace_append hprefix tailTrace_1220159
  have hstable : (prefixWord ++ tailWord_1220159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220159).length < 2 ^ (prefixWord ++ tailWord_1220159).sum := by decide
  have hdescent : baseEnd_1220159 < baseStart_1220159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220218 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 5]
def baseStart_1220218 : Nat := 118140960795 + 1220218 * 2 ^ 59
def prefixEnd_1220218 : Nat := 4983230072969 + 3 ^ 40 * 1220218 * 2
def baseEnd_1220218 : Nat := 278470372119116500072589

theorem tailTrace_1220218 : CollatzResearch.WordTrace tailWord_1220218 prefixEnd_1220218 278470372119116500072589 := by
  unfold tailWord_1220218
  simp only [CollatzResearch.WordTrace]
  refine ⟨11126251673341514372051327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29670004462244038325470205 11126251673341514372051327)
  ·
    refine ⟨16689377510012271558076991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11126251673341514372051327 16689377510012271558076991)
    ·
      refine ⟨25034066265018407337115487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16689377510012271558076991 25034066265018407337115487)
      ·
        refine ⟨37551099397527611005673231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25034066265018407337115487 37551099397527611005673231)
        ·
          refine ⟨56326649096291416508509847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37551099397527611005673231 56326649096291416508509847)
          ·
            refine ⟨84489973644437124762764771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56326649096291416508509847 84489973644437124762764771)
            ·
              refine ⟨126734960466655687144147157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84489973644437124762764771 126734960466655687144147157)
              ·
                refine ⟨2970350635937242667440949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 126734960466655687144147157 2970350635937242667440949)
                ·
                  refine ⟨278470372119116500072589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2970350635937242667440949 278470372119116500072589)
                  ·
                    rfl

theorem cell21_1220218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_1220218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220218 prefixEnd_1220218 := by exact prefixLift 1220218
  have htrace : WordTrace (prefixWord ++ tailWord_1220218) baseStart_1220218 baseEnd_1220218 := by
    simpa [prefixWord, tailWord_1220218, baseEnd_1220218] using wordTrace_append hprefix tailTrace_1220218
  have hstable : (prefixWord ++ tailWord_1220218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220218).length < 2 ^ (prefixWord ++ tailWord_1220218).sum := by decide
  have hdescent : baseEnd_1220218 < baseStart_1220218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220263 : List Nat := [1, 1, 6, 13]
def baseStart_1220263 : Nat := 118140960795 + 1220263 * 2 ^ 59
def prefixEnd_1220263 : Nat := 4983230072969 + 3 ^ 40 * 1220263 * 2
def baseEnd_1220263 : Nat := 1146010871325952353179

theorem tailTrace_1220263 : CollatzResearch.WordTrace tailWord_1220263 prefixEnd_1220263 1146010871325952353179 := by
  unfold tailWord_1220263
  simp only [CollatzResearch.WordTrace]
  refine ⟨44506647978203030173593443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29671098652135353449062295 44506647978203030173593443)
  ·
    refine ⟨66759971967304545260390165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44506647978203030173593443 66759971967304545260390165)
    ·
      refine ⟨3129373685967400559080789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66759971967304545260390165 3129373685967400559080789)
      ·
        refine ⟨1146010871325952353179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3129373685967400559080789 1146010871325952353179)
        ·
          rfl

theorem cell21_1220263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 13].length) (baseStart_1220263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220263 prefixEnd_1220263 := by exact prefixLift 1220263
  have htrace : WordTrace (prefixWord ++ tailWord_1220263) baseStart_1220263 baseEnd_1220263 := by
    simpa [prefixWord, tailWord_1220263, baseEnd_1220263] using wordTrace_append hprefix tailTrace_1220263
  have hstable : (prefixWord ++ tailWord_1220263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220263).length < 2 ^ (prefixWord ++ tailWord_1220263).sum := by decide
  have hdescent : baseEnd_1220263 < baseStart_1220263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220317 : List Nat := [1, 4, 3, 3, 2, 1, 1, 2, 4]
def baseStart_1220317 : Nat := 118140960795 + 1220317 * 2 ^ 59
def prefixEnd_1220317 : Nat := 4983230072969 + 3 ^ 40 * 1220317 * 2
def baseEnd_1220317 : Nat := 278492965267914327922387

theorem tailTrace_1220317 : CollatzResearch.WordTrace tailWord_1220317 prefixEnd_1220317 278492965267914327922387 := by
  unfold tailWord_1220317
  simp only [CollatzResearch.WordTrace]
  refine ⟨44508617520007397396059205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29672411680004931597372803 44508617520007397396059205)
  ·
    refine ⟨8345365785001387011761101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44508617520007397396059205 8345365785001387011761101)
    ·
      refine ⟨3129512169375520129410413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8345365785001387011761101 3129512169375520129410413)
      ·
        refine ⟨1173567063515820048528905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3129512169375520129410413 1173567063515820048528905)
        ·
          refine ⟨880175297636865036396679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1173567063515820048528905 880175297636865036396679)
          ·
            refine ⟨1320262946455297554595019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880175297636865036396679 1320262946455297554595019)
            ·
              refine ⟨1980394419682946331892529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1320262946455297554595019 1980394419682946331892529)
              ·
                refine ⟨1485295814762209748919397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1980394419682946331892529 1485295814762209748919397)
                ·
                  refine ⟨278492965267914327922387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1485295814762209748919397 278492965267914327922387)
                  ·
                    rfl

theorem cell21_1220317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_1220317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220317 prefixEnd_1220317 := by exact prefixLift 1220317
  have htrace : WordTrace (prefixWord ++ tailWord_1220317) baseStart_1220317 baseEnd_1220317 := by
    simpa [prefixWord, tailWord_1220317, baseEnd_1220317] using wordTrace_append hprefix tailTrace_1220317
  have hstable : (prefixWord ++ tailWord_1220317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220317).length < 2 ^ (prefixWord ++ tailWord_1220317).sum := by decide
  have hdescent : baseEnd_1220317 < baseStart_1220317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220325 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 6]
def baseStart_1220325 : Nat := 118140960795 + 1220325 * 2 ^ 59
def prefixEnd_1220325 : Nat := 4983230072969 + 3 ^ 40 * 1220325 * 2
def baseEnd_1220325 : Nat := 278494790976908091789037

theorem tailTrace_1220325 : CollatzResearch.WordTrace tailWord_1220325 prefixEnd_1220325 278494790976908091789037 := by
  unfold tailWord_1220325
  simp only [CollatzResearch.WordTrace]
  refine ⟨44508909303978414762350429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29672606202652276508233619 44508909303978414762350429)
  ·
    refine ⟨16690840988991905535881411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44508909303978414762350429 16690840988991905535881411)
    ·
      refine ⟨25036261483487858303822117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16690840988991905535881411 25036261483487858303822117)
      ·
        refine ⟨4694299028153973431966647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25036261483487858303822117 4694299028153973431966647)
        ·
          refine ⟨7041448542230960147949971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4694299028153973431966647 7041448542230960147949971)
          ·
            refine ⟨10562172813346440221924957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7041448542230960147949971 10562172813346440221924957)
            ·
              refine ⟨3960814805004915083221859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10562172813346440221924957 3960814805004915083221859)
              ·
                refine ⟨5941222207507372624832789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3960814805004915083221859 5941222207507372624832789)
                ·
                  refine ⟨278494790976908091789037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5941222207507372624832789 278494790976908091789037)
                  ·
                    rfl

theorem cell21_1220325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_1220325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220325 prefixEnd_1220325 := by exact prefixLift 1220325
  have htrace : WordTrace (prefixWord ++ tailWord_1220325) baseStart_1220325 baseEnd_1220325 := by
    simpa [prefixWord, tailWord_1220325, baseEnd_1220325] using wordTrace_append hprefix tailTrace_1220325
  have hstable : (prefixWord ++ tailWord_1220325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220325).length < 2 ^ (prefixWord ++ tailWord_1220325).sum := by decide
  have hdescent : baseEnd_1220325 < baseStart_1220325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220328 : List Nat := [2, 1, 4, 1, 3, 1, 2, 4, 3]
def baseStart_1220328 : Nat := 118140960795 + 1220328 * 2 ^ 59
def prefixEnd_1220328 : Nat := 4983230072969 + 3 ^ 40 * 1220328 * 2
def baseEnd_1220328 : Nat := 278495475617780753239031

theorem tailTrace_1220328 : CollatzResearch.WordTrace tailWord_1220328 prefixEnd_1220328 278495475617780753239031 := by
  unfold tailWord_1220328
  simp only [CollatzResearch.WordTrace]
  refine ⟨22254509361483773137354819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29672679148645030849806425 22254509361483773137354819)
  ·
    refine ⟨33381764042225659706032229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22254509361483773137354819 33381764042225659706032229)
    ·
      refine ⟨6259080757917311194881043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33381764042225659706032229 6259080757917311194881043)
      ·
        refine ⟨9388621136875966792321565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6259080757917311194881043 9388621136875966792321565)
        ·
          refine ⟨3520732926328487547120587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9388621136875966792321565 3520732926328487547120587)
          ·
            refine ⟨5281099389492731320680881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3520732926328487547120587 5281099389492731320680881)
            ·
              refine ⟨3960824542119548490510661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5281099389492731320680881 3960824542119548490510661)
              ·
                refine ⟨742654601647415341970749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3960824542119548490510661 742654601647415341970749)
                ·
                  refine ⟨278495475617780753239031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742654601647415341970749 278495475617780753239031)
                  ·
                    rfl

theorem cell21_1220328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 4, 3].length) (baseStart_1220328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220328 prefixEnd_1220328 := by exact prefixLift 1220328
  have htrace : WordTrace (prefixWord ++ tailWord_1220328) baseStart_1220328 baseEnd_1220328 := by
    simpa [prefixWord, tailWord_1220328, baseEnd_1220328] using wordTrace_append hprefix tailTrace_1220328
  have hstable : (prefixWord ++ tailWord_1220328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220328).length < 2 ^ (prefixWord ++ tailWord_1220328).sum := by decide
  have hdescent : baseEnd_1220328 < baseStart_1220328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220356 : List Nat := [2, 3, 2, 2, 1, 3, 1, 7]
def baseStart_1220356 : Nat := 118140960795 + 1220356 * 2 ^ 59
def prefixEnd_1220356 : Nat := 4983230072969 + 3 ^ 40 * 1220356 * 2
def baseEnd_1220356 : Nat := 92833955199752975590769

theorem tailTrace_1220356 : CollatzResearch.WordTrace tailWord_1220356 prefixEnd_1220356 92833955199752975590769 := by
  unfold tailWord_1220356
  simp only [CollatzResearch.WordTrace]
  refine ⟨22255019983433053528364461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29673359977910738037819281 22255019983433053528364461)
  ·
    refine ⟨8345632493787395073136673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22255019983433053528364461 8345632493787395073136673)
    ·
      refine ⟨6259224370340546304852505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8345632493787395073136673 6259224370340546304852505)
      ·
        refine ⟨4694418277755409728639379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6259224370340546304852505 4694418277755409728639379)
        ·
          refine ⟨7041627416633114592959069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4694418277755409728639379 7041627416633114592959069)
          ·
            refine ⟨2640610281237417972359651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7041627416633114592959069 2640610281237417972359651)
            ·
              refine ⟨3960915421856126958539477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2640610281237417972359651 3960915421856126958539477)
              ·
                refine ⟨92833955199752975590769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3960915421856126958539477 92833955199752975590769)
                ·
                  rfl

theorem cell21_1220356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 7].length) (baseStart_1220356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220356 prefixEnd_1220356 := by exact prefixLift 1220356
  have htrace : WordTrace (prefixWord ++ tailWord_1220356) baseStart_1220356 baseEnd_1220356 := by
    simpa [prefixWord, tailWord_1220356, baseEnd_1220356] using wordTrace_append hprefix tailTrace_1220356
  have hstable : (prefixWord ++ tailWord_1220356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220356).length < 2 ^ (prefixWord ++ tailWord_1220356).sum := by decide
  have hdescent : baseEnd_1220356 < baseStart_1220356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220387 : List Nat := [1, 1, 1, 4, 2, 1, 2, 6, 3]
def baseStart_1220387 : Nat := 118140960795 + 1220387 * 2 ^ 59
def prefixEnd_1220387 : Nat := 4983230072969 + 3 ^ 40 * 1220387 * 2
def baseEnd_1220387 : Nat := 278508940221609761755577

theorem tailTrace_1220387 : CollatzResearch.WordTrace tailWord_1220387 prefixEnd_1220387 278508940221609761755577 := by
  unfold tailWord_1220387
  simp only [CollatzResearch.WordTrace]
  refine ⟨44511170629753799351107415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29674113753169199567404943 44511170629753799351107415)
  ·
    refine ⟨66766755944630699026661123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44511170629753799351107415 66766755944630699026661123)
    ·
      refine ⟨100150133916946048539991685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66766755944630699026661123 100150133916946048539991685)
      ·
        refine ⟨18778150109427384101248441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100150133916946048539991685 18778150109427384101248441)
        ·
          refine ⟨14083612582070538075936331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18778150109427384101248441 14083612582070538075936331)
          ·
            refine ⟨21125418873105807113904497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14083612582070538075936331 21125418873105807113904497)
            ·
              refine ⟨15844064154829355335428373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21125418873105807113904497 15844064154829355335428373)
              ·
                refine ⟨742690507257626031348205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15844064154829355335428373 742690507257626031348205)
                ·
                  refine ⟨278508940221609761755577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742690507257626031348205 278508940221609761755577)
                  ·
                    rfl

theorem cell21_1220387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 3].length) (baseStart_1220387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220387 prefixEnd_1220387 := by exact prefixLift 1220387
  have htrace : WordTrace (prefixWord ++ tailWord_1220387) baseStart_1220387 baseEnd_1220387 := by
    simpa [prefixWord, tailWord_1220387, baseEnd_1220387] using wordTrace_append hprefix tailTrace_1220387
  have hstable : (prefixWord ++ tailWord_1220387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220387).length < 2 ^ (prefixWord ++ tailWord_1220387).sum := by decide
  have hdescent : baseEnd_1220387 < baseStart_1220387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220511 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 4]
def baseStart_1220511 : Nat := 118140960795 + 1220511 * 2 ^ 59
def prefixEnd_1220511 : Nat := 4983230072969 + 3 ^ 40 * 1220511 * 2
def baseEnd_1220511 : Nat := 278537238711013101688657

theorem tailTrace_1220511 : CollatzResearch.WordTrace tailWord_1220511 prefixEnd_1220511 278537238711013101688657 := by
  unfold tailWord_1220511
  simp only [CollatzResearch.WordTrace]
  refine ⟨44515693281304568528621387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29677128854203045685747591 44515693281304568528621387)
  ·
    refine ⟨66773539921956852792932081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44515693281304568528621387 66773539921956852792932081)
    ·
      refine ⟨50080154941467639594699061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66773539921956852792932081 50080154941467639594699061)
      ·
        refine ⟨4695014525762591212003037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50080154941467639594699061 4695014525762591212003037)
        ·
          refine ⟨1760630447160971704501139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4695014525762591212003037 1760630447160971704501139)
          ·
            refine ⟨2640945670741457556751709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760630447160971704501139 2640945670741457556751709)
            ·
              refine ⟨990354626528046583781891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2640945670741457556751709 990354626528046583781891)
              ·
                refine ⟨1485531939792069875672837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990354626528046583781891 1485531939792069875672837)
                ·
                  refine ⟨278537238711013101688657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1485531939792069875672837 278537238711013101688657)
                  ·
                    rfl

theorem cell21_1220511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 4].length) (baseStart_1220511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220511 prefixEnd_1220511 := by exact prefixLift 1220511
  have htrace : WordTrace (prefixWord ++ tailWord_1220511) baseStart_1220511 baseEnd_1220511 := by
    simpa [prefixWord, tailWord_1220511, baseEnd_1220511] using wordTrace_append hprefix tailTrace_1220511
  have hstable : (prefixWord ++ tailWord_1220511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220511).length < 2 ^ (prefixWord ++ tailWord_1220511).sum := by decide
  have hdescent : baseEnd_1220511 < baseStart_1220511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220536 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 8]
def baseStart_1220536 : Nat := 118140960795 + 1220536 * 2 ^ 59
def prefixEnd_1220536 : Nat := 4983230072969 + 3 ^ 40 * 1220536 * 2
def baseEnd_1220536 : Nat := 278542944051618613771939

theorem tailTrace_1220536 : CollatzResearch.WordTrace tailWord_1220536 prefixEnd_1220536 278542944051618613771939 := by
  unfold tailWord_1220536
  simp only [CollatzResearch.WordTrace]
  refine ⟨22258302553106998899140731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29677736737475998532187641 22258302553106998899140731)
  ·
    refine ⟨33387453829660498348711097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22258302553106998899140731 33387453829660498348711097)
    ·
      refine ⟨25040590372245373761533323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33387453829660498348711097 25040590372245373761533323)
      ·
        refine ⟨37560885558368060642299985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25040590372245373761533323 37560885558368060642299985)
        ·
          refine ⟨28170664168776045481724989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37560885558368060642299985 28170664168776045481724989)
          ·
            refine ⟨10563999063291017055646871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28170664168776045481724989 10563999063291017055646871)
            ·
              refine ⟨15845998594936525583470307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10563999063291017055646871 15845998594936525583470307)
              ·
                refine ⟨23768997892404788375205461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15845998594936525583470307 23768997892404788375205461)
                ·
                  refine ⟨278542944051618613771939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23768997892404788375205461 278542944051618613771939)
                  ·
                    rfl

theorem cell21_1220536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 8].length) (baseStart_1220536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220536 prefixEnd_1220536 := by exact prefixLift 1220536
  have htrace : WordTrace (prefixWord ++ tailWord_1220536) baseStart_1220536 baseEnd_1220536 := by
    simpa [prefixWord, tailWord_1220536, baseEnd_1220536] using wordTrace_append hprefix tailTrace_1220536
  have hstable : (prefixWord ++ tailWord_1220536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220536).length < 2 ^ (prefixWord ++ tailWord_1220536).sum := by decide
  have hdescent : baseEnd_1220536 < baseStart_1220536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220567 : List Nat := [1, 1, 3, 2, 1, 1, 6, 6]
def baseStart_1220567 : Nat := 118140960795 + 1220567 * 2 ^ 59
def prefixEnd_1220567 : Nat := 4983230072969 + 3 ^ 40 * 1220567 * 2
def baseEnd_1220567 : Nat := 92850006224656482918403

theorem tailTrace_1220567 : CollatzResearch.WordTrace tailWord_1220567 prefixEnd_1220567 92850006224656482918403 := by
  unfold tailWord_1220567
  simp only [CollatzResearch.WordTrace]
  refine ⟨44517735769101690092659955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29678490512734460061773303 44517735769101690092659955)
  ·
    refine ⟨66776603653652535138989933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44517735769101690092659955 66776603653652535138989933)
    ·
      refine ⟨25041226370119700677121225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66776603653652535138989933 25041226370119700677121225)
      ·
        refine ⟨18780919777589775507840919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25041226370119700677121225 18780919777589775507840919)
        ·
          refine ⟨28171379666384663261761379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18780919777589775507840919 28171379666384663261761379)
          ·
            refine ⟨42257069499576994892642069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28171379666384663261761379 42257069499576994892642069)
            ·
              refine ⟨1980800132792671635592597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42257069499576994892642069 1980800132792671635592597)
              ·
                refine ⟨92850006224656482918403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1980800132792671635592597 92850006224656482918403)
                ·
                  rfl

theorem cell21_1220567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 6].length) (baseStart_1220567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220567 prefixEnd_1220567 := by exact prefixLift 1220567
  have htrace : WordTrace (prefixWord ++ tailWord_1220567) baseStart_1220567 baseEnd_1220567 := by
    simpa [prefixWord, tailWord_1220567, baseEnd_1220567] using wordTrace_append hprefix tailTrace_1220567
  have hstable : (prefixWord ++ tailWord_1220567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220567).length < 2 ^ (prefixWord ++ tailWord_1220567).sum := by decide
  have hdescent : baseEnd_1220567 < baseStart_1220567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220570 : List Nat := [3, 1, 1, 2, 5, 1, 1, 3, 4]
def baseStart_1220570 : Nat := 118140960795 + 1220570 * 2 ^ 59
def prefixEnd_1220570 : Nat := 4983230072969 + 3 ^ 40 * 1220570 * 2
def baseEnd_1220570 : Nat := 278550703314842110205203

theorem tailTrace_1220570 : CollatzResearch.WordTrace tailWord_1220570 prefixEnd_1220570 278550703314842110205203 := by
  unfold tailWord_1220570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11129461297022705401254791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29678563458727214403346109 11129461297022705401254791)
  ·
    refine ⟨16694191945534058101882187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11129461297022705401254791 16694191945534058101882187)
    ·
      refine ⟨25041287918301087152823281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16694191945534058101882187 25041287918301087152823281)
      ·
        refine ⟨18780965938725815364617461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25041287918301087152823281 18780965938725815364617461)
        ·
          refine ⟨1760715556755545190432887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18780965938725815364617461 1760715556755545190432887)
          ·
            refine ⟨2641073335133317785649331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760715556755545190432887 2641073335133317785649331)
            ·
              refine ⟨3961610002699976678473997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641073335133317785649331 3961610002699976678473997)
              ·
                refine ⟨1485603751012491254427749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3961610002699976678473997 1485603751012491254427749)
                ·
                  refine ⟨278550703314842110205203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1485603751012491254427749 278550703314842110205203)
                  ·
                    rfl

theorem cell21_1220570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 4].length) (baseStart_1220570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220570 prefixEnd_1220570 := by exact prefixLift 1220570
  have htrace : WordTrace (prefixWord ++ tailWord_1220570) baseStart_1220570 baseEnd_1220570 := by
    simpa [prefixWord, tailWord_1220570, baseEnd_1220570] using wordTrace_append hprefix tailTrace_1220570
  have hstable : (prefixWord ++ tailWord_1220570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220570).length < 2 ^ (prefixWord ++ tailWord_1220570).sum := by decide
  have hdescent : baseEnd_1220570 < baseStart_1220570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220694 : List Nat := [5, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1220694 : Nat := 118140960795 + 1220694 * 2 ^ 59
def prefixEnd_1220694 : Nat := 4983230072969 + 3 ^ 40 * 1220694 * 2
def baseEnd_1220694 : Nat := 92859667268081816712761

theorem tailTrace_1220694 : CollatzResearch.WordTrace tailWord_1220694 prefixEnd_1220694 92859667268081816712761 := by
  unfold tailWord_1220694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782647989977599423908321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29681578559761060521688757 2782647989977599423908321)
  ·
    refine ⟨2086985992483199567931241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2782647989977599423908321 2086985992483199567931241)
    ·
      refine ⟨1565239494362399675948431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2086985992483199567931241 1565239494362399675948431)
      ·
        refine ⟨2347859241543599513922647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565239494362399675948431 2347859241543599513922647)
        ·
          refine ⟨3521788862315399270883971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2347859241543599513922647 3521788862315399270883971)
          ·
            refine ⟨5282683293473098906325957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3521788862315399270883971 5282683293473098906325957)
            ·
              refine ⟨990503117526206044936117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5282683293473098906325957 990503117526206044936117)
              ·
                refine ⟨92859667268081816712761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 990503117526206044936117 92859667268081816712761)
                ·
                  rfl

theorem cell21_1220694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1220694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220694 prefixEnd_1220694 := by exact prefixLift 1220694
  have htrace : WordTrace (prefixWord ++ tailWord_1220694) baseStart_1220694 baseEnd_1220694 := by
    simpa [prefixWord, tailWord_1220694, baseEnd_1220694] using wordTrace_append hprefix tailTrace_1220694
  have hstable : (prefixWord ++ tailWord_1220694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220694).length < 2 ^ (prefixWord ++ tailWord_1220694).sum := by decide
  have hdescent : baseEnd_1220694 < baseStart_1220694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220719 : List Nat := [1, 1, 2, 1, 3, 6, 7]
def baseStart_1220719 : Nat := 118140960795 + 1220719 * 2 ^ 59
def prefixEnd_1220719 : Nat := 4983230072969 + 3 ^ 40 * 1220719 * 2
def baseEnd_1220719 : Nat := 30953856349427884691285

theorem tailTrace_1220719 : CollatzResearch.WordTrace tailWord_1220719 prefixEnd_1220719 30953856349427884691285 := by
  unfold tailWord_1220719
  simp only [CollatzResearch.WordTrace]
  refine ⟨44523279664551020052193211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29682186443034013368128807 44523279664551020052193211)
  ·
    refine ⟨66784919496826530078289817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44523279664551020052193211 66784919496826530078289817)
    ·
      refine ⟨50088689622619897558717363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66784919496826530078289817 50088689622619897558717363)
      ·
        refine ⟨75133034433929846338076045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50088689622619897558717363 75133034433929846338076045)
        ·
          refine ⟨28174887912723692376778517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75133034433929846338076045 28174887912723692376778517)
          ·
            refine ⟨1320697870908923080161493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28174887912723692376778517 1320697870908923080161493)
            ·
              refine ⟨30953856349427884691285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1320697870908923080161493 30953856349427884691285)
              ·
                rfl

theorem cell21_1220719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 7].length) (baseStart_1220719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220719 prefixEnd_1220719 := by exact prefixLift 1220719
  have htrace : WordTrace (prefixWord ++ tailWord_1220719) baseStart_1220719 baseEnd_1220719 := by
    simpa [prefixWord, tailWord_1220719, baseEnd_1220719] using wordTrace_append hprefix tailTrace_1220719
  have hstable : (prefixWord ++ tailWord_1220719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220719).length < 2 ^ (prefixWord ++ tailWord_1220719).sum := by decide
  have hdescent : baseEnd_1220719 < baseStart_1220719 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220885 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 7]
def baseStart_1220885 : Nat := 118140960795 + 1220885 * 2 ^ 59
def prefixEnd_1220885 : Nat := 4983230072969 + 3 ^ 40 * 1220885 * 2
def baseEnd_1220885 : Nat := 278622590606471562454559

theorem tailTrace_1220885 : CollatzResearch.WordTrace tailWord_1220885 prefixEnd_1220885 278622590606471562454559 := by
  unfold tailWord_1220885
  simp only [CollatzResearch.WordTrace]
  refine ⟨44529334181949630402736109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29686222787966420268490739 44529334181949630402736109)
  ·
    refine ⟨16698500318231111401026041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44529334181949630402736109 16698500318231111401026041)
    ·
      refine ⟨12523875238673333550769531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16698500318231111401026041 12523875238673333550769531)
      ·
        refine ⟨18785812858010000326154297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12523875238673333550769531 18785812858010000326154297)
        ·
          refine ⟨14089359643507500244615723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18785812858010000326154297 14089359643507500244615723)
          ·
            refine ⟨21134039465261250366923585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14089359643507500244615723 21134039465261250366923585)
            ·
              refine ⟨15850529598945937775192689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21134039465261250366923585 15850529598945937775192689)
              ·
                refine ⟨11887897199209453331394517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15850529598945937775192689 11887897199209453331394517)
                ·
                  refine ⟨278622590606471562454559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11887897199209453331394517 278622590606471562454559)
                  ·
                    rfl

theorem cell21_1220885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_1220885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220885 prefixEnd_1220885 := by exact prefixLift 1220885
  have htrace : WordTrace (prefixWord ++ tailWord_1220885) baseStart_1220885 baseEnd_1220885 := by
    simpa [prefixWord, tailWord_1220885, baseEnd_1220885] using wordTrace_append hprefix tailTrace_1220885
  have hstable : (prefixWord ++ tailWord_1220885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220885).length < 2 ^ (prefixWord ++ tailWord_1220885).sum := by decide
  have hdescent : baseEnd_1220885 < baseStart_1220885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220894 : List Nat := [4, 3, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1220894 : Nat := 118140960795 + 1220894 * 2 ^ 59
def prefixEnd_1220894 : Nat := 4983230072969 + 3 ^ 40 * 1220894 * 2
def baseEnd_1220894 : Nat := 278624644529089546804541

theorem tailTrace_1220894 : CollatzResearch.WordTrace tailWord_1220894 prefixEnd_1220894 278624644529089546804541 := by
  unfold tailWord_1220894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5566207804864628117476717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29686441625944683293209157 5566207804864628117476717)
  ·
    refine ⟨2087327926824235544053769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5566207804864628117476717 2087327926824235544053769)
    ·
      refine ⟨1565495945118176658040327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2087327926824235544053769 1565495945118176658040327)
      ·
        refine ⟨2348243917677264987060491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565495945118176658040327 2348243917677264987060491)
        ·
          refine ⟨3522365876515897480590737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2348243917677264987060491 3522365876515897480590737)
          ·
            refine ⟨2641774407386923110443053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3522365876515897480590737 2641774407386923110443053)
            ·
              refine ⟨990665402770096166416145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2641774407386923110443053 990665402770096166416145)
              ·
                refine ⟨742999052077572124812109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990665402770096166416145 742999052077572124812109)
                ·
                  refine ⟨278624644529089546804541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 742999052077572124812109 278624644529089546804541)
                  ·
                    rfl

theorem cell21_1220894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1220894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220894 prefixEnd_1220894 := by exact prefixLift 1220894
  have htrace : WordTrace (prefixWord ++ tailWord_1220894) baseStart_1220894 baseEnd_1220894 := by
    simpa [prefixWord, tailWord_1220894, baseEnd_1220894] using wordTrace_append hprefix tailTrace_1220894
  have hstable : (prefixWord ++ tailWord_1220894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220894).length < 2 ^ (prefixWord ++ tailWord_1220894).sum := by decide
  have hdescent : baseEnd_1220894 < baseStart_1220894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1220978 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_1220978 : Nat := 118140960795 + 1220978 * 2 ^ 59
def prefixEnd_1220978 : Nat := 4983230072969 + 3 ^ 40 * 1220978 * 2
def baseEnd_1220978 : Nat := 278643814473524067404369

theorem tailTrace_1220978 : CollatzResearch.WordTrace tailWord_1220978 prefixEnd_1220978 278643814473524067404369 := by
  unfold tailWord_1220978
  simp only [CollatzResearch.WordTrace]
  refine ⟨11133181542653176821467897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29688484113741804857247725 11133181542653176821467897)
  ·
    refine ⟨8349886156989882616100923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11133181542653176821467897 8349886156989882616100923)
    ·
      refine ⟨12524829235484823924151385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8349886156989882616100923 12524829235484823924151385)
      ·
        refine ⟨9393621926613617943113539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12524829235484823924151385 9393621926613617943113539)
        ·
          refine ⟨14090432889920426914670309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9393621926613617943113539 14090432889920426914670309)
          ·
            refine ⟨2641956166860080046500683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14090432889920426914670309 2641956166860080046500683)
            ·
              refine ⟨3962934250290120069751025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2641956166860080046500683 3962934250290120069751025)
              ·
                refine ⟨2972200687717590052313269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3962934250290120069751025 2972200687717590052313269)
                ·
                  refine ⟨278643814473524067404369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2972200687717590052313269 278643814473524067404369)
                  ·
                    rfl

theorem cell21_1220978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_1220978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1220978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1220978 prefixEnd_1220978 := by exact prefixLift 1220978
  have htrace : WordTrace (prefixWord ++ tailWord_1220978) baseStart_1220978 baseEnd_1220978 := by
    simpa [prefixWord, tailWord_1220978, baseEnd_1220978] using wordTrace_append hprefix tailTrace_1220978
  have hstable : (prefixWord ++ tailWord_1220978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1220978).length < 2 ^ (prefixWord ++ tailWord_1220978).sum := by decide
  have hdescent : baseEnd_1220978 < baseStart_1220978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1220978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221026 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1221026 : Nat := 118140960795 + 1221026 * 2 ^ 59
def prefixEnd_1221026 : Nat := 4983230072969 + 3 ^ 40 * 1221026 * 2
def baseEnd_1221026 : Nat := 278654768727486650604271

theorem tailTrace_1221026 : CollatzResearch.WordTrace tailWord_1221026 prefixEnd_1221026 278654768727486650604271 := by
  unfold tailWord_1221026
  simp only [CollatzResearch.WordTrace]
  refine ⟨11133619218609702870904733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29689651249625874322412621 11133619218609702870904733)
  ·
    refine ⟨4175107206978638576589275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11133619218609702870904733 4175107206978638576589275)
    ·
      refine ⟨6262660810467957864883913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4175107206978638576589275 6262660810467957864883913)
      ·
        refine ⟨4696995607850968398662935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6262660810467957864883913 4696995607850968398662935)
        ·
          refine ⟨7045493411776452597994403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4696995607850968398662935 7045493411776452597994403)
          ·
            refine ⟨10568240117664678896991605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7045493411776452597994403 10568240117664678896991605)
            ·
              refine ⟨990772511031063646592963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10568240117664678896991605 990772511031063646592963)
              ·
                refine ⟨1486158766546595469889445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 990772511031063646592963 1486158766546595469889445)
                ·
                  refine ⟨278654768727486650604271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1486158766546595469889445 278654768727486650604271)
                  ·
                    rfl

theorem cell21_1221026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1221026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221026 prefixEnd_1221026 := by exact prefixLift 1221026
  have htrace : WordTrace (prefixWord ++ tailWord_1221026) baseStart_1221026 baseEnd_1221026 := by
    simpa [prefixWord, tailWord_1221026, baseEnd_1221026] using wordTrace_append hprefix tailTrace_1221026
  have hstable : (prefixWord ++ tailWord_1221026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221026).length < 2 ^ (prefixWord ++ tailWord_1221026).sum := by decide
  have hdescent : baseEnd_1221026 < baseStart_1221026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221085 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 4]
def baseStart_1221085 : Nat := 118140960795 + 1221085 * 2 ^ 59
def prefixEnd_1221085 : Nat := 4983230072969 + 3 ^ 40 * 1221085 * 2
def baseEnd_1221085 : Nat := 278668233331315659120817

theorem tailTrace_1221085 : CollatzResearch.WordTrace tailWord_1221085 prefixEnd_1221085 278668233331315659120817 := by
  unfold tailWord_1221085
  simp only [CollatzResearch.WordTrace]
  refine ⟨44536628781225064560016709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29691085854150043040011139 44536628781225064560016709)
  ·
    refine ⟨8350617896479699605003133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44536628781225064560016709 8350617896479699605003133)
    ·
      refine ⟨3131481711179887351876175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8350617896479699605003133 3131481711179887351876175)
      ·
        refine ⟨4697222566769831027814263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3131481711179887351876175 4697222566769831027814263)
        ·
          refine ⟨7045833850154746541721395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4697222566769831027814263 7045833850154746541721395)
          ·
            refine ⟨10568750775232119812582093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7045833850154746541721395 10568750775232119812582093)
            ·
              refine ⟨3963281540712044929718285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10568750775232119812582093 3963281540712044929718285)
              ·
                refine ⟨1486230577767016848644357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3963281540712044929718285 1486230577767016848644357)
                ·
                  refine ⟨278668233331315659120817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1486230577767016848644357 278668233331315659120817)
                  ·
                    rfl

theorem cell21_1221085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_1221085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221085 prefixEnd_1221085 := by exact prefixLift 1221085
  have htrace : WordTrace (prefixWord ++ tailWord_1221085) baseStart_1221085 baseEnd_1221085 := by
    simpa [prefixWord, tailWord_1221085, baseEnd_1221085] using wordTrace_append hprefix tailTrace_1221085
  have hstable : (prefixWord ++ tailWord_1221085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221085).length < 2 ^ (prefixWord ++ tailWord_1221085).sum := by decide
  have hdescent : baseEnd_1221085 < baseStart_1221085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221122 : List Nat := [3, 4, 1, 2, 2, 2, 2, 2, 3]
def baseStart_1221122 : Nat := 118140960795 + 1221122 * 2 ^ 59
def prefixEnd_1221122 : Nat := 4983230072969 + 3 ^ 40 * 1221122 * 2
def baseEnd_1221122 : Nat := 278676677235411817004075

theorem tailTrace_1221122 : CollatzResearch.WordTrace tailWord_1221122 prefixEnd_1221122 278676677235411817004075 := by
  unfold tailWord_1221122
  simp only [CollatzResearch.WordTrace]
  refine ⟨11134494570522754969778405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29691985521394013252742413 11134494570522754969778405)
  ·
    refine ⟨2087717731973016556833451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11134494570522754969778405 2087717731973016556833451)
    ·
      refine ⟨3131576597959524835250177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2087717731973016556833451 3131576597959524835250177)
      ·
        refine ⟨2348682448469643626437633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3131576597959524835250177 2348682448469643626437633)
        ·
          refine ⟨1761511836352232719828225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2348682448469643626437633 1761511836352232719828225)
          ·
            refine ⟨1321133877264174539871169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1761511836352232719828225 1321133877264174539871169)
            ·
              refine ⟨990850407948130904903377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1321133877264174539871169 990850407948130904903377)
              ·
                refine ⟨743137805961098178677533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990850407948130904903377 743137805961098178677533)
                ·
                  refine ⟨278676677235411817004075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743137805961098178677533 278676677235411817004075)
                  ·
                    rfl

theorem cell21_1221122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_1221122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221122 prefixEnd_1221122 := by exact prefixLift 1221122
  have htrace : WordTrace (prefixWord ++ tailWord_1221122) baseStart_1221122 baseEnd_1221122 := by
    simpa [prefixWord, tailWord_1221122, baseEnd_1221122] using wordTrace_append hprefix tailTrace_1221122
  have hstable : (prefixWord ++ tailWord_1221122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221122).length < 2 ^ (prefixWord ++ tailWord_1221122).sum := by decide
  have hdescent : baseEnd_1221122 < baseStart_1221122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221133 : List Nat := [1, 7, 1, 1, 1, 1, 3, 6]
def baseStart_1221133 : Nat := 118140960795 + 1221133 * 2 ^ 59
def prefixEnd_1221133 : Nat := 4983230072969 + 3 ^ 40 * 1221133 * 2
def baseEnd_1221133 : Nat := 92893062528426080773573

theorem tailTrace_1221133 : CollatzResearch.WordTrace tailWord_1221133 prefixEnd_1221133 92893062528426080773573 := by
  unfold tailWord_1221133
  simp only [CollatzResearch.WordTrace]
  refine ⟨44538379485051168757764053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29692252990034112505176035 44538379485051168757764053)
  ·
    refine ⟨1043868269180886767760095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 44538379485051168757764053 1043868269180886767760095)
    ·
      refine ⟨1565802403771330151640143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1043868269180886767760095 1565802403771330151640143)
      ·
        refine ⟨2348703605656995227460215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565802403771330151640143 2348703605656995227460215)
        ·
          refine ⟨3523055408485492841190323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2348703605656995227460215 3523055408485492841190323)
          ·
            refine ⟨5284583112728239261785485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3523055408485492841190323 5284583112728239261785485)
            ·
              refine ⟨1981718667273089723169557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5284583112728239261785485 1981718667273089723169557)
              ·
                refine ⟨92893062528426080773573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1981718667273089723169557 92893062528426080773573)
                ·
                  rfl

theorem cell21_1221133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 6].length) (baseStart_1221133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221133 prefixEnd_1221133 := by exact prefixLift 1221133
  have htrace : WordTrace (prefixWord ++ tailWord_1221133) baseStart_1221133 baseEnd_1221133 := by
    simpa [prefixWord, tailWord_1221133, baseEnd_1221133] using wordTrace_append hprefix tailTrace_1221133
  have hstable : (prefixWord ++ tailWord_1221133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221133).length < 2 ^ (prefixWord ++ tailWord_1221133).sum := by decide
  have hdescent : baseEnd_1221133 < baseStart_1221133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221189 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 5]
def baseStart_1221189 : Nat := 118140960795 + 1221189 * 2 ^ 59
def prefixEnd_1221189 : Nat := 4983230072969 + 3 ^ 40 * 1221189 * 2
def baseEnd_1221189 : Nat := 278691967548234589387271

theorem tailTrace_1221189 : CollatzResearch.WordTrace tailWord_1221189 prefixEnd_1221189 278691967548234589387271 := by
  unfold tailWord_1221189
  simp only [CollatzResearch.WordTrace]
  refine ⟨44540421972848290321802621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29693614648565526881201747 44540421972848290321802621)
  ·
    refine ⟨16702658239818108870675983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44540421972848290321802621 16702658239818108870675983)
    ·
      refine ⟨25053987359727163306013975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16702658239818108870675983 25053987359727163306013975)
      ·
        refine ⟨37580981039590744959020963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25053987359727163306013975 37580981039590744959020963)
        ·
          refine ⟨56371471559386117438531445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37580981039590744959020963 56371471559386117438531445)
          ·
            refine ⟨5284825458692448509862323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56371471559386117438531445 5284825458692448509862323)
            ·
              refine ⟨7927238188038672764793485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5284825458692448509862323 7927238188038672764793485)
              ·
                refine ⟨2972714320514502286797557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7927238188038672764793485 2972714320514502286797557)
                ·
                  refine ⟨278691967548234589387271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2972714320514502286797557 278691967548234589387271)
                  ·
                    rfl

theorem cell21_1221189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_1221189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221189 prefixEnd_1221189 := by exact prefixLift 1221189
  have htrace : WordTrace (prefixWord ++ tailWord_1221189) baseStart_1221189 baseEnd_1221189 := by
    simpa [prefixWord, tailWord_1221189, baseEnd_1221189] using wordTrace_append hprefix tailTrace_1221189
  have hstable : (prefixWord ++ tailWord_1221189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221189).length < 2 ^ (prefixWord ++ tailWord_1221189).sum := by decide
  have hdescent : baseEnd_1221189 < baseStart_1221189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221299 : List Nat := [1, 1, 1, 2, 3, 4, 4, 2, 3]
def baseStart_1221299 : Nat := 118140960795 + 1221299 * 2 ^ 59
def prefixEnd_1221299 : Nat := 4983230072969 + 3 ^ 40 * 1221299 * 2
def baseEnd_1221299 : Nat := 278717071046898842553713

theorem tailTrace_1221299 : CollatzResearch.WordTrace tailWord_1221299 prefixEnd_1221299 278717071046898842553713 := by
  unfold tailWord_1221299
  simp only [CollatzResearch.WordTrace]
  refine ⟨44544434002449779108306951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29696289334966519405537967 44544434002449779108306951)
  ·
    refine ⟨66816651003674668662460427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44544434002449779108306951 66816651003674668662460427)
    ·
      refine ⟨100224976505512002993690641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66816651003674668662460427 100224976505512002993690641)
      ·
        refine ⟨75168732379134002245267981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100224976505512002993690641 75168732379134002245267981)
        ·
          refine ⟨28188274642175250841975493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75168732379134002245267981 28188274642175250841975493)
          ·
            refine ⟨5285301495407859532870405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28188274642175250841975493 5285301495407859532870405)
            ·
              refine ⟨990994030388973662413201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5285301495407859532870405 990994030388973662413201)
              ·
                refine ⟨743245522791730246809901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 990994030388973662413201 743245522791730246809901)
                ·
                  refine ⟨278717071046898842553713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743245522791730246809901 278717071046898842553713)
                  ·
                    rfl

theorem cell21_1221299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 3].length) (baseStart_1221299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221299 prefixEnd_1221299 := by exact prefixLift 1221299
  have htrace : WordTrace (prefixWord ++ tailWord_1221299) baseStart_1221299 baseEnd_1221299 := by
    simpa [prefixWord, tailWord_1221299, baseEnd_1221299] using wordTrace_append hprefix tailTrace_1221299
  have hstable : (prefixWord ++ tailWord_1221299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221299).length < 2 ^ (prefixWord ++ tailWord_1221299).sum := by decide
  have hdescent : baseEnd_1221299 < baseStart_1221299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221302 : List Nat := [5, 1, 3, 1, 3, 1, 1, 6]
def baseStart_1221302 : Nat := 118140960795 + 1221302 * 2 ^ 59
def prefixEnd_1221302 : Nat := 4983230072969 + 3 ^ 40 * 1221302 * 2
def baseEnd_1221302 : Nat := 92905918562590501334569

theorem tailTrace_1221302 : CollatzResearch.WordTrace tailWord_1221302 prefixEnd_1221302 92905918562590501334569 := by
  unfold tailWord_1221302
  simp only [CollatzResearch.WordTrace]
  refine ⟨2784033963839931913791635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29696362280959273747110773 2784033963839931913791635)
  ·
    refine ⟨4176050945759897870687453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2784033963839931913791635 4176050945759897870687453)
    ·
      refine ⟨1566019104659961701507795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4176050945759897870687453 1566019104659961701507795)
      ·
        refine ⟨2349028656989942552261693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566019104659961701507795 2349028656989942552261693)
        ·
          refine ⟨880885746371228457098135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2349028656989942552261693 880885746371228457098135)
          ·
            refine ⟨1321328619556842685647203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880885746371228457098135 1321328619556842685647203)
            ·
              refine ⟨1981992929335264028470805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321328619556842685647203 1981992929335264028470805)
              ·
                refine ⟨92905918562590501334569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1981992929335264028470805 92905918562590501334569)
                ·
                  rfl

theorem cell21_1221302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_1221302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221302 prefixEnd_1221302 := by exact prefixLift 1221302
  have htrace : WordTrace (prefixWord ++ tailWord_1221302) baseStart_1221302 baseEnd_1221302 := by
    simpa [prefixWord, tailWord_1221302, baseEnd_1221302] using wordTrace_append hprefix tailTrace_1221302
  have hstable : (prefixWord ++ tailWord_1221302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221302).length < 2 ^ (prefixWord ++ tailWord_1221302).sum := by decide
  have hdescent : baseEnd_1221302 < baseStart_1221302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221358 : List Nat := [4, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_1221358 : Nat := 118140960795 + 1221358 * 2 ^ 59
def prefixEnd_1221358 : Nat := 4983230072969 + 3 ^ 40 * 1221358 * 2
def baseEnd_1221358 : Nat := 278730535650727851070259

theorem tailTrace_1221358 : CollatzResearch.WordTrace tailWord_1221358 prefixEnd_1221358 278730535650727851070259 := by
  unfold tailWord_1221358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5568323238654504023088091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29697723939490688123136485 5568323238654504023088091)
  ·
    refine ⟨8352484857981756034632137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5568323238654504023088091 8352484857981756034632137)
    ·
      refine ⟨6264363643486317025974103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8352484857981756034632137 6264363643486317025974103)
      ·
        refine ⟨9396545465229475538961155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264363643486317025974103 9396545465229475538961155)
        ·
          refine ⟨14094818197844213308441733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9396545465229475538961155 14094818197844213308441733)
          ·
            refine ⟨2642778412095789995332825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14094818197844213308441733 2642778412095789995332825)
            ·
              refine ⟨1982083809071842496499619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2642778412095789995332825 1982083809071842496499619)
              ·
                refine ⟨2973125713607763744749429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982083809071842496499619 2973125713607763744749429)
                ·
                  refine ⟨278730535650727851070259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2973125713607763744749429 278730535650727851070259)
                  ·
                    rfl

theorem cell21_1221358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_1221358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221358 prefixEnd_1221358 := by exact prefixLift 1221358
  have htrace : WordTrace (prefixWord ++ tailWord_1221358) baseStart_1221358 baseEnd_1221358 := by
    simpa [prefixWord, tailWord_1221358, baseEnd_1221358] using wordTrace_append hprefix tailTrace_1221358
  have hstable : (prefixWord ++ tailWord_1221358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221358).length < 2 ^ (prefixWord ++ tailWord_1221358).sum := by decide
  have hdescent : baseEnd_1221358 < baseStart_1221358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221364 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1221364 : Nat := 118140960795 + 1221364 * 2 ^ 59
def prefixEnd_1221364 : Nat := 4983230072969 + 3 ^ 40 * 1221364 * 2
def baseEnd_1221364 : Nat := 278731904932473173970247

theorem tailTrace_1221364 : CollatzResearch.WordTrace tailWord_1221364 prefixEnd_1221364 278731904932473173970247 := by
  unfold tailWord_1221364
  simp only [CollatzResearch.WordTrace]
  refine ⟨22273402373607147604711573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29697869831476196806282097 22273402373607147604711573)
  ·
    refine ⟨1044065736262835043970855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22273402373607147604711573 1044065736262835043970855)
    ·
      refine ⟨1566098604394252565956283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1044065736262835043970855 1566098604394252565956283)
      ·
        refine ⟨2349147906591378848934425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1566098604394252565956283 2349147906591378848934425)
        ·
          refine ⟨1761860929943534136700819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2349147906591378848934425 1761860929943534136700819)
          ·
            refine ⟨2642791394915301205051229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761860929943534136700819 2642791394915301205051229)
            ·
              refine ⟨991046773093237951894211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2642791394915301205051229 991046773093237951894211)
              ·
                refine ⟨1486570159639856927841317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991046773093237951894211 1486570159639856927841317)
                ·
                  refine ⟨278731904932473173970247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1486570159639856927841317 278731904932473173970247)
                  ·
                    rfl

theorem cell21_1221364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1221364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221364 prefixEnd_1221364 := by exact prefixLift 1221364
  have htrace : WordTrace (prefixWord ++ tailWord_1221364) baseStart_1221364 baseEnd_1221364 := by
    simpa [prefixWord, tailWord_1221364, baseEnd_1221364] using wordTrace_append hprefix tailTrace_1221364
  have hstable : (prefixWord ++ tailWord_1221364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221364).length < 2 ^ (prefixWord ++ tailWord_1221364).sum := by decide
  have hdescent : baseEnd_1221364 < baseStart_1221364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221386 : List Nat := [3, 1, 2, 2, 1, 2, 3, 7]
def baseStart_1221386 : Nat := 118140960795 + 1221386 * 2 ^ 59
def prefixEnd_1221386 : Nat := 4983230072969 + 3 ^ 40 * 1221386 * 2
def baseEnd_1221386 : Nat := 92912308544068674867845

theorem tailTrace_1221386 : CollatzResearch.WordTrace tailWord_1221386 prefixEnd_1221386 92912308544068674867845 := by
  unfold tailWord_1221386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11136901788283648241681003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29698404768756395311149341 11136901788283648241681003)
  ·
    refine ⟨16705352682425472362521505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11136901788283648241681003 16705352682425472362521505)
    ·
      refine ⟨12529014511819104271891129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16705352682425472362521505 12529014511819104271891129)
      ·
        refine ⟨9396760883864328203918347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12529014511819104271891129 9396760883864328203918347)
        ·
          refine ⟨14095141325796492305877521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9396760883864328203918347 14095141325796492305877521)
          ·
            refine ⟨10571355994347369229408141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14095141325796492305877521 10571355994347369229408141)
            ·
              refine ⟨3964258497880263461028053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10571355994347369229408141 3964258497880263461028053)
              ·
                refine ⟨92912308544068674867845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3964258497880263461028053 92912308544068674867845)
                ·
                  rfl

theorem cell21_1221386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_1221386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221386 prefixEnd_1221386 := by exact prefixLift 1221386
  have htrace : WordTrace (prefixWord ++ tailWord_1221386) baseStart_1221386 baseEnd_1221386 := by
    simpa [prefixWord, tailWord_1221386, baseEnd_1221386] using wordTrace_append hprefix tailTrace_1221386
  have hstable : (prefixWord ++ tailWord_1221386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221386).length < 2 ^ (prefixWord ++ tailWord_1221386).sum := by decide
  have hdescent : baseEnd_1221386 < baseStart_1221386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221462 : List Nat := [5, 2, 14]
def baseStart_1221462 : Nat := 118140960795 + 1221462 * 2 ^ 59
def prefixEnd_1221462 : Nat := 4983230072969 + 3 ^ 40 * 1221462 * 2
def baseEnd_1221462 : Nat := 382378971011861154097

theorem tailTrace_1221462 : CollatzResearch.WordTrace tailWord_1221462 prefixEnd_1221462 382378971011861154097 := by
  unfold tailWord_1221462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2784398693803703621655665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29700252733906171964327093 2784398693803703621655665)
  ·
    refine ⟨2088299020352777716241749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2784398693803703621655665 2088299020352777716241749)
    ·
      refine ⟨382378971011861154097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 2088299020352777716241749 382378971011861154097)
      ·
        rfl

theorem cell21_1221462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 14].length) (baseStart_1221462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221462 prefixEnd_1221462 := by exact prefixLift 1221462
  have htrace : WordTrace (prefixWord ++ tailWord_1221462) baseStart_1221462 baseEnd_1221462 := by
    simpa [prefixWord, tailWord_1221462, baseEnd_1221462] using wordTrace_append hprefix tailTrace_1221462
  have hstable : (prefixWord ++ tailWord_1221462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221462).length < 2 ^ (prefixWord ++ tailWord_1221462).sum := by decide
  have hdescent : baseEnd_1221462 < baseStart_1221462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221468 : List Nat := [2, 2, 4, 2, 1, 1, 4, 2, 3]
def baseStart_1221468 : Nat := 118140960795 + 1221468 * 2 ^ 59
def prefixEnd_1221468 : Nat := 4983230072969 + 3 ^ 40 * 1221468 * 2
def baseEnd_1221468 : Nat := 278755639149392104236701

theorem tailTrace_1221468 : CollatzResearch.WordTrace tailWord_1221468 prefixEnd_1221468 278755639149392104236701 := by
  unfold tailWord_1221468
  simp only [CollatzResearch.WordTrace]
  refine ⟨22275298969418760485604529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29700398625891680647472705 22275298969418760485604529)
  ·
    refine ⟨16706474227064070364203397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22275298969418760485604529 16706474227064070364203397)
    ·
      refine ⟨3132463917574513193288137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16706474227064070364203397 3132463917574513193288137)
      ·
        refine ⟨2349347938180884894966103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3132463917574513193288137 2349347938180884894966103)
        ·
          refine ⟨3524021907271327342449155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349347938180884894966103 3524021907271327342449155)
          ·
            refine ⟨5286032860906991013673733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524021907271327342449155 5286032860906991013673733)
            ·
              refine ⟨991131161420060815063825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5286032860906991013673733 991131161420060815063825)
              ·
                refine ⟨743348371065045611297869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 991131161420060815063825 743348371065045611297869)
                ·
                  refine ⟨278755639149392104236701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743348371065045611297869 278755639149392104236701)
                  ·
                    rfl

theorem cell21_1221468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_1221468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221468 prefixEnd_1221468 := by exact prefixLift 1221468
  have htrace : WordTrace (prefixWord ++ tailWord_1221468) baseStart_1221468 baseEnd_1221468 := by
    simpa [prefixWord, tailWord_1221468, baseEnd_1221468] using wordTrace_append hprefix tailTrace_1221468
  have hstable : (prefixWord ++ tailWord_1221468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221468).length < 2 ^ (prefixWord ++ tailWord_1221468).sum := by decide
  have hdescent : baseEnd_1221468 < baseStart_1221468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221479 : List Nat := [1, 1, 5, 1, 2, 4, 1, 6]
def baseStart_1221479 : Nat := 118140960795 + 1221479 * 2 ^ 59
def prefixEnd_1221479 : Nat := 4983230072969 + 3 ^ 40 * 1221479 * 2
def baseEnd_1221479 : Nat := 92919383166419509851115

theorem tailTrace_1221479 : CollatzResearch.WordTrace tailWord_1221479 prefixEnd_1221479 92919383166419509851115 := by
  unfold tailWord_1221479
  simp only [CollatzResearch.WordTrace]
  refine ⟨44550999141797669849859491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29700666094531779899906327 44550999141797669849859491)
  ·
    refine ⟨66826498712696504774789237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44550999141797669849859491 66826498712696504774789237)
    ·
      refine ⟨6264984254315297322636491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66826498712696504774789237 6264984254315297322636491)
      ·
        refine ⟨9397476381472945983954737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6264984254315297322636491 9397476381472945983954737)
        ·
          refine ⟨7048107286104709487966053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9397476381472945983954737 7048107286104709487966053)
          ·
            refine ⟨1321520116144633028993635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7048107286104709487966053 1321520116144633028993635)
            ·
              refine ⟨1982280174216949543490453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321520116144633028993635 1982280174216949543490453)
              ·
                refine ⟨92919383166419509851115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1982280174216949543490453 92919383166419509851115)
                ·
                  rfl

theorem cell21_1221479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 6].length) (baseStart_1221479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221479 prefixEnd_1221479 := by exact prefixLift 1221479
  have htrace : WordTrace (prefixWord ++ tailWord_1221479) baseStart_1221479 baseEnd_1221479 := by
    simpa [prefixWord, tailWord_1221479, baseEnd_1221479] using wordTrace_append hprefix tailTrace_1221479
  have hstable : (prefixWord ++ tailWord_1221479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221479).length < 2 ^ (prefixWord ++ tailWord_1221479).sum := by decide
  have hdescent : baseEnd_1221479 < baseStart_1221479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221493 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 7]
def baseStart_1221493 : Nat := 118140960795 + 1221493 * 2 ^ 59
def prefixEnd_1221493 : Nat := 4983230072969 + 3 ^ 40 * 1221493 * 2
def baseEnd_1221493 : Nat := 278761344489997616319983

theorem tailTrace_1221493 : CollatzResearch.WordTrace tailWord_1221493 prefixEnd_1221493 278761344489997616319983 := by
  unfold tailWord_1221493
  simp only [CollatzResearch.WordTrace]
  refine ⟨44551509763746950240869133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29701006509164633493912755 44551509763746950240869133)
  ·
    refine ⟨16706816161405106340325925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44551509763746950240869133 16706816161405106340325925)
    ·
      refine ⟨3132528030263457438811111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16706816161405106340325925 3132528030263457438811111)
      ·
        refine ⟨4698792045395186158216667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3132528030263457438811111 4698792045395186158216667)
        ·
          refine ⟨7048188068092779237325001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4698792045395186158216667 7048188068092779237325001)
          ·
            refine ⟨5286141051069584427993751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7048188068092779237325001 5286141051069584427993751)
            ·
              refine ⟨7929211576604376641990627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5286141051069584427993751 7929211576604376641990627)
              ·
                refine ⟨11893817364906564962985941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7929211576604376641990627 11893817364906564962985941)
                ·
                  refine ⟨278761344489997616319983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11893817364906564962985941 278761344489997616319983)
                  ·
                    rfl

theorem cell21_1221493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_1221493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221493 prefixEnd_1221493 := by exact prefixLift 1221493
  have htrace : WordTrace (prefixWord ++ tailWord_1221493) baseStart_1221493 baseEnd_1221493 := by
    simpa [prefixWord, tailWord_1221493, baseEnd_1221493] using wordTrace_append hprefix tailTrace_1221493
  have hstable : (prefixWord ++ tailWord_1221493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221493).length < 2 ^ (prefixWord ++ tailWord_1221493).sum := by decide
  have hdescent : baseEnd_1221493 < baseStart_1221493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221507 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 6]
def baseStart_1221507 : Nat := 118140960795 + 1221507 * 2 ^ 59
def prefixEnd_1221507 : Nat := 4983230072969 + 3 ^ 40 * 1221507 * 2
def baseEnd_1221507 : Nat := 278764539480736703086621

theorem tailTrace_1221507 : CollatzResearch.WordTrace tailWord_1221507 prefixEnd_1221507 278764539480736703086621 := by
  unfold tailWord_1221507
  simp only [CollatzResearch.WordTrace]
  refine ⟨44552020385696230631878775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29701346923797487087919183 44552020385696230631878775)
  ·
    refine ⟨66828030578544345947818163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44552020385696230631878775 66828030578544345947818163)
    ·
      refine ⟨100242045867816518921727245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66828030578544345947818163 100242045867816518921727245)
      ·
        refine ⟨37590767200431194595647717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100242045867816518921727245 37590767200431194595647717)
        ·
          refine ⟨7048268850080848986683947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37590767200431194595647717 7048268850080848986683947)
          ·
            refine ⟨10572403275121273480025921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7048268850080848986683947 10572403275121273480025921)
            ·
              refine ⟨7929302456340955110019441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10572403275121273480025921 7929302456340955110019441)
              ·
                refine ⟨5946976842255716332514581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7929302456340955110019441 5946976842255716332514581)
                ·
                  refine ⟨278764539480736703086621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5946976842255716332514581 278764539480736703086621)
                  ·
                    rfl

theorem cell21_1221507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_1221507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221507 prefixEnd_1221507 := by exact prefixLift 1221507
  have htrace : WordTrace (prefixWord ++ tailWord_1221507) baseStart_1221507 baseEnd_1221507 := by
    simpa [prefixWord, tailWord_1221507, baseEnd_1221507] using wordTrace_append hprefix tailTrace_1221507
  have hstable : (prefixWord ++ tailWord_1221507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221507).length < 2 ^ (prefixWord ++ tailWord_1221507).sum := by decide
  have hdescent : baseEnd_1221507 < baseStart_1221507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221524 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1221524 : Nat := 118140960795 + 1221524 * 2 ^ 59
def prefixEnd_1221524 : Nat := 4983230072969 + 3 ^ 40 * 1221524 * 2
def baseEnd_1221524 : Nat := 278768419112348451303253

theorem tailTrace_1221524 : CollatzResearch.WordTrace tailWord_1221524 prefixEnd_1221524 278768419112348451303253 := by
  unfold tailWord_1221524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22276320213317321267623813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29701760284423095023498417 22276320213317321267623813)
  ·
    refine ⟨4176810039996997737679465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22276320213317321267623813 4176810039996997737679465)
    ·
      refine ⟨3132607529997748303259599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4176810039996997737679465 3132607529997748303259599)
      ·
        refine ⟨4698911294996622454889399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3132607529997748303259599 4698911294996622454889399)
        ·
          refine ⟨7048366942494933682334099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4698911294996622454889399 7048366942494933682334099)
          ·
            refine ⟨10572550413742400523501149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7048366942494933682334099 10572550413742400523501149)
            ·
              refine ⟨3964706405153400196312931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10572550413742400523501149 3964706405153400196312931)
              ·
                refine ⟨5947059607730100294469397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964706405153400196312931 5947059607730100294469397)
                ·
                  refine ⟨278768419112348451303253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5947059607730100294469397 278768419112348451303253)
                  ·
                    rfl

theorem cell21_1221524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1221524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221524 prefixEnd_1221524 := by exact prefixLift 1221524
  have htrace : WordTrace (prefixWord ++ tailWord_1221524) baseStart_1221524 baseEnd_1221524 := by
    simpa [prefixWord, tailWord_1221524, baseEnd_1221524] using wordTrace_append hprefix tailTrace_1221524
  have hstable : (prefixWord ++ tailWord_1221524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221524).length < 2 ^ (prefixWord ++ tailWord_1221524).sum := by decide
  have hdescent : baseEnd_1221524 < baseStart_1221524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221572 : List Nat := [2, 3, 3, 3, 1, 2, 7]
def baseStart_1221572 : Nat := 118140960795 + 1221572 * 2 ^ 59
def prefixEnd_1221572 : Nat := 4983230072969 + 3 ^ 40 * 1221572 * 2
def baseEnd_1221572 : Nat := 30975485929590114944795

theorem tailTrace_1221572 : CollatzResearch.WordTrace tailWord_1221572 prefixEnd_1221572 30975485929590114944795 := by
  unfold tailWord_1221572
  simp only [CollatzResearch.WordTrace]
  refine ⟨22277195565230373366497485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29702927420307164488663313 22277195565230373366497485)
  ·
    refine ⟨8353948336961390012436557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22277195565230373366497485 8353948336961390012436557)
    ·
      refine ⟨3132730626360521254663709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8353948336961390012436557 3132730626360521254663709)
      ·
        refine ⟨1174773984885195470498891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3132730626360521254663709 1174773984885195470498891)
        ·
          refine ⟨1762160977327793205748337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174773984885195470498891 1762160977327793205748337)
          ·
            refine ⟨1321620732995844904311253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1762160977327793205748337 1321620732995844904311253)
            ·
              refine ⟨30975485929590114944795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1321620732995844904311253 30975485929590114944795)
              ·
                rfl

theorem cell21_1221572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 7].length) (baseStart_1221572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221572 prefixEnd_1221572 := by exact prefixLift 1221572
  have htrace : WordTrace (prefixWord ++ tailWord_1221572) baseStart_1221572 baseEnd_1221572 := by
    simpa [prefixWord, tailWord_1221572, baseEnd_1221572] using wordTrace_append hprefix tailTrace_1221572
  have hstable : (prefixWord ++ tailWord_1221572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221572).length < 2 ^ (prefixWord ++ tailWord_1221572).sum := by decide
  have hdescent : baseEnd_1221572 < baseStart_1221572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221583 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 6]
def baseStart_1221583 : Nat := 118140960795 + 1221583 * 2 ^ 59
def prefixEnd_1221583 : Nat := 4983230072969 + 3 ^ 40 * 1221583 * 2
def baseEnd_1221583 : Nat := 278781883716177459819799

theorem tailTrace_1221583 : CollatzResearch.WordTrace tailWord_1221583 prefixEnd_1221583 278781883716177459819799 := by
  unfold tailWord_1221583
  simp only [CollatzResearch.WordTrace]
  refine ⟨44554792333420895611645403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29703194888947263741096935 44554792333420895611645403)
  ·
    refine ⟨66832188500131343417468105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44554792333420895611645403 66832188500131343417468105)
    ·
      refine ⟨50124141375098507563101079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66832188500131343417468105 50124141375098507563101079)
      ·
        refine ⟨75186212062647761344651619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50124141375098507563101079 75186212062647761344651619)
        ·
          refine ⟨112779318093971642016977429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75186212062647761344651619 112779318093971642016977429)
          ·
            refine ⟨5286530535654920719545817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 112779318093971642016977429 5286530535654920719545817)
            ·
              refine ⟨3964897901741190539659363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5286530535654920719545817 3964897901741190539659363)
              ·
                refine ⟨5947346852611785809489045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3964897901741190539659363 5947346852611785809489045)
                ·
                  refine ⟨278781883716177459819799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5947346852611785809489045 278781883716177459819799)
                  ·
                    rfl

theorem cell21_1221583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_1221583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221583 prefixEnd_1221583 := by exact prefixLift 1221583
  have htrace : WordTrace (prefixWord ++ tailWord_1221583) baseStart_1221583 baseEnd_1221583 := by
    simpa [prefixWord, tailWord_1221583, baseEnd_1221583] using wordTrace_append hprefix tailTrace_1221583
  have hstable : (prefixWord ++ tailWord_1221583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221583).length < 2 ^ (prefixWord ++ tailWord_1221583).sum := by decide
  have hdescent : baseEnd_1221583 < baseStart_1221583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221586 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 5]
def baseStart_1221586 : Nat := 118140960795 + 1221586 * 2 ^ 59
def prefixEnd_1221586 : Nat := 4983230072969 + 3 ^ 40 * 1221586 * 2
def baseEnd_1221586 : Nat := 278782568357050121269793

theorem tailTrace_1221586 : CollatzResearch.WordTrace tailWord_1221586 prefixEnd_1221586 278782568357050121269793 := by
  unfold tailWord_1221586
  simp only [CollatzResearch.WordTrace]
  refine ⟨11138725438102506781001153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29703267834940018082669741 11138725438102506781001153)
  ·
    refine ⟨8354044078576880085750865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11138725438102506781001153 8354044078576880085750865)
    ·
      refine ⟨6265533058932660064313149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8354044078576880085750865 6265533058932660064313149)
      ·
        refine ⟨2349574897099747524117431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6265533058932660064313149 2349574897099747524117431)
        ·
          refine ⟨3524362345649621286176147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2349574897099747524117431 3524362345649621286176147)
          ·
            refine ⟨5286543518474431929264221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3524362345649621286176147 5286543518474431929264221)
            ·
              refine ⟨1982453819427911973474083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5286543518474431929264221 1982453819427911973474083)
              ·
                refine ⟨2973680729141867960211125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1982453819427911973474083 2973680729141867960211125)
                ·
                  refine ⟨278782568357050121269793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2973680729141867960211125 278782568357050121269793)
                  ·
                    rfl

theorem cell21_1221586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_1221586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221586 prefixEnd_1221586 := by exact prefixLift 1221586
  have htrace : WordTrace (prefixWord ++ tailWord_1221586) baseStart_1221586 baseEnd_1221586 := by
    simpa [prefixWord, tailWord_1221586, baseEnd_1221586] using wordTrace_append hprefix tailTrace_1221586
  have hstable : (prefixWord ++ tailWord_1221586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221586).length < 2 ^ (prefixWord ++ tailWord_1221586).sum := by decide
  have hdescent : baseEnd_1221586 < baseStart_1221586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221693 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 4]
def baseStart_1221693 : Nat := 118140960795 + 1221693 * 2 ^ 59
def prefixEnd_1221693 : Nat := 4983230072969 + 3 ^ 40 * 1221693 * 2
def baseEnd_1221693 : Nat := 278806987214841712986241

theorem tailTrace_1221693 : CollatzResearch.WordTrace tailWord_1221693 prefixEnd_1221693 278806987214841712986241 := by
  unfold tailWord_1221693
  simp only [CollatzResearch.WordTrace]
  refine ⟨44558804363022384398149733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29705869575348256265433155 44558804363022384398149733)
  ·
    refine ⟨8354775818066697074653075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44558804363022384398149733 8354775818066697074653075)
    ·
      refine ⟨12532163727100045611979613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8354775818066697074653075 12532163727100045611979613)
      ·
        refine ⟨4699561397662517104492355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12532163727100045611979613 4699561397662517104492355)
        ·
          refine ⟨7049342096493775656738533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4699561397662517104492355 7049342096493775656738533)
          ·
            refine ⟨1321751643092582935638475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7049342096493775656738533 1321751643092582935638475)
            ·
              refine ⟨1982627464638874403457713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321751643092582935638475 1982627464638874403457713)
              ·
                refine ⟨1486970598479155802593285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1982627464638874403457713 1486970598479155802593285)
                ·
                  refine ⟨278806987214841712986241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1486970598479155802593285 278806987214841712986241)
                  ·
                    rfl

theorem cell21_1221693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_1221693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221693 prefixEnd_1221693 := by exact prefixLift 1221693
  have htrace : WordTrace (prefixWord ++ tailWord_1221693) baseStart_1221693 baseEnd_1221693 := by
    simpa [prefixWord, tailWord_1221693, baseEnd_1221693] using wordTrace_append hprefix tailTrace_1221693
  have hstable : (prefixWord ++ tailWord_1221693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221693).length < 2 ^ (prefixWord ++ tailWord_1221693).sum := by decide
  have hdescent : baseEnd_1221693 < baseStart_1221693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221735 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 6]
def baseStart_1221735 : Nat := 118140960795 + 1221735 * 2 ^ 59
def prefixEnd_1221735 : Nat := 4983230072969 + 3 ^ 40 * 1221735 * 2
def baseEnd_1221735 : Nat := 278816572187058973286155

theorem tailTrace_1221735 : CollatzResearch.WordTrace tailWord_1221735 prefixEnd_1221735 278816572187058973286155 := by
  unfold tailWord_1221735
  simp only [CollatzResearch.WordTrace]
  refine ⟨44560336228870225571178659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29706890819246817047452439 44560336228870225571178659)
  ·
    refine ⟨66840504343305338356767989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44560336228870225571178659 66840504343305338356767989)
    ·
      refine ⟨6266297282184875470946999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66840504343305338356767989 6266297282184875470946999)
      ·
        refine ⟨9399445923277313206420499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6266297282184875470946999 9399445923277313206420499)
        ·
          refine ⟨14099168884915969809630749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9399445923277313206420499 14099168884915969809630749)
          ·
            refine ⟨5287188331843488678611531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14099168884915969809630749 5287188331843488678611531)
            ·
              refine ⟨7930782497765233017917297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5287188331843488678611531 7930782497765233017917297)
              ·
                refine ⟨5948086873323924763437973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7930782497765233017917297 5948086873323924763437973)
                ·
                  refine ⟨278816572187058973286155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5948086873323924763437973 278816572187058973286155)
                  ·
                    rfl

theorem cell21_1221735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_1221735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221735 prefixEnd_1221735 := by exact prefixLift 1221735
  have htrace : WordTrace (prefixWord ++ tailWord_1221735) baseStart_1221735 baseEnd_1221735 := by
    simpa [prefixWord, tailWord_1221735, baseEnd_1221735] using wordTrace_append hprefix tailTrace_1221735
  have hstable : (prefixWord ++ tailWord_1221735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221735).length < 2 ^ (prefixWord ++ tailWord_1221735).sum := by decide
  have hdescent : baseEnd_1221735 < baseStart_1221735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221769 : List Nat := [1, 2, 1, 1, 4, 5, 2, 1, 4]
def baseStart_1221769 : Nat := 118140960795 + 1221769 * 2 ^ 59
def prefixEnd_1221769 : Nat := 4983230072969 + 3 ^ 40 * 1221769 * 2
def baseEnd_1221769 : Nat := 278824331450282469719419

theorem tailTrace_1221769 : CollatzResearch.WordTrace tailWord_1221769 prefixEnd_1221769 278824331450282469719419 := by
  unfold tailWord_1221769
  simp only [CollatzResearch.WordTrace]
  refine ⟨44561576310747049377916361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29707717540498032918610907 44561576310747049377916361)
  ·
    refine ⟨33421182233060287033437271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44561576310747049377916361 33421182233060287033437271)
    ·
      refine ⟨50131773349590430550155907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33421182233060287033437271 50131773349590430550155907)
      ·
        refine ⟨75197660024385645825233861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50131773349590430550155907 75197660024385645825233861)
        ·
          refine ⟨14099561254572308592231349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75197660024385645825233861 14099561254572308592231349)
          ·
            refine ⟨1321833867616153930521689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14099561254572308592231349 1321833867616153930521689)
            ·
              refine ⟨991375400712115447891267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1321833867616153930521689 991375400712115447891267)
              ·
                refine ⟨1487063101068173171836901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991375400712115447891267 1487063101068173171836901)
                ·
                  refine ⟨278824331450282469719419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487063101068173171836901 278824331450282469719419)
                  ·
                    rfl

theorem cell21_1221769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_1221769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221769 prefixEnd_1221769 := by exact prefixLift 1221769
  have htrace : WordTrace (prefixWord ++ tailWord_1221769) baseStart_1221769 baseEnd_1221769 := by
    simpa [prefixWord, tailWord_1221769, baseEnd_1221769] using wordTrace_append hprefix tailTrace_1221769
  have hstable : (prefixWord ++ tailWord_1221769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221769).length < 2 ^ (prefixWord ++ tailWord_1221769).sum := by decide
  have hdescent : baseEnd_1221769 < baseStart_1221769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1221811 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 4]
def baseStart_1221811 : Nat := 118140960795 + 1221811 * 2 ^ 59
def prefixEnd_1221811 : Nat := 4983230072969 + 3 ^ 40 * 1221811 * 2
def baseEnd_1221811 : Nat := 278833916422499730019333

theorem tailTrace_1221811 : CollatzResearch.WordTrace tailWord_1221811 prefixEnd_1221811 278833916422499730019333 := by
  unfold tailWord_1221811
  simp only [CollatzResearch.WordTrace]
  refine ⟨44563108176594890550945287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29708738784396593700630191 44563108176594890550945287)
  ·
    refine ⟨66844662264892335826417931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44563108176594890550945287 66844662264892335826417931)
    ·
      refine ⟨100266993397338503739626897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66844662264892335826417931 100266993397338503739626897)
      ·
        refine ⟨75200245048003877804720173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100266993397338503739626897 75200245048003877804720173)
        ·
          refine ⟨28200091893001454176770065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75200245048003877804720173 28200091893001454176770065)
          ·
            refine ⟨21150068919751090632577549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28200091893001454176770065 21150068919751090632577549)
            ·
              refine ⟨7931275844906658987216581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21150068919751090632577549 7931275844906658987216581)
              ·
                refine ⟨1487114220919998560103109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7931275844906658987216581 1487114220919998560103109)
                ·
                  refine ⟨278833916422499730019333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487114220919998560103109 278833916422499730019333)
                  ·
                    rfl

theorem cell21_1221811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 4].length) (baseStart_1221811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1221811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1221811 prefixEnd_1221811 := by exact prefixLift 1221811
  have htrace : WordTrace (prefixWord ++ tailWord_1221811) baseStart_1221811 baseEnd_1221811 := by
    simpa [prefixWord, tailWord_1221811, baseEnd_1221811] using wordTrace_append hprefix tailTrace_1221811
  have hstable : (prefixWord ++ tailWord_1221811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1221811).length < 2 ^ (prefixWord ++ tailWord_1221811).sum := by decide
  have hdescent : baseEnd_1221811 < baseStart_1221811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1221811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222076 : List Nat := [2, 2, 2, 4, 3, 1, 1, 3, 3]
def baseStart_1222076 : Nat := 118140960795 + 1222076 * 2 ^ 59
def prefixEnd_1222076 : Nat := 4983230072969 + 3 ^ 40 * 1222076 * 2
def baseEnd_1222076 : Nat := 278894393032918158102125

theorem tailTrace_1222076 : CollatzResearch.WordTrace tailWord_1222076 prefixEnd_1222076 278894393032918158102125 := by
  unfold tailWord_1222076
  simp only [CollatzResearch.WordTrace]
  refine ⟨22286386760317420404671041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29715182347089893872894721 22286386760317420404671041)
  ·
    refine ⟨16714790070238065303503281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22286386760317420404671041 16714790070238065303503281)
    ·
      refine ⟨12536092552678548977627461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16714790070238065303503281 12536092552678548977627461)
      ·
        refine ⟨2350517353627227933305149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12536092552678548977627461 2350517353627227933305149)
        ·
          refine ⟨881444007610210474989431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2350517353627227933305149 881444007610210474989431)
          ·
            refine ⟨1322166011415315712484147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881444007610210474989431 1322166011415315712484147)
            ·
              refine ⟨1983249017122973568726221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322166011415315712484147 1983249017122973568726221)
              ·
                refine ⟨743718381421115088272333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1983249017122973568726221 743718381421115088272333)
                ·
                  refine ⟨278894393032918158102125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743718381421115088272333 278894393032918158102125)
                  ·
                    rfl

theorem cell21_1222076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_1222076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222076 prefixEnd_1222076 := by exact prefixLift 1222076
  have htrace : WordTrace (prefixWord ++ tailWord_1222076) baseStart_1222076 baseEnd_1222076 := by
    simpa [prefixWord, tailWord_1222076, baseEnd_1222076] using wordTrace_append hprefix tailTrace_1222076
  have hstable : (prefixWord ++ tailWord_1222076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222076).length < 2 ^ (prefixWord ++ tailWord_1222076).sum := by decide
  have hdescent : baseEnd_1222076 < baseStart_1222076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222129 : List Nat := [1, 2, 2, 2, 3, 2, 2, 7]
def baseStart_1222129 : Nat := 118140960795 + 1222129 * 2 ^ 59
def prefixEnd_1222129 : Nat := 4983230072969 + 3 ^ 40 * 1222129 * 2
def baseEnd_1222129 : Nat := 92968829451667281239561

theorem tailTrace_1222129 : CollatzResearch.WordTrace tailWord_1222129 prefixEnd_1222129 92968829451667281239561 := by
  unfold tailWord_1222129
  simp only [CollatzResearch.WordTrace]
  refine ⟨44574706589442830861021441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29716471059628553907347627 44574706589442830861021441)
  ·
    refine ⟨33431029942082123145766081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44574706589442830861021441 33431029942082123145766081)
    ·
      refine ⟨25073272456561592359324561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33431029942082123145766081 25073272456561592359324561)
      ·
        refine ⟨18804954342421194269493421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25073272456561592359324561 18804954342421194269493421)
        ·
          refine ⟨7051857878407947851060033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18804954342421194269493421 7051857878407947851060033)
          ·
            refine ⟨5288893408805960888295025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7051857878407947851060033 5288893408805960888295025)
            ·
              refine ⟨3966670056604470666221269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5288893408805960888295025 3966670056604470666221269)
              ·
                refine ⟨92968829451667281239561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3966670056604470666221269 92968829451667281239561)
                ·
                  rfl

theorem cell21_1222129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 7].length) (baseStart_1222129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222129 prefixEnd_1222129 := by exact prefixLift 1222129
  have htrace : WordTrace (prefixWord ++ tailWord_1222129) baseStart_1222129 baseEnd_1222129 := by
    simpa [prefixWord, tailWord_1222129, baseEnd_1222129] using wordTrace_append hprefix tailTrace_1222129
  have hstable : (prefixWord ++ tailWord_1222129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222129).length < 2 ^ (prefixWord ++ tailWord_1222129).sum := by decide
  have hdescent : baseEnd_1222129 < baseStart_1222129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222143 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 9]
def baseStart_1222143 : Nat := 118140960795 + 1222143 * 2 ^ 59
def prefixEnd_1222143 : Nat := 4983230072969 + 3 ^ 40 * 1222143 * 2
def baseEnd_1222143 : Nat := 278909683345740930485321

theorem tailTrace_1222143 : CollatzResearch.WordTrace tailWord_1222143 prefixEnd_1222143 278909683345740930485321 := by
  unfold tailWord_1222143
  simp only [CollatzResearch.WordTrace]
  refine ⟨44575217211392111252031083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29716811474261407501354055 44575217211392111252031083)
  ·
    refine ⟨66862825817088166878046625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44575217211392111252031083 66862825817088166878046625)
    ·
      refine ⟨50147119362816125158534969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66862825817088166878046625 50147119362816125158534969)
      ·
        refine ⟨37610339522112093868901227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50147119362816125158534969 37610339522112093868901227)
        ·
          refine ⟨56415509283168140803351841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37610339522112093868901227 56415509283168140803351841)
          ·
            refine ⟨42311631962376105602513881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56415509283168140803351841 42311631962376105602513881)
            ·
              refine ⟨31733723971782079201885411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42311631962376105602513881 31733723971782079201885411)
              ·
                refine ⟨47600585957673118802828117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31733723971782079201885411 47600585957673118802828117)
                ·
                  refine ⟨278909683345740930485321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47600585957673118802828117 278909683345740930485321)
                  ·
                    rfl

theorem cell21_1222143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_1222143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222143 prefixEnd_1222143 := by exact prefixLift 1222143
  have htrace : WordTrace (prefixWord ++ tailWord_1222143) baseStart_1222143 baseEnd_1222143 := by
    simpa [prefixWord, tailWord_1222143, baseEnd_1222143] using wordTrace_append hprefix tailTrace_1222143
  have hstable : (prefixWord ++ tailWord_1222143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222143).length < 2 ^ (prefixWord ++ tailWord_1222143).sum := by decide
  have hdescent : baseEnd_1222143 < baseStart_1222143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222146 : List Nat := [3, 4, 1, 2, 1, 10]
def baseStart_1222146 : Nat := 118140960795 + 1222146 * 2 ^ 59
def prefixEnd_1222146 : Nat := 4983230072969 + 3 ^ 40 * 1222146 * 2
def baseEnd_1222146 : Nat := 10330013629133836738345

theorem tailTrace_1222146 : CollatzResearch.WordTrace tailWord_1222146 prefixEnd_1222146 10330013629133836738345 := by
  unfold tailWord_1222146
  simp only [CollatzResearch.WordTrace]
  refine ⟨11143831657595310691097573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29716884420254161842926861 11143831657595310691097573)
  ·
    refine ⟨2089468435799120754580795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11143831657595310691097573 2089468435799120754580795)
    ·
      refine ⟨3134202653698681131871193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2089468435799120754580795 3134202653698681131871193)
      ·
        refine ⟨2350651990274010848903395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3134202653698681131871193 2350651990274010848903395)
        ·
          refine ⟨3525977985411016273355093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350651990274010848903395 3525977985411016273355093)
          ·
            refine ⟨10330013629133836738345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3525977985411016273355093 10330013629133836738345)
            ·
              rfl

theorem cell21_1222146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 10].length) (baseStart_1222146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222146 prefixEnd_1222146 := by exact prefixLift 1222146
  have htrace : WordTrace (prefixWord ++ tailWord_1222146) baseStart_1222146 baseEnd_1222146 := by
    simpa [prefixWord, tailWord_1222146, baseEnd_1222146] using wordTrace_append hprefix tailTrace_1222146
  have hstable : (prefixWord ++ tailWord_1222146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222146).length < 2 ^ (prefixWord ++ tailWord_1222146).sum := by decide
  have hdescent : baseEnd_1222146 < baseStart_1222146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222433 : List Nat := [1, 2, 3, 2, 1, 5, 7]
def baseStart_1222433 : Nat := 118140960795 + 1222433 * 2 ^ 59
def prefixEnd_1222433 : Nat := 4983230072969 + 3 ^ 40 * 1222433 * 2
def baseEnd_1222433 : Nat := 30997318366307207850155

theorem tailTrace_1222433 : CollatzResearch.WordTrace tailWord_1222433 prefixEnd_1222433 30997318366307207850155 := by
  unfold tailWord_1222433
  simp only [CollatzResearch.WordTrace]
  refine ⟨44585794380341490780087953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29723862920227660520058635 44585794380341490780087953)
  ·
    refine ⟨33439345785256118085065965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44585794380341490780087953 33439345785256118085065965)
    ·
      refine ⟨12539754669471044281899737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33439345785256118085065965 12539754669471044281899737)
      ·
        refine ⟨9404816002103283211424803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12539754669471044281899737 9404816002103283211424803)
        ·
          refine ⟨14107224003154924817137205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9404816002103283211424803 14107224003154924817137205)
          ·
            refine ⟨1322552250295774201606613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14107224003154924817137205 1322552250295774201606613)
            ·
              refine ⟨30997318366307207850155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1322552250295774201606613 30997318366307207850155)
              ·
                rfl

theorem cell21_1222433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 7].length) (baseStart_1222433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222433 prefixEnd_1222433 := by exact prefixLift 1222433
  have htrace : WordTrace (prefixWord ++ tailWord_1222433) baseStart_1222433 baseEnd_1222433 := by
    simpa [prefixWord, tailWord_1222433, baseEnd_1222433] using wordTrace_append hprefix tailTrace_1222433
  have hstable : (prefixWord ++ tailWord_1222433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222433).length < 2 ^ (prefixWord ++ tailWord_1222433).sum := by decide
  have hdescent : baseEnd_1222433 < baseStart_1222433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222453 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 4]
def baseStart_1222453 : Nat := 118140960795 + 1222453 * 2 ^ 59
def prefixEnd_1222453 : Nat := 4983230072969 + 3 ^ 40 * 1222453 * 2
def baseEnd_1222453 : Nat := 278980429569249280318021

theorem tailTrace_1222453 : CollatzResearch.WordTrace tailWord_1222453 prefixEnd_1222453 278980429569249280318021 := by
  unfold tailWord_1222453
  simp only [CollatzResearch.WordTrace]
  refine ⟨44586523840269034195816013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29724349226846022797210675 44586523840269034195816013)
  ·
    refine ⟨16719946440100887823431005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44586523840269034195816013 16719946440100887823431005)
    ·
      refine ⟨6269979915037832933786627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16719946440100887823431005 6269979915037832933786627)
      ·
        refine ⟨9404969872556749400679941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6269979915037832933786627 9404969872556749400679941)
        ·
          refine ⟨1763431851104390512627489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9404969872556749400679941 1763431851104390512627489)
          ·
            refine ⟨1322573888328292884470617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1763431851104390512627489 1322573888328292884470617)
            ·
              refine ⟨991930416246219663352963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1322573888328292884470617 991930416246219663352963)
              ·
                refine ⟨1487895624369329495029445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991930416246219663352963 1487895624369329495029445)
                ·
                  refine ⟨278980429569249280318021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487895624369329495029445 278980429569249280318021)
                  ·
                    rfl

theorem cell21_1222453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_1222453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222453 prefixEnd_1222453 := by exact prefixLift 1222453
  have htrace : WordTrace (prefixWord ++ tailWord_1222453) baseStart_1222453 baseEnd_1222453 := by
    simpa [prefixWord, tailWord_1222453, baseEnd_1222453] using wordTrace_append hprefix tailTrace_1222453
  have hstable : (prefixWord ++ tailWord_1222453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222453).length < 2 ^ (prefixWord ++ tailWord_1222453).sum := by decide
  have hdescent : baseEnd_1222453 < baseStart_1222453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222495 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 4]
def baseStart_1222495 : Nat := 118140960795 + 1222495 * 2 ^ 59
def prefixEnd_1222495 : Nat := 4983230072969 + 3 ^ 40 * 1222495 * 2
def baseEnd_1222495 : Nat := 278990014541466540617935

theorem tailTrace_1222495 : CollatzResearch.WordTrace tailWord_1222495 prefixEnd_1222495 278990014541466540617935 := by
  unfold tailWord_1222495
  simp only [CollatzResearch.WordTrace]
  refine ⟨44588055706116875368844939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29725370470744583579229959 44588055706116875368844939)
  ·
    refine ⟨66882083559175313053267409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44588055706116875368844939 66882083559175313053267409)
    ·
      refine ⟨50161562669381484789950557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66882083559175313053267409 50161562669381484789950557)
      ·
        refine ⟨18810586001018056796231459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50161562669381484789950557 18810586001018056796231459)
        ·
          refine ⟨28215879001527085194347189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18810586001018056796231459 28215879001527085194347189)
          ·
            refine ⟨2645238656393164236970049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28215879001527085194347189 2645238656393164236970049)
            ·
              refine ⟨1983928992294873177727537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2645238656393164236970049 1983928992294873177727537)
              ·
                refine ⟨1487946744221154883295653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1983928992294873177727537 1487946744221154883295653)
                ·
                  refine ⟨278990014541466540617935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1487946744221154883295653 278990014541466540617935)
                  ·
                    rfl

theorem cell21_1222495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 4].length) (baseStart_1222495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222495 prefixEnd_1222495 := by exact prefixLift 1222495
  have htrace : WordTrace (prefixWord ++ tailWord_1222495) baseStart_1222495 baseEnd_1222495 := by
    simpa [prefixWord, tailWord_1222495, baseEnd_1222495] using wordTrace_append hprefix tailTrace_1222495
  have hstable : (prefixWord ++ tailWord_1222495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222495).length < 2 ^ (prefixWord ++ tailWord_1222495).sum := by decide
  have hdescent : baseEnd_1222495 < baseStart_1222495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222498 : List Nat := [3, 3, 2, 1, 2, 2, 1, 4, 3]
def baseStart_1222498 : Nat := 118140960795 + 1222498 * 2 ^ 59
def prefixEnd_1222498 : Nat := 4983230072969 + 3 ^ 40 * 1222498 * 2
def baseEnd_1222498 : Nat := 278990699182339202067929

theorem tailTrace_1222498 : CollatzResearch.WordTrace tailWord_1222498 prefixEnd_1222498 278990699182339202067929 := by
  unfold tailWord_1222498
  simp only [CollatzResearch.WordTrace]
  refine ⟨11147041281276501720301037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29725443416737337920802765 11147041281276501720301037)
  ·
    refine ⟨4180140480478688145112889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11147041281276501720301037 4180140480478688145112889)
    ·
      refine ⟨3135105360359016108834667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4180140480478688145112889 3135105360359016108834667)
      ·
        refine ⟨4702658040538524163252001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3135105360359016108834667 4702658040538524163252001)
        ·
          refine ⟨3526993530403893122439001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4702658040538524163252001 3526993530403893122439001)
          ·
            refine ⟨2645245147802919841829251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3526993530403893122439001 2645245147802919841829251)
            ·
              refine ⟨3967867721704379762743877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645245147802919841829251 3967867721704379762743877)
              ·
                refine ⟨743975197819571205514477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3967867721704379762743877 743975197819571205514477)
                ·
                  refine ⟨278990699182339202067929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743975197819571205514477 278990699182339202067929)
                  ·
                    rfl

theorem cell21_1222498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_1222498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222498 prefixEnd_1222498 := by exact prefixLift 1222498
  have htrace : WordTrace (prefixWord ++ tailWord_1222498) baseStart_1222498 baseEnd_1222498 := by
    simpa [prefixWord, tailWord_1222498, baseEnd_1222498] using wordTrace_append hprefix tailTrace_1222498
  have hstable : (prefixWord ++ tailWord_1222498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222498).length < 2 ^ (prefixWord ++ tailWord_1222498).sum := by decide
  have hdescent : baseEnd_1222498 < baseStart_1222498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222509 : List Nat := [1, 5, 1, 1, 1, 1, 5, 6]
def baseStart_1222509 : Nat := 118140960795 + 1222509 * 2 ^ 59
def prefixEnd_1222509 : Nat := 4983230072969 + 3 ^ 40 * 1222509 * 2
def baseEnd_1222509 : Nat := 92997736510735209128191

theorem tailTrace_1222509 : CollatzResearch.WordTrace tailWord_1222509 prefixEnd_1222509 92997736510735209128191 := by
  unfold tailWord_1222509
  simp only [CollatzResearch.WordTrace]
  refine ⟨44588566328066155759854581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29725710885377437173236387 44588566328066155759854581)
  ·
    refine ⟨4180178093256202102486367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44588566328066155759854581 4180178093256202102486367)
    ·
      refine ⟨6270267139884303153729551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4180178093256202102486367 6270267139884303153729551)
      ·
        refine ⟨9405400709826454730594327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6270267139884303153729551 9405400709826454730594327)
        ·
          refine ⟨14108101064739682095891491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9405400709826454730594327 14108101064739682095891491)
          ·
            refine ⟨21162151597109523143837237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14108101064739682095891491 21162151597109523143837237)
            ·
              refine ⟨1983951712229017794734741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21162151597109523143837237 1983951712229017794734741)
              ·
                refine ⟨92997736510735209128191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1983951712229017794734741 92997736510735209128191)
                ·
                  rfl

theorem cell21_1222509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 6].length) (baseStart_1222509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222509 prefixEnd_1222509 := by exact prefixLift 1222509
  have htrace : WordTrace (prefixWord ++ tailWord_1222509) baseStart_1222509 baseEnd_1222509 := by
    simpa [prefixWord, tailWord_1222509, baseEnd_1222509] using wordTrace_append hprefix tailTrace_1222509
  have hstable : (prefixWord ++ tailWord_1222509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222509).length < 2 ^ (prefixWord ++ tailWord_1222509).sum := by decide
  have hdescent : baseEnd_1222509 < baseStart_1222509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222557 : List Nat := [1, 4, 2, 1, 2, 2, 2, 4, 3]
def baseStart_1222557 : Nat := 118140960795 + 1222557 * 2 ^ 59
def prefixEnd_1222557 : Nat := 4983230072969 + 3 ^ 40 * 1222557 * 2
def baseEnd_1222557 : Nat := 279004163786168210584475

theorem tailTrace_1222557 : CollatzResearch.WordTrace tailWord_1222557 prefixEnd_1222557 279004163786168210584475 := by
  unfold tailWord_1222557
  simp only [CollatzResearch.WordTrace]
  refine ⟨44590317031892259957601925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29726878021261506638401283 44590317031892259957601925)
  ·
    refine ⟨8360684443479798742050361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44590317031892259957601925 8360684443479798742050361)
    ·
      refine ⟨6270513332609849056537771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8360684443479798742050361 6270513332609849056537771)
      ·
        refine ⟨9405769998914773584806657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6270513332609849056537771 9405769998914773584806657)
        ·
          refine ⟨7054327499186080188604993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9405769998914773584806657 7054327499186080188604993)
          ·
            refine ⟨5290745624389560141453745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7054327499186080188604993 5290745624389560141453745)
            ·
              refine ⟨3968059218292170106090309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5290745624389560141453745 3968059218292170106090309)
              ·
                refine ⟨744011103429781894891933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3968059218292170106090309 744011103429781894891933)
                ·
                  refine ⟨279004163786168210584475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744011103429781894891933 279004163786168210584475)
                  ·
                    rfl

theorem cell21_1222557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_1222557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222557 prefixEnd_1222557 := by exact prefixLift 1222557
  have htrace : WordTrace (prefixWord ++ tailWord_1222557) baseStart_1222557 baseEnd_1222557 := by
    simpa [prefixWord, tailWord_1222557, baseEnd_1222557] using wordTrace_append hprefix tailTrace_1222557
  have hstable : (prefixWord ++ tailWord_1222557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222557).length < 2 ^ (prefixWord ++ tailWord_1222557).sum := by decide
  have hdescent : baseEnd_1222557 < baseStart_1222557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222695 : List Nat := [1, 1, 7, 1, 2, 1, 3, 5]
def baseStart_1222695 : Nat := 118140960795 + 1222695 * 2 ^ 59
def prefixEnd_1222695 : Nat := 4983230072969 + 3 ^ 40 * 1222695 * 2
def baseEnd_1222695 : Nat := 93011885755436879094731

theorem tailTrace_1222695 : CollatzResearch.WordTrace tailWord_1222695 prefixEnd_1222695 93011885755436879094731 := by
  unfold tailWord_1222695
  simp only [CollatzResearch.WordTrace]
  refine ⟨44595350305392309526125539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29730233536928206350750359 44595350305392309526125539)
  ·
    refine ⟨66893025458088464289188309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44595350305392309526125539 66893025458088464289188309)
    ·
      refine ⟨1567805284173948381777851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 66893025458088464289188309 1567805284173948381777851)
      ·
        refine ⟨2351707926260922572666777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567805284173948381777851 2351707926260922572666777)
        ·
          refine ⟨1763780944695691929500083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351707926260922572666777 1763780944695691929500083)
          ·
            refine ⟨2645671417043537894250125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763780944695691929500083 2645671417043537894250125)
            ·
              refine ⟨992126781391326710343797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2645671417043537894250125 992126781391326710343797)
              ·
                refine ⟨93011885755436879094731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 992126781391326710343797 93011885755436879094731)
                ·
                  rfl

theorem cell21_1222695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 5].length) (baseStart_1222695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222695 prefixEnd_1222695 := by exact prefixLift 1222695
  have htrace : WordTrace (prefixWord ++ tailWord_1222695) baseStart_1222695 baseEnd_1222695 := by
    simpa [prefixWord, tailWord_1222695, baseEnd_1222695] using wordTrace_append hprefix tailTrace_1222695
  have hstable : (prefixWord ++ tailWord_1222695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222695).length < 2 ^ (prefixWord ++ tailWord_1222695).sum := by decide
  have hdescent : baseEnd_1222695 < baseStart_1222695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222720 : List Nat := [2, 1, 1, 2, 2, 5, 8]
def baseStart_1222720 : Nat := 118140960795 + 1222720 * 2 ^ 59
def prefixEnd_1222720 : Nat := 4983230072969 + 3 ^ 40 * 1222720 * 2
def baseEnd_1222720 : Nat := 31004595845212905485275

theorem tailTrace_1222720 : CollatzResearch.WordTrace tailWord_1222720 prefixEnd_1222720 31004595845212905485275 := by
  unfold tailWord_1222720
  simp only [CollatzResearch.WordTrace]
  refine ⟨22298131065150869397892807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29730841420201159197190409 22298131065150869397892807)
  ·
    refine ⟨33447196597726304096839211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22298131065150869397892807 33447196597726304096839211)
    ·
      refine ⟨50170794896589456145258817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33447196597726304096839211 50170794896589456145258817)
      ·
        refine ⟨37628096172442092108944113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50170794896589456145258817 37628096172442092108944113)
        ·
          refine ⟨28221072129331569081708085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37628096172442092108944113 28221072129331569081708085)
          ·
            refine ⟨2645725512124834601410133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28221072129331569081708085 2645725512124834601410133)
            ·
              refine ⟨31004595845212905485275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2645725512124834601410133 31004595845212905485275)
              ·
                rfl

theorem cell21_1222720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 8].length) (baseStart_1222720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222720 prefixEnd_1222720 := by exact prefixLift 1222720
  have htrace : WordTrace (prefixWord ++ tailWord_1222720) baseStart_1222720 baseEnd_1222720 := by
    simpa [prefixWord, tailWord_1222720, baseEnd_1222720] using wordTrace_append hprefix tailTrace_1222720
  have hstable : (prefixWord ++ tailWord_1222720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222720).length < 2 ^ (prefixWord ++ tailWord_1222720).sum := by decide
  have hdescent : baseEnd_1222720 < baseStart_1222720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222726 : List Nat := [6, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_1222726 : Nat := 118140960795 + 1222726 * 2 ^ 59
def prefixEnd_1222726 : Nat := 4983230072969 + 3 ^ 40 * 1222726 * 2
def baseEnd_1222726 : Nat := 279042731888661472267463

theorem tailTrace_1222726 : CollatzResearch.WordTrace tailWord_1222726 prefixEnd_1222726 279042731888661472267463 := by
  unfold tailWord_1222726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1393640030258750056890751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29730987312186667880336021 1393640030258750056890751)
  ·
    refine ⟨2090460045388125085336127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1393640030258750056890751 2090460045388125085336127)
    ·
      refine ⟨3135690068082187628004191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2090460045388125085336127 3135690068082187628004191)
      ·
        refine ⟨4703535102123281442006287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3135690068082187628004191 4703535102123281442006287)
        ·
          refine ⟨7055302653184922163009431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4703535102123281442006287 7055302653184922163009431)
          ·
            refine ⟨10582953979777383244514147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7055302653184922163009431 10582953979777383244514147)
            ·
              refine ⟨15874430969666074866771221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10582953979777383244514147 15874430969666074866771221)
              ·
                refine ⟨744113951703097259379901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15874430969666074866771221 744113951703097259379901)
                ·
                  refine ⟨279042731888661472267463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744113951703097259379901 279042731888661472267463)
                  ·
                    rfl

theorem cell21_1222726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_1222726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222726 prefixEnd_1222726 := by exact prefixLift 1222726
  have htrace : WordTrace (prefixWord ++ tailWord_1222726) baseStart_1222726 baseEnd_1222726 := by
    simpa [prefixWord, tailWord_1222726, baseEnd_1222726] using wordTrace_append hprefix tailTrace_1222726
  have hstable : (prefixWord ++ tailWord_1222726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222726).length < 2 ^ (prefixWord ++ tailWord_1222726).sum := by decide
  have hdescent : baseEnd_1222726 < baseStart_1222726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222754 : List Nat := [3, 3, 2, 2, 2, 1, 1, 7]
def baseStart_1222754 : Nat := 118140960795 + 1222754 * 2 ^ 59
def prefixEnd_1222754 : Nat := 4983230072969 + 3 ^ 40 * 1222754 * 2
def baseEnd_1222754 : Nat := 93016373956713215266913

theorem tailTrace_1222754 : CollatzResearch.WordTrace tailWord_1222754 prefixEnd_1222754 93016373956713215266913 := by
  unfold tailWord_1222754
  simp only [CollatzResearch.WordTrace]
  refine ⟨11149375553044640650630829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29731668141452375068348877 11149375553044640650630829)
  ·
    refine ⟨4181015832391740243986561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11149375553044640650630829 4181015832391740243986561)
    ·
      refine ⟨3135761874293805182989921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4181015832391740243986561 3135761874293805182989921)
      ·
        refine ⟨2351821405720353887242441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3135761874293805182989921 2351821405720353887242441)
        ·
          refine ⟨1763866054290265415431831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351821405720353887242441 1763866054290265415431831)
          ·
            refine ⟨2645799081435398123147747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763866054290265415431831 2645799081435398123147747)
            ·
              refine ⟨3968698622153097184721621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645799081435398123147747 3968698622153097184721621)
              ·
                refine ⟨93016373956713215266913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3968698622153097184721621 93016373956713215266913)
                ·
                  rfl

theorem cell21_1222754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_1222754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222754 prefixEnd_1222754 := by exact prefixLift 1222754
  have htrace : WordTrace (prefixWord ++ tailWord_1222754) baseStart_1222754 baseEnd_1222754 := by
    simpa [prefixWord, tailWord_1222754, baseEnd_1222754] using wordTrace_append hprefix tailTrace_1222754
  have hstable : (prefixWord ++ tailWord_1222754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222754).length < 2 ^ (prefixWord ++ tailWord_1222754).sum := by decide
  have hdescent : baseEnd_1222754 < baseStart_1222754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222785 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 5]
def baseStart_1222785 : Nat := 118140960795 + 1222785 * 2 ^ 59
def prefixEnd_1222785 : Nat := 4983230072969 + 3 ^ 40 * 1222785 * 2
def baseEnd_1222785 : Nat := 279056196492490480784009

theorem tailTrace_1222785 : CollatzResearch.WordTrace tailWord_1222785 prefixEnd_1222785 279056196492490480784009 := by
  unfold tailWord_1222785
  simp only [CollatzResearch.WordTrace]
  refine ⟨44598632875066254896901809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29732421916710836597934539 44598632875066254896901809)
  ·
    refine ⟨33448974656299691172676357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44598632875066254896901809 33448974656299691172676357)
    ·
      refine ⟨6271682748056192094876817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33448974656299691172676357 6271682748056192094876817)
      ·
        refine ⟨4703762061042144071157613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6271682748056192094876817 4703762061042144071157613)
        ·
          refine ⟨1763910772890804026684105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4703762061042144071157613 1763910772890804026684105)
          ·
            refine ⟨1322933079668103020013079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1763910772890804026684105 1322933079668103020013079)
            ·
              refine ⟨1984399619502154530019619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322933079668103020013079 1984399619502154530019619)
              ·
                refine ⟨2976599429253231795029429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984399619502154530019619 2976599429253231795029429)
                ·
                  refine ⟨279056196492490480784009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2976599429253231795029429 279056196492490480784009)
                  ·
                    rfl

theorem cell21_1222785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_1222785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222785 prefixEnd_1222785 := by exact prefixLift 1222785
  have htrace : WordTrace (prefixWord ++ tailWord_1222785) baseStart_1222785 baseEnd_1222785 := by
    simpa [prefixWord, tailWord_1222785, baseEnd_1222785] using wordTrace_append hprefix tailTrace_1222785
  have hstable : (prefixWord ++ tailWord_1222785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222785).length < 2 ^ (prefixWord ++ tailWord_1222785).sum := by decide
  have hdescent : baseEnd_1222785 < baseStart_1222785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222830 : List Nat := [4, 1, 4, 2, 1, 9]
def baseStart_1222830 : Nat := 118140960795 + 1222830 * 2 ^ 59
def prefixEnd_1222830 : Nat := 4983230072969 + 3 ^ 40 * 1222830 * 2
def baseEnd_1222830 : Nat := 10335795040947422316071

theorem tailTrace_1222830 : CollatzResearch.WordTrace tailWord_1222830 prefixEnd_1222830 10335795040947422316071 := by
  unfold tailWord_1222830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5575034269987903447786243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29733516106602151721526629 5575034269987903447786243)
  ·
    refine ⟨8362551404981855171679365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5575034269987903447786243 8362551404981855171679365)
    ·
      refine ⟨1567978388434097844689881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8362551404981855171679365 1567978388434097844689881)
      ·
        refine ⟨1175983791325573383517411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1567978388434097844689881 1175983791325573383517411)
        ·
          refine ⟨1763975686988360075276117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175983791325573383517411 1763975686988360075276117)
          ·
            refine ⟨10335795040947422316071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1763975686988360075276117 10335795040947422316071)
            ·
              rfl

theorem cell21_1222830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 9].length) (baseStart_1222830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222830 prefixEnd_1222830 := by exact prefixLift 1222830
  have htrace : WordTrace (prefixWord ++ tailWord_1222830) baseStart_1222830 baseEnd_1222830 := by
    simpa [prefixWord, tailWord_1222830, baseEnd_1222830] using wordTrace_append hprefix tailTrace_1222830
  have hstable : (prefixWord ++ tailWord_1222830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222830).length < 2 ^ (prefixWord ++ tailWord_1222830).sum := by decide
  have hdescent : baseEnd_1222830 < baseStart_1222830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222836 : List Nat := [2, 5, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1222836 : Nat := 118140960795 + 1222836 * 2 ^ 59
def prefixEnd_1222836 : Nat := 4983230072969 + 3 ^ 40 * 1222836 * 2
def baseEnd_1222836 : Nat := 279067835387325725433905

theorem tailTrace_1222836 : CollatzResearch.WordTrace tailWord_1222836 prefixEnd_1222836 279067835387325725433905 := by
  unfold tailWord_1222836
  simp only [CollatzResearch.WordTrace]
  refine ⟨22300246498940745303504181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29733661998587660404672241 22300246498940745303504181)
  ·
    refine ⟨2090648109275694872203517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22300246498940745303504181 2090648109275694872203517)
    ·
      refine ⟨783993040978385577076319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2090648109275694872203517 783993040978385577076319)
      ·
        refine ⟨1175989561467578365614479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783993040978385577076319 1175989561467578365614479)
        ·
          refine ⟨1763984342201367548421719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175989561467578365614479 1763984342201367548421719)
          ·
            refine ⟨2645976513302051322632579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763984342201367548421719 2645976513302051322632579)
            ·
              refine ⟨3968964769953076983948869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645976513302051322632579 3968964769953076983948869)
              ·
                refine ⟨744180894366201934490413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3968964769953076983948869 744180894366201934490413)
                ·
                  refine ⟨279067835387325725433905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744180894366201934490413 279067835387325725433905)
                  ·
                    rfl

theorem cell21_1222836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1222836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222836 prefixEnd_1222836 := by exact prefixLift 1222836
  have htrace : WordTrace (prefixWord ++ tailWord_1222836) baseStart_1222836 baseEnd_1222836 := by
    simpa [prefixWord, tailWord_1222836, baseEnd_1222836] using wordTrace_append hprefix tailTrace_1222836
  have hstable : (prefixWord ++ tailWord_1222836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222836).length < 2 ^ (prefixWord ++ tailWord_1222836).sum := by decide
  have hdescent : baseEnd_1222836 < baseStart_1222836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222858 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_1222858 : Nat := 118140960795 + 1222858 * 2 ^ 59
def prefixEnd_1222858 : Nat := 4983230072969 + 3 ^ 40 * 1222858 * 2
def baseEnd_1222858 : Nat := 279072856087058576067193

theorem tailTrace_1222858 : CollatzResearch.WordTrace tailWord_1222858 prefixEnd_1222858 279072856087058576067193 := by
  unfold tailWord_1222858
  simp only [CollatzResearch.WordTrace]
  refine ⟨11150323850950447091077307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29734196935867858909539485 11150323850950447091077307)
  ·
    refine ⟨16725485776425670636615961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11150323850950447091077307 16725485776425670636615961)
    ·
      refine ⟨12544114332319252977461971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16725485776425670636615961 12544114332319252977461971)
      ·
        refine ⟨18816171498478879466192957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12544114332319252977461971 18816171498478879466192957)
        ·
          refine ⟨7056064311929579799822359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18816171498478879466192957 7056064311929579799822359)
          ·
            refine ⟨10584096467894369699733539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7056064311929579799822359 10584096467894369699733539)
            ·
              refine ⟨15876144701841554549600309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10584096467894369699733539 15876144701841554549600309)
              ·
                refine ⟨1488388565797645739025029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15876144701841554549600309 1488388565797645739025029)
                ·
                  refine ⟨279072856087058576067193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1488388565797645739025029 279072856087058576067193)
                  ·
                    rfl

theorem cell21_1222858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_1222858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222858 prefixEnd_1222858 := by exact prefixLift 1222858
  have htrace : WordTrace (prefixWord ++ tailWord_1222858) baseStart_1222858 baseEnd_1222858 := by
    simpa [prefixWord, tailWord_1222858, baseEnd_1222858] using wordTrace_append hprefix tailTrace_1222858
  have hstable : (prefixWord ++ tailWord_1222858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222858).length < 2 ^ (prefixWord ++ tailWord_1222858).sum := by decide
  have hdescent : baseEnd_1222858 < baseStart_1222858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222948 : List Nat := [2, 3, 1, 3, 1, 2, 9]
def baseStart_1222948 : Nat := 118140960795 + 1222948 * 2 ^ 59
def prefixEnd_1222948 : Nat := 4983230072969 + 3 ^ 40 * 1222948 * 2
def baseEnd_1222948 : Nat := 31010377257026491063001

theorem tailTrace_1222948 : CollatzResearch.WordTrace tailWord_1222948 prefixEnd_1222948 31010377257026491063001 := by
  unfold tailWord_1222948
  simp only [CollatzResearch.WordTrace]
  refine ⟨22302288986737866867542749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29736385315650489156723665 22302288986737866867542749)
  ·
    refine ⟨8363358370026700075328531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22302288986737866867542749 8363358370026700075328531)
    ·
      refine ⟨12545037555040050112992797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8363358370026700075328531 12545037555040050112992797)
      ·
        refine ⟨4704389083140018792372299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12545037555040050112992797 4704389083140018792372299)
        ·
          refine ⟨7056583624710028188558449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4704389083140018792372299 7056583624710028188558449)
          ·
            refine ⟨5292437718532521141418837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7056583624710028188558449 5292437718532521141418837)
            ·
              refine ⟨31010377257026491063001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5292437718532521141418837 31010377257026491063001)
              ·
                rfl

theorem cell21_1222948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 9].length) (baseStart_1222948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222948 prefixEnd_1222948 := by exact prefixLift 1222948
  have htrace : WordTrace (prefixWord ++ tailWord_1222948) baseStart_1222948 baseEnd_1222948 := by
    simpa [prefixWord, tailWord_1222948, baseEnd_1222948] using wordTrace_append hprefix tailTrace_1222948
  have hstable : (prefixWord ++ tailWord_1222948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222948).length < 2 ^ (prefixWord ++ tailWord_1222948).sum := by decide
  have hdescent : baseEnd_1222948 < baseStart_1222948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1222954 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 5]
def baseStart_1222954 : Nat := 118140960795 + 1222954 * 2 ^ 59
def prefixEnd_1222954 : Nat := 4983230072969 + 3 ^ 40 * 1222954 * 2
def baseEnd_1222954 : Nat := 279094764594983742466997

theorem tailTrace_1222954 : CollatzResearch.WordTrace tailWord_1222954 prefixEnd_1222954 279094764594983742466997 := by
  unfold tailWord_1222954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11151199202863499189950979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29736531207635997839869277 11151199202863499189950979)
  ·
    refine ⟨16726798804295248784926469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11151199202863499189950979 16726798804295248784926469)
    ·
      refine ⟨3136274775805359147173713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16726798804295248784926469 3136274775805359147173713)
      ·
        refine ⟨2352206081854019360380285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3136274775805359147173713 2352206081854019360380285)
        ·
          refine ⟨882077280695257260142607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2352206081854019360380285 882077280695257260142607)
          ·
            refine ⟨1323115921042885890213911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882077280695257260142607 1323115921042885890213911)
            ·
              refine ⟨1984673881564328835320867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323115921042885890213911 1984673881564328835320867)
              ·
                refine ⟨2977010822346493252981301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1984673881564328835320867 2977010822346493252981301)
                ·
                  refine ⟨279094764594983742466997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2977010822346493252981301 279094764594983742466997)
                  ·
                    rfl

theorem cell21_1222954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_1222954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1222954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1222954 prefixEnd_1222954 := by exact prefixLift 1222954
  have htrace : WordTrace (prefixWord ++ tailWord_1222954) baseStart_1222954 baseEnd_1222954 := by
    simpa [prefixWord, tailWord_1222954, baseEnd_1222954] using wordTrace_append hprefix tailTrace_1222954
  have hstable : (prefixWord ++ tailWord_1222954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1222954).length < 2 ^ (prefixWord ++ tailWord_1222954).sum := by decide
  have hdescent : baseEnd_1222954 < baseStart_1222954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1222954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223013 : List Nat := [1, 3, 1, 3, 1, 3, 4, 2, 3]
def baseStart_1223013 : Nat := 118140960795 + 1223013 * 2 ^ 59
def prefixEnd_1223013 : Nat := 4983230072969 + 3 ^ 40 * 1223013 * 2
def baseEnd_1223013 : Nat := 279108229198812750983543

theorem tailTrace_1223013 : CollatzResearch.WordTrace tailWord_1223013 prefixEnd_1223013 279108229198812750983543 := by
  unfold tailWord_1223013
  simp only [CollatzResearch.WordTrace]
  refine ⟨44606948718240249836201693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29737965812160166557467795 44606948718240249836201693)
  ·
    refine ⟨16727605769340093688575635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44606948718240249836201693 16727605769340093688575635)
    ·
      refine ⟨25091408654010140532863453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16727605769340093688575635 25091408654010140532863453)
      ·
        refine ⟨9409278245253802699823795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25091408654010140532863453 9409278245253802699823795)
        ·
          refine ⟨14113917367880704049735693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9409278245253802699823795 14113917367880704049735693)
          ·
            refine ⟨5292719012955264018650885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14113917367880704049735693 5292719012955264018650885)
            ·
              refine ⟨992384814929112003497041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5292719012955264018650885 992384814929112003497041)
              ·
                refine ⟨744288611196834002622781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992384814929112003497041 744288611196834002622781)
                ·
                  refine ⟨279108229198812750983543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744288611196834002622781 279108229198812750983543)
                  ·
                    rfl

theorem cell21_1223013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_1223013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223013 prefixEnd_1223013 := by exact prefixLift 1223013
  have htrace : WordTrace (prefixWord ++ tailWord_1223013) baseStart_1223013 baseEnd_1223013 := by
    simpa [prefixWord, tailWord_1223013, baseEnd_1223013] using wordTrace_append hprefix tailTrace_1223013
  have hstable : (prefixWord ++ tailWord_1223013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223013).length < 2 ^ (prefixWord ++ tailWord_1223013).sum := by decide
  have hdescent : baseEnd_1223013 < baseStart_1223013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223024 : List Nat := [2, 1, 1, 1, 4, 3, 3, 6]
def baseStart_1223024 : Nat := 118140960795 + 1223024 * 2 ^ 59
def prefixEnd_1223024 : Nat := 4983230072969 + 3 ^ 40 * 1223024 * 2
def baseEnd_1223024 : Nat := 93036913182893058766729

theorem tailTrace_1223024 : CollatzResearch.WordTrace tailWord_1223024 prefixEnd_1223024 93036913182893058766729 := by
  unfold tailWord_1223024
  simp only [CollatzResearch.WordTrace]
  refine ⟨22303674960600199357426063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29738233280800265809901417 22303674960600199357426063)
  ·
    refine ⟨33455512440900299036139095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22303674960600199357426063 33455512440900299036139095)
    ·
      refine ⟨50183268661350448554208643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33455512440900299036139095 50183268661350448554208643)
      ·
        refine ⟨75274902992025672831312965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50183268661350448554208643 75274902992025672831312965)
        ·
          refine ⟨14114044311004813655871181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75274902992025672831312965 14114044311004813655871181)
          ·
            refine ⟨5292766616626805120951693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14114044311004813655871181 5292766616626805120951693)
            ·
              refine ⟨1984787481235051920356885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5292766616626805120951693 1984787481235051920356885)
              ·
                refine ⟨93036913182893058766729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1984787481235051920356885 93036913182893058766729)
                ·
                  rfl

theorem cell21_1223024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 6].length) (baseStart_1223024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223024 prefixEnd_1223024 := by exact prefixLift 1223024
  have htrace : WordTrace (prefixWord ++ tailWord_1223024) baseStart_1223024 baseEnd_1223024 := by
    simpa [prefixWord, tailWord_1223024, baseEnd_1223024] using wordTrace_append hprefix tailTrace_1223024
  have hstable : (prefixWord ++ tailWord_1223024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223024).length < 2 ^ (prefixWord ++ tailWord_1223024).sum := by decide
  have hdescent : baseEnd_1223024 < baseStart_1223024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223072 : List Nat := [2, 1, 1, 4, 1, 3, 2, 4, 3]
def baseStart_1223072 : Nat := 118140960795 + 1223072 * 2 ^ 59
def prefixEnd_1223072 : Nat := 4983230072969 + 3 ^ 40 * 1223072 * 2
def baseEnd_1223072 : Nat := 279121693802641759500089

theorem tailTrace_1223072 : CollatzResearch.WordTrace tailWord_1223072 prefixEnd_1223072 279121693802641759500089 := by
  unfold tailWord_1223072
  simp only [CollatzResearch.WordTrace]
  refine ⟨22304550312513251456299735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29739400416684335275066313 22304550312513251456299735)
  ·
    refine ⟨33456825468769877184449603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22304550312513251456299735 33456825468769877184449603)
    ·
      refine ⟨50185238203154815776674405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33456825468769877184449603 50185238203154815776674405)
      ·
        refine ⟨9409732163091527958126451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50185238203154815776674405 9409732163091527958126451)
        ·
          refine ⟨14114598244637291937189677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9409732163091527958126451 14114598244637291937189677)
          ·
            refine ⟨5292974341738984476446129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14114598244637291937189677 5292974341738984476446129)
            ·
              refine ⟨3969730756304238357334597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5292974341738984476446129 3969730756304238357334597)
              ·
                refine ⟨744324516807044692000237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3969730756304238357334597 744324516807044692000237)
                ·
                  refine ⟨279121693802641759500089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744324516807044692000237 279121693802641759500089)
                  ·
                    rfl

theorem cell21_1223072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 4, 3].length) (baseStart_1223072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223072 prefixEnd_1223072 := by exact prefixLift 1223072
  have htrace : WordTrace (prefixWord ++ tailWord_1223072) baseStart_1223072 baseEnd_1223072 := by
    simpa [prefixWord, tailWord_1223072, baseEnd_1223072] using wordTrace_append hprefix tailTrace_1223072
  have hstable : (prefixWord ++ tailWord_1223072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223072).length < 2 ^ (prefixWord ++ tailWord_1223072).sum := by decide
  have hdescent : baseEnd_1223072 < baseStart_1223072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223092 : List Nat := [2, 5, 2, 2, 1, 2, 2, 5]
def baseStart_1223092 : Nat := 118140960795 + 1223092 * 2 ^ 59
def prefixEnd_1223092 : Nat := 4983230072969 + 3 ^ 40 * 1223092 * 2
def baseEnd_1223092 : Nat := 93042086025042056388905

theorem tailTrace_1223092 : CollatzResearch.WordTrace tailWord_1223092 prefixEnd_1223092 93042086025042056388905 := by
  unfold tailWord_1223092
  simp only [CollatzResearch.WordTrace]
  refine ⟨22304915042477023164163765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29739886723302697552218353 22304915042477023164163765)
  ·
    refine ⟨2091085785232220921640353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22304915042477023164163765 2091085785232220921640353)
    ·
      refine ⟨1568314338924165691230265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2091085785232220921640353 1568314338924165691230265)
      ·
        refine ⟨1176235754193124268422699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1568314338924165691230265 1176235754193124268422699)
        ·
          refine ⟨1764353631289686402634049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176235754193124268422699 1764353631289686402634049)
          ·
            refine ⟨1323265223467264801975537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1764353631289686402634049 1323265223467264801975537)
            ·
              refine ⟨992448917600448601481653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1323265223467264801975537 992448917600448601481653)
              ·
                refine ⟨93042086025042056388905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 992448917600448601481653 93042086025042056388905)
                ·
                  rfl

theorem cell21_1223092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 5].length) (baseStart_1223092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223092 prefixEnd_1223092 := by exact prefixLift 1223092
  have htrace : WordTrace (prefixWord ++ tailWord_1223092) baseStart_1223092 baseEnd_1223092 := by
    simpa [prefixWord, tailWord_1223092, baseEnd_1223092] using wordTrace_append hprefix tailTrace_1223092
  have hstable : (prefixWord ++ tailWord_1223092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223092).length < 2 ^ (prefixWord ++ tailWord_1223092).sum := by decide
  have hdescent : baseEnd_1223092 < baseStart_1223092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223182 : List Nat := [4, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_1223182 : Nat := 118140960795 + 1223182 * 2 ^ 59
def prefixEnd_1223182 : Nat := 4983230072969 + 3 ^ 40 * 1223182 * 2
def baseEnd_1223182 : Nat := 279146797301306012666531

theorem tailTrace_1223182 : CollatzResearch.WordTrace tailWord_1223182 prefixEnd_1223182 279146797301306012666531 := by
  unfold tailWord_1223182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5576639081828498962387975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29742075103085327799402533 5576639081828498962387975)
  ·
    refine ⟨8364958622742748443581963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5576639081828498962387975 8364958622742748443581963)
    ·
      refine ⟨12547437934114122665372945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8364958622742748443581963 12547437934114122665372945)
      ·
        refine ⟨9410578450585591999029709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12547437934114122665372945 9410578450585591999029709)
        ·
          refine ⟨3528966918969596999636141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9410578450585591999029709 3528966918969596999636141)
          ·
            refine ⟨1323362594613598874863553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3528966918969596999636141 1323362594613598874863553)
            ·
              refine ⟨992521945960199156147665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1323362594613598874863553 992521945960199156147665)
              ·
                refine ⟨744391459470149367110749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992521945960199156147665 744391459470149367110749)
                ·
                  refine ⟨279146797301306012666531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744391459470149367110749 279146797301306012666531)
                  ·
                    rfl

theorem cell21_1223182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_1223182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223182 prefixEnd_1223182 := by exact prefixLift 1223182
  have htrace : WordTrace (prefixWord ++ tailWord_1223182) baseStart_1223182 baseEnd_1223182 := by
    simpa [prefixWord, tailWord_1223182, baseEnd_1223182] using wordTrace_append hprefix tailTrace_1223182
  have hstable : (prefixWord ++ tailWord_1223182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223182).length < 2 ^ (prefixWord ++ tailWord_1223182).sum := by decide
  have hdescent : baseEnd_1223182 < baseStart_1223182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223221 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 6]
def baseStart_1223221 : Nat := 118140960795 + 1223221 * 2 ^ 59
def prefixEnd_1223221 : Nat := 4983230072969 + 3 ^ 40 * 1223221 * 2
def baseEnd_1223221 : Nat := 279155697632650611516451

theorem tailTrace_1223221 : CollatzResearch.WordTrace tailWord_1223221 prefixEnd_1223221 279155697632650611516451 := by
  unfold tailWord_1223221
  simp only [CollatzResearch.WordTrace]
  refine ⟨44614535101486701359773517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29743023400991134239849011 44614535101486701359773517)
  ·
    refine ⟨16730450663057513009915069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44614535101486701359773517 16730450663057513009915069)
    ·
      refine ⟨6273918998646567378718151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16730450663057513009915069 6273918998646567378718151)
      ·
        refine ⟨9410878497969851068077227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6273918998646567378718151 9410878497969851068077227)
        ·
          refine ⟨14116317746954776602115841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9410878497969851068077227 14116317746954776602115841)
          ·
            refine ⟨10587238310216082451586881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14116317746954776602115841 10587238310216082451586881)
            ·
              refine ⟨7940428732662061838690161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10587238310216082451586881 7940428732662061838690161)
              ·
                refine ⟨5955321549496546379017621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7940428732662061838690161 5955321549496546379017621)
                ·
                  refine ⟨279155697632650611516451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5955321549496546379017621 279155697632650611516451)
                  ·
                    rfl

theorem cell21_1223221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_1223221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223221 prefixEnd_1223221 := by exact prefixLift 1223221
  have htrace : WordTrace (prefixWord ++ tailWord_1223221) baseStart_1223221 baseEnd_1223221 := by
    simpa [prefixWord, tailWord_1223221, baseEnd_1223221] using wordTrace_append hprefix tailTrace_1223221
  have hstable : (prefixWord ++ tailWord_1223221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223221).length < 2 ^ (prefixWord ++ tailWord_1223221).sum := by decide
  have hdescent : baseEnd_1223221 < baseStart_1223221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223224 : List Nat := [2, 1, 2, 1, 4, 1, 4, 3, 3]
def baseStart_1223224 : Nat := 118140960795 + 1223224 * 2 ^ 59
def prefixEnd_1223224 : Nat := 4983230072969 + 3 ^ 40 * 1223224 * 2
def baseEnd_1223224 : Nat := 279156382273523272966445

theorem tailTrace_1223224 : CollatzResearch.WordTrace tailWord_1223224 prefixEnd_1223224 279156382273523272966445 := by
  unfold tailWord_1223224
  simp only [CollatzResearch.WordTrace]
  refine ⟨22307322260237916436066363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29743096346983888581421817 22307322260237916436066363)
  ·
    refine ⟨33460983390356874654099545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22307322260237916436066363 33460983390356874654099545)
    ·
      refine ⟨25095737542767655990574659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33460983390356874654099545 25095737542767655990574659)
      ·
        refine ⟨37643606314151483985861989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25095737542767655990574659 37643606314151483985861989)
        ·
          refine ⟨7058176183903403247349123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37643606314151483985861989 7058176183903403247349123)
          ·
            refine ⟨10587264275855104871023685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058176183903403247349123 10587264275855104871023685)
            ·
              refine ⟨1985112051722832163316941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10587264275855104871023685 1985112051722832163316941)
              ·
                refine ⟨744417019396062061243853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1985112051722832163316941 744417019396062061243853)
                ·
                  refine ⟨279156382273523272966445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744417019396062061243853 279156382273523272966445)
                  ·
                    rfl

theorem cell21_1223224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 3, 3].length) (baseStart_1223224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223224 prefixEnd_1223224 := by exact prefixLift 1223224
  have htrace : WordTrace (prefixWord ++ tailWord_1223224) baseStart_1223224 baseEnd_1223224 := by
    simpa [prefixWord, tailWord_1223224, baseEnd_1223224] using wordTrace_append hprefix tailTrace_1223224
  have hstable : (prefixWord ++ tailWord_1223224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223224).length < 2 ^ (prefixWord ++ tailWord_1223224).sum := by decide
  have hdescent : baseEnd_1223224 < baseStart_1223224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223283 : List Nat := [1, 1, 1, 2, 2, 1, 1, 9, 3]
def baseStart_1223283 : Nat := 118140960795 + 1223283 * 2 ^ 59
def prefixEnd_1223283 : Nat := 4983230072969 + 3 ^ 40 * 1223283 * 2
def baseEnd_1223283 : Nat := 279169846877352281482991

theorem tailTrace_1223283 : CollatzResearch.WordTrace tailWord_1223283 prefixEnd_1223283 279169846877352281482991 := by
  unfold tailWord_1223283
  simp only [CollatzResearch.WordTrace]
  refine ⟨44616796427262085948530503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29744530951508057299020335 44616796427262085948530503)
  ·
    refine ⟨66925194640893128922795755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44616796427262085948530503 66925194640893128922795755)
    ·
      refine ⟨100387791961339693384193633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66925194640893128922795755 100387791961339693384193633)
      ·
        refine ⟨75290843971004770038145225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100387791961339693384193633 75290843971004770038145225)
        ·
          refine ⟨56468132978253577528608919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75290843971004770038145225 56468132978253577528608919)
          ·
            refine ⟨84702199467380366292913379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56468132978253577528608919 84702199467380366292913379)
            ·
              refine ⟨127053299201070549439370069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84702199467380366292913379 127053299201070549439370069)
              ·
                refine ⟨744452925006272750621309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 127053299201070549439370069 744452925006272750621309)
                ·
                  refine ⟨279169846877352281482991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744452925006272750621309 279169846877352281482991)
                  ·
                    rfl

theorem cell21_1223283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 3].length) (baseStart_1223283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223283 prefixEnd_1223283 := by exact prefixLift 1223283
  have htrace : WordTrace (prefixWord ++ tailWord_1223283) baseStart_1223283 baseEnd_1223283 := by
    simpa [prefixWord, tailWord_1223283, baseEnd_1223283] using wordTrace_append hprefix tailTrace_1223283
  have hstable : (prefixWord ++ tailWord_1223283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223283).length < 2 ^ (prefixWord ++ tailWord_1223283).sum := by decide
  have hdescent : baseEnd_1223283 < baseStart_1223283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223286 : List Nat := [5, 1, 1, 2, 4, 1, 7]
def baseStart_1223286 : Nat := 118140960795 + 1223286 * 2 ^ 59
def prefixEnd_1223286 : Nat := 4983230072969 + 3 ^ 40 * 1223286 * 2
def baseEnd_1223286 : Nat := 31018947946469438103665

theorem tailTrace_1223286 : CollatzResearch.WordTrace tailWord_1223286 prefixEnd_1223286 31018947946469438103665 := by
  unfold tailWord_1223286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2788556615390701091305607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29744603897500811640593141 2788556615390701091305607)
  ·
    refine ⟨4182834923086051636958411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2788556615390701091305607 4182834923086051636958411)
    ·
      refine ⟨6274252384629077455437617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4182834923086051636958411 6274252384629077455437617)
      ·
        refine ⟨4705689288471808091578213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6274252384629077455437617 4705689288471808091578213)
        ·
          refine ⟨882316741588464017170915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4705689288471808091578213 882316741588464017170915)
          ·
            refine ⟨1323475112382696025756373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882316741588464017170915 1323475112382696025756373)
            ·
              refine ⟨31018947946469438103665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1323475112382696025756373 31018947946469438103665)
              ·
                rfl

theorem cell21_1223286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 7].length) (baseStart_1223286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223286 prefixEnd_1223286 := by exact prefixLift 1223286
  have htrace : WordTrace (prefixWord ++ tailWord_1223286) baseStart_1223286 baseEnd_1223286 := by
    simpa [prefixWord, tailWord_1223286, baseEnd_1223286] using wordTrace_append hprefix tailTrace_1223286
  have hstable : (prefixWord ++ tailWord_1223286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223286).length < 2 ^ (prefixWord ++ tailWord_1223286).sum := by decide
  have hdescent : baseEnd_1223286 < baseStart_1223286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223297 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 6]
def baseStart_1223297 : Nat := 118140960795 + 1223297 * 2 ^ 59
def prefixEnd_1223297 : Nat := 4983230072969 + 3 ^ 40 * 1223297 * 2
def baseEnd_1223297 : Nat := 279173041868091368249629

theorem tailTrace_1223297 : CollatzResearch.WordTrace tailWord_1223297 prefixEnd_1223297 279173041868091368249629 := by
  unfold tailWord_1223297
  simp only [CollatzResearch.WordTrace]
  refine ⟨44617307049211366339540145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29744871366140910893026763 44617307049211366339540145)
  ·
    refine ⟨33462980286908524754655109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44617307049211366339540145 33462980286908524754655109)
    ·
      refine ⟨6274308803795348391497833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33462980286908524754655109 6274308803795348391497833)
      ·
        refine ⟨4705731602846511293623375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6274308803795348391497833 4705731602846511293623375)
        ·
          refine ⟨7058597404269766940435063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4705731602846511293623375 7058597404269766940435063)
          ·
            refine ⟨10587896106404650410652595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058597404269766940435063 10587896106404650410652595)
            ·
              refine ⟨15881844159606975615978893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10587896106404650410652595 15881844159606975615978893)
              ·
                refine ⟨5955691559852615855992085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15881844159606975615978893 5955691559852615855992085)
                ·
                  refine ⟨279173041868091368249629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5955691559852615855992085 279173041868091368249629)
                  ·
                    rfl

theorem cell21_1223297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_1223297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223297 prefixEnd_1223297 := by exact prefixLift 1223297
  have htrace : WordTrace (prefixWord ++ tailWord_1223297) baseStart_1223297 baseEnd_1223297 := by
    simpa [prefixWord, tailWord_1223297, baseEnd_1223297] using wordTrace_append hprefix tailTrace_1223297
  have hstable : (prefixWord ++ tailWord_1223297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223297).length < 2 ^ (prefixWord ++ tailWord_1223297).sum := by decide
  have hdescent : baseEnd_1223297 < baseStart_1223297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223300 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 5]
def baseStart_1223300 : Nat := 118140960795 + 1223300 * 2 ^ 59
def prefixEnd_1223300 : Nat := 4983230072969 + 3 ^ 40 * 1223300 * 2
def baseEnd_1223300 : Nat := 279173726508964029699623

theorem tailTrace_1223300 : CollatzResearch.WordTrace tailWord_1223300 prefixEnd_1223300 279173726508964029699623 := by
  unfold tailWord_1223300
  simp only [CollatzResearch.WordTrace]
  refine ⟨22308708234100248925949677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29744944312133665234599569 22308708234100248925949677)
  ·
    refine ⟨8365765587787593347231129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22308708234100248925949677 8365765587787593347231129)
    ·
      refine ⟨6274324190840695010423347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8365765587787593347231129 6274324190840695010423347)
      ·
        refine ⟨9411486286261042515635021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6274324190840695010423347 9411486286261042515635021)
        ·
          refine ⟨3529307357347890943363133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9411486286261042515635021 3529307357347890943363133)
          ·
            refine ⟨1323490259005459103761175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3529307357347890943363133 1323490259005459103761175)
            ·
              refine ⟨1985235388508188655641763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1323490259005459103761175 1985235388508188655641763)
              ·
                refine ⟨2977853082762282983462645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985235388508188655641763 2977853082762282983462645)
                ·
                  refine ⟨279173726508964029699623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2977853082762282983462645 279173726508964029699623)
                  ·
                    rfl

theorem cell21_1223300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_1223300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223300 prefixEnd_1223300 := by exact prefixLift 1223300
  have htrace : WordTrace (prefixWord ++ tailWord_1223300) baseStart_1223300 baseEnd_1223300 := by
    simpa [prefixWord, tailWord_1223300, baseEnd_1223300] using wordTrace_append hprefix tailTrace_1223300
  have hstable : (prefixWord ++ tailWord_1223300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223300).length < 2 ^ (prefixWord ++ tailWord_1223300).sum := by decide
  have hdescent : baseEnd_1223300 < baseStart_1223300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223345 : List Nat := [1, 2, 2, 6, 2, 8]
def baseStart_1223345 : Nat := 118140960795 + 1223345 * 2 ^ 59
def prefixEnd_1223345 : Nat := 4983230072969 + 3 ^ 40 * 1223345 * 2
def baseEnd_1223345 : Nat := 10340148004520516720353

theorem tailTrace_1223345 : CollatzResearch.WordTrace tailWord_1223345 prefixEnd_1223345 10340148004520516720353 := by
  unfold tailWord_1223345
  simp only [CollatzResearch.WordTrace]
  refine ⟨44619057753037470537287489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29746038502024980358191659 44619057753037470537287489)
  ·
    refine ⟨33464293314778102902965617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44619057753037470537287489 33464293314778102902965617)
    ·
      refine ⟨25098219986083577177224213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33464293314778102902965617 25098219986083577177224213)
      ·
        refine ⟨1176479061847667680182385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25098219986083577177224213 1176479061847667680182385)
        ·
          refine ⟨882359296385750760136789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1176479061847667680182385 882359296385750760136789)
          ·
            refine ⟨10340148004520516720353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 882359296385750760136789 10340148004520516720353)
            ·
              rfl

theorem cell21_1223345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 8].length) (baseStart_1223345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223345 prefixEnd_1223345 := by exact prefixLift 1223345
  have htrace : WordTrace (prefixWord ++ tailWord_1223345) baseStart_1223345 baseEnd_1223345 := by
    simpa [prefixWord, tailWord_1223345, baseEnd_1223345] using wordTrace_append hprefix tailTrace_1223345
  have hstable : (prefixWord ++ tailWord_1223345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223345).length < 2 ^ (prefixWord ++ tailWord_1223345).sum := by decide
  have hdescent : baseEnd_1223345 < baseStart_1223345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223418 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_1223418 : Nat := 118140960795 + 1223418 * 2 ^ 59
def prefixEnd_1223418 : Nat := 4983230072969 + 3 ^ 40 * 1223418 * 2
def baseEnd_1223418 : Nat := 279200655716622046732715

theorem tailTrace_1223418 : CollatzResearch.WordTrace tailWord_1223418 prefixEnd_1223418 279200655716622046732715 := by
  unfold tailWord_1223418
  simp only [CollatzResearch.WordTrace]
  refine ⟨11155430070443251001173727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29747813521182002669796605 11155430070443251001173727)
  ·
    refine ⟨16733145105664876501760591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11155430070443251001173727 16733145105664876501760591)
    ·
      refine ⟨25099717658497314752640887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16733145105664876501760591 25099717658497314752640887)
      ·
        refine ⟨37649576487745972128961331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25099717658497314752640887 37649576487745972128961331)
        ·
          refine ⟨56474364731618958193441997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37649576487745972128961331 56474364731618958193441997)
          ·
            refine ⟨21177886774357109322540749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56474364731618958193441997 21177886774357109322540749)
            ·
              refine ⟨7941707540383915995952781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21177886774357109322540749 7941707540383915995952781)
              ·
                refine ⟨2978140327643968498482293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7941707540383915995952781 2978140327643968498482293)
                ·
                  refine ⟨279200655716622046732715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2978140327643968498482293 279200655716622046732715)
                  ·
                    rfl

theorem cell21_1223418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_1223418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223418 prefixEnd_1223418 := by exact prefixLift 1223418
  have htrace : WordTrace (prefixWord ++ tailWord_1223418) baseStart_1223418 baseEnd_1223418 := by
    simpa [prefixWord, tailWord_1223418, baseEnd_1223418] using wordTrace_append hprefix tailTrace_1223418
  have hstable : (prefixWord ++ tailWord_1223418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223418).length < 2 ^ (prefixWord ++ tailWord_1223418).sum := by decide
  have hdescent : baseEnd_1223418 < baseStart_1223418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223452 : List Nat := [2, 2, 3, 1, 1, 3, 3, 3, 3]
def baseStart_1223452 : Nat := 118140960795 + 1223452 * 2 ^ 59
def prefixEnd_1223452 : Nat := 4983230072969 + 3 ^ 40 * 1223452 * 2
def baseEnd_1223452 : Nat := 279208414979845543165979

theorem tailTrace_1223452 : CollatzResearch.WordTrace tailWord_1223452 prefixEnd_1223452 279208414979845543165979 := by
  unfold tailWord_1223452
  simp only [CollatzResearch.WordTrace]
  refine ⟨22311480181824913905716305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29748640242433218540955073 22311480181824913905716305)
  ·
    refine ⟨16733610136368685429287229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22311480181824913905716305 16733610136368685429287229)
    ·
      refine ⟨6275103801138257035982711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16733610136368685429287229 6275103801138257035982711)
      ·
        refine ⟨9412655701707385553974067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6275103801138257035982711 9412655701707385553974067)
        ·
          refine ⟨14118983552561078330961101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9412655701707385553974067 14118983552561078330961101)
          ·
            refine ⟨5294618832210404374110413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14118983552561078330961101 5294618832210404374110413)
            ·
              refine ⟨1985482062078901640291405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5294618832210404374110413 1985482062078901640291405)
              ·
                refine ⟨744555773279588115109277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1985482062078901640291405 744555773279588115109277)
                ·
                  refine ⟨279208414979845543165979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744555773279588115109277 279208414979845543165979)
                  ·
                    rfl

theorem cell21_1223452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 3].length) (baseStart_1223452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223452 prefixEnd_1223452 := by exact prefixLift 1223452
  have htrace : WordTrace (prefixWord ++ tailWord_1223452) baseStart_1223452 baseEnd_1223452 := by
    simpa [prefixWord, tailWord_1223452, baseEnd_1223452] using wordTrace_append hprefix tailTrace_1223452
  have hstable : (prefixWord ++ tailWord_1223452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223452).length < 2 ^ (prefixWord ++ tailWord_1223452).sum := by decide
  have hdescent : baseEnd_1223452 < baseStart_1223452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223525 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 4]
def baseStart_1223525 : Nat := 118140960795 + 1223525 * 2 ^ 59
def prefixEnd_1223525 : Nat := 4983230072969 + 3 ^ 40 * 1223525 * 2
def baseEnd_1223525 : Nat := 279225074574413638449163

theorem tailTrace_1223525 : CollatzResearch.WordTrace tailWord_1223525 prefixEnd_1223525 279225074574413638449163 := by
  unfold tailWord_1223525
  simp only [CollatzResearch.WordTrace]
  refine ⟨44625622892385361278840029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29750415261590240852560019 44625622892385361278840029)
  ·
    refine ⟨16734608584644510479565011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44625622892385361278840029 16734608584644510479565011)
    ·
      refine ⟨25101912876966765719347517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16734608584644510479565011 25101912876966765719347517)
      ·
        refine ⟨9413217328862537144755319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25101912876966765719347517 9413217328862537144755319)
        ·
          refine ⟨14119825993293805717132979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9413217328862537144755319 14119825993293805717132979)
          ·
            refine ⟨21179738989940708575699469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14119825993293805717132979 21179738989940708575699469)
            ·
              refine ⟨7942402121227765715887301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21179738989940708575699469 7942402121227765715887301)
              ·
                refine ⟨1489200397730206071728869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7942402121227765715887301 1489200397730206071728869)
                ·
                  refine ⟨279225074574413638449163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1489200397730206071728869 279225074574413638449163)
                  ·
                    rfl

theorem cell21_1223525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_1223525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223525 prefixEnd_1223525 := by exact prefixLift 1223525
  have htrace : WordTrace (prefixWord ++ tailWord_1223525) baseStart_1223525 baseEnd_1223525 := by
    simpa [prefixWord, tailWord_1223525, baseEnd_1223525] using wordTrace_append hprefix tailTrace_1223525
  have hstable : (prefixWord ++ tailWord_1223525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223525).length < 2 ^ (prefixWord ++ tailWord_1223525).sum := by decide
  have hdescent : baseEnd_1223525 < baseStart_1223525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223528 : List Nat := [2, 1, 4, 2, 1, 3, 1, 4, 3]
def baseStart_1223528 : Nat := 118140960795 + 1223528 * 2 ^ 59
def prefixEnd_1223528 : Nat := 4983230072969 + 3 ^ 40 * 1223528 * 2
def baseEnd_1223528 : Nat := 279225759215286299899157

theorem tailTrace_1223528 : CollatzResearch.WordTrace tailWord_1223528 prefixEnd_1223528 279225759215286299899157 := by
  unfold tailWord_1223528
  simp only [CollatzResearch.WordTrace]
  refine ⟨22312866155687246395599619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29750488207582995194132825 22312866155687246395599619)
  ·
    refine ⟨33469299233530869593399429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22312866155687246395599619 33469299233530869593399429)
    ·
      refine ⟨6275493606287038048762393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33469299233530869593399429 6275493606287038048762393)
      ·
        refine ⟨4706620204715278536571795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6275493606287038048762393 4706620204715278536571795)
        ·
          refine ⟨7059930307072917804857693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4706620204715278536571795 7059930307072917804857693)
          ·
            refine ⟨2647473865152344176821635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7059930307072917804857693 2647473865152344176821635)
            ·
              refine ⟨3971210797728516265232453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647473865152344176821635 3971210797728516265232453)
              ·
                refine ⟨744602024574096799731085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3971210797728516265232453 744602024574096799731085)
                ·
                  refine ⟨279225759215286299899157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744602024574096799731085 279225759215286299899157)
                  ·
                    rfl

theorem cell21_1223528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 4, 3].length) (baseStart_1223528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223528 prefixEnd_1223528 := by exact prefixLift 1223528
  have htrace : WordTrace (prefixWord ++ tailWord_1223528) baseStart_1223528 baseEnd_1223528 := by
    simpa [prefixWord, tailWord_1223528, baseEnd_1223528] using wordTrace_append hprefix tailTrace_1223528
  have hstable : (prefixWord ++ tailWord_1223528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223528).length < 2 ^ (prefixWord ++ tailWord_1223528).sum := by decide
  have hdescent : baseEnd_1223528 < baseStart_1223528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223539 : List Nat := [1, 1, 1, 2, 2, 1, 7, 6]
def baseStart_1223539 : Nat := 118140960795 + 1223539 * 2 ^ 59
def prefixEnd_1223539 : Nat := 4983230072969 + 3 ^ 40 * 1223539 * 2
def baseEnd_1223539 : Nat := 93076089855050908405267

theorem tailTrace_1223539 : CollatzResearch.WordTrace tailWord_1223539 prefixEnd_1223539 93076089855050908405267 := by
  unfold tailWord_1223539
  simp only [CollatzResearch.WordTrace]
  refine ⟨44626133514334641669849671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29750755676223094446566447 44626133514334641669849671)
  ·
    refine ⟨66939200271501962504774507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44626133514334641669849671 66939200271501962504774507)
    ·
      refine ⟨100408800407252943757161761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66939200271501962504774507 100408800407252943757161761)
      ·
        refine ⟨75306600305439707817871321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100408800407252943757161761 75306600305439707817871321)
        ·
          refine ⟨56479950229079780863403491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75306600305439707817871321 56479950229079780863403491)
          ·
            refine ⟨84719925343619671295105237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56479950229079780863403491 84719925343619671295105237)
            ·
              refine ⟨1985623250241086045979029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 84719925343619671295105237 1985623250241086045979029)
              ·
                refine ⟨93076089855050908405267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1985623250241086045979029 93076089855050908405267)
                ·
                  rfl

theorem cell21_1223539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 6].length) (baseStart_1223539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223539 prefixEnd_1223539 := by exact prefixLift 1223539
  have htrace : WordTrace (prefixWord ++ tailWord_1223539) baseStart_1223539 baseEnd_1223539 := by
    simpa [prefixWord, tailWord_1223539, baseEnd_1223539] using wordTrace_append hprefix tailTrace_1223539
  have hstable : (prefixWord ++ tailWord_1223539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223539).length < 2 ^ (prefixWord ++ tailWord_1223539).sum := by decide
  have hdescent : baseEnd_1223539 < baseStart_1223539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223587 : List Nat := [1, 1, 1, 4, 1, 2, 4, 4, 3]
def baseStart_1223587 : Nat := 118140960795 + 1223587 * 2 ^ 59
def prefixEnd_1223587 : Nat := 4983230072969 + 3 ^ 40 * 1223587 * 2
def baseEnd_1223587 : Nat := 279239223819115308415703

theorem tailTrace_1223587 : CollatzResearch.WordTrace tailWord_1223587 prefixEnd_1223587 279239223819115308415703 := by
  unfold tailWord_1223587
  simp only [CollatzResearch.WordTrace]
  refine ⟨44627884218160745867597015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29751922812107163911731343 44627884218160745867597015)
  ·
    refine ⟨66941826327241118801395523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44627884218160745867597015 66941826327241118801395523)
    ·
      refine ⟨100412739490861678202093285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66941826327241118801395523 100412739490861678202093285)
      ·
        refine ⟨18827388654536564662892491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100412739490861678202093285 18827388654536564662892491)
        ·
          refine ⟨28241082981804846994338737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18827388654536564662892491 28241082981804846994338737)
          ·
            refine ⟨21180812236353635245754053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28241082981804846994338737 21180812236353635245754053)
            ·
              refine ⟨3971402294316306608578885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21180812236353635245754053 3971402294316306608578885)
              ·
                refine ⟨744637930184307489108541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3971402294316306608578885 744637930184307489108541)
                ·
                  refine ⟨279239223819115308415703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744637930184307489108541 279239223819115308415703)
                  ·
                    rfl

theorem cell21_1223587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 3].length) (baseStart_1223587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223587 prefixEnd_1223587 := by exact prefixLift 1223587
  have htrace : WordTrace (prefixWord ++ tailWord_1223587) baseStart_1223587 baseEnd_1223587 := by
    simpa [prefixWord, tailWord_1223587, baseEnd_1223587] using wordTrace_append hprefix tailTrace_1223587
  have hstable : (prefixWord ++ tailWord_1223587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223587).length < 2 ^ (prefixWord ++ tailWord_1223587).sum := by decide
  have hdescent : baseEnd_1223587 < baseStart_1223587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223604 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1223604 : Nat := 118140960795 + 1223604 * 2 ^ 59
def prefixEnd_1223604 : Nat := 4983230072969 + 3 ^ 40 * 1223604 * 2
def baseEnd_1223604 : Nat := 279243103450727056632335

theorem tailTrace_1223604 : CollatzResearch.WordTrace tailWord_1223604 prefixEnd_1223604 279243103450727056632335 := by
  unfold tailWord_1223604
  simp only [CollatzResearch.WordTrace]
  refine ⟨22314252129549578885482933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29752336172732771847310577 22314252129549578885482933)
  ·
    refine ⟨2091961137145273020514025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22314252129549578885482933 2091961137145273020514025)
    ·
      refine ⟨1568970852858954765385519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2091961137145273020514025 1568970852858954765385519)
      ·
        refine ⟨2353456279288432148078279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1568970852858954765385519 2353456279288432148078279)
        ·
          refine ⟨3530184418932648222117419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353456279288432148078279 3530184418932648222117419)
          ·
            refine ⟨5295276628398972333176129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530184418932648222117419 5295276628398972333176129)
            ·
              refine ⟨3971457471299229249882097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5295276628398972333176129 3971457471299229249882097)
              ·
                refine ⟨2978593103474421937411573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3971457471299229249882097 2978593103474421937411573)
                ·
                  refine ⟨279243103450727056632335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2978593103474421937411573 279243103450727056632335)
                  ·
                    rfl

theorem cell21_1223604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1223604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223604 prefixEnd_1223604 := by exact prefixLift 1223604
  have htrace : WordTrace (prefixWord ++ tailWord_1223604) baseStart_1223604 baseEnd_1223604 := by
    simpa [prefixWord, tailWord_1223604, baseEnd_1223604] using wordTrace_append hprefix tailTrace_1223604
  have hstable : (prefixWord ++ tailWord_1223604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223604).length < 2 ^ (prefixWord ++ tailWord_1223604).sum := by decide
  have hdescent : baseEnd_1223604 < baseStart_1223604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223638 : List Nat := [5, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1223638 : Nat := 118140960795 + 1223638 * 2 ^ 59
def prefixEnd_1223638 : Nat := 4983230072969 + 3 ^ 40 * 1223638 * 2
def baseEnd_1223638 : Nat := 279250862713950553065599

theorem tailTrace_1223638 : CollatzResearch.WordTrace tailWord_1223638 prefixEnd_1223638 279250862713950553065599 := by
  unfold tailWord_1223638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789359021310998848606473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29753162893983987718469045 2789359021310998848606473)
  ·
    refine ⟨2092019265983249136454855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2789359021310998848606473 2092019265983249136454855)
    ·
      refine ⟨3138028898974873704682283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092019265983249136454855 3138028898974873704682283)
      ·
        refine ⟨4707043348462310557023425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3138028898974873704682283 4707043348462310557023425)
        ·
          refine ⟨3530282511346732917767569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4707043348462310557023425 3530282511346732917767569)
          ·
            refine ⟨2647711883510049688325677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530282511346732917767569 2647711883510049688325677)
            ·
              refine ⟨992891956316268633122129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2647711883510049688325677 992891956316268633122129)
              ·
                refine ⟨744668967237201474841597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992891956316268633122129 744668967237201474841597)
                ·
                  refine ⟨279250862713950553065599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 744668967237201474841597 279250862713950553065599)
                  ·
                    rfl

theorem cell21_1223638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1223638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223638 prefixEnd_1223638 := by exact prefixLift 1223638
  have htrace : WordTrace (prefixWord ++ tailWord_1223638) baseStart_1223638 baseEnd_1223638 := by
    simpa [prefixWord, tailWord_1223638, baseEnd_1223638] using wordTrace_append hprefix tailTrace_1223638
  have hstable : (prefixWord ++ tailWord_1223638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223638).length < 2 ^ (prefixWord ++ tailWord_1223638).sum := by decide
  have hdescent : baseEnd_1223638 < baseStart_1223638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223694 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1223694 : Nat := 118140960795 + 1223694 * 2 ^ 59
def prefixEnd_1223694 : Nat := 4983230072969 + 3 ^ 40 * 1223694 * 2
def baseEnd_1223694 : Nat := 279263642676906900132151

theorem tailTrace_1223694 : CollatzResearch.WordTrace tailWord_1223694 prefixEnd_1223694 279263642676906900132151 := by
  unfold tailWord_1223694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5578973353596637892717767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29754524552515402094494757 5578973353596637892717767)
  ·
    refine ⟨8368460030394956839076651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5578973353596637892717767 8368460030394956839076651)
    ·
      refine ⟨12552690045592435258614977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8368460030394956839076651 12552690045592435258614977)
      ·
        refine ⟨9414517534194326443961233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12552690045592435258614977 9414517534194326443961233)
        ·
          refine ⟨7060888150645744832970925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9414517534194326443961233 7060888150645744832970925)
          ·
            refine ⟨2647833056492154312364097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7060888150645744832970925 2647833056492154312364097)
            ·
              refine ⟨1985874792369115734273073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2647833056492154312364097 1985874792369115734273073)
              ·
                refine ⟨1489406094276836800704805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1985874792369115734273073 1489406094276836800704805)
                ·
                  refine ⟨279263642676906900132151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1489406094276836800704805 279263642676906900132151)
                  ·
                    rfl

theorem cell21_1223694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1223694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223694 prefixEnd_1223694 := by exact prefixLift 1223694
  have htrace : WordTrace (prefixWord ++ tailWord_1223694) baseStart_1223694 baseEnd_1223694 := by
    simpa [prefixWord, tailWord_1223694, baseEnd_1223694] using wordTrace_append hprefix tailTrace_1223694
  have hstable : (prefixWord ++ tailWord_1223694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223694).length < 2 ^ (prefixWord ++ tailWord_1223694).sum := by decide
  have hdescent : baseEnd_1223694 < baseStart_1223694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223860 : List Nat := [2, 5, 3, 11]
def baseStart_1223860 : Nat := 118140960795 + 1223860 * 2 ^ 59
def prefixEnd_1223860 : Nat := 4983230072969 + 3 ^ 40 * 1223860 * 2
def baseEnd_1223860 : Nat := 1149388996454845680515

theorem tailTrace_1223860 : CollatzResearch.WordTrace tailWord_1223860 prefixEnd_1223860 1149388996454845680515 := by
  unfold tailWord_1223860
  simp only [CollatzResearch.WordTrace]
  refine ⟨22318920673085856746142517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29758560897447808994856689 22318920673085856746142517)
  ·
    refine ⟨2092398813101799069950861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22318920673085856746142517 2092398813101799069950861)
    ·
      refine ⟨784649554913174651231573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2092398813101799069950861 784649554913174651231573)
      ·
        refine ⟨1149388996454845680515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 784649554913174651231573 1149388996454845680515)
        ·
          rfl

theorem cell21_1223860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 11].length) (baseStart_1223860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223860 prefixEnd_1223860 := by exact prefixLift 1223860
  have htrace : WordTrace (prefixWord ++ tailWord_1223860) baseStart_1223860 baseEnd_1223860 := by
    simpa [prefixWord, tailWord_1223860, baseEnd_1223860] using wordTrace_append hprefix tailTrace_1223860
  have hstable : (prefixWord ++ tailWord_1223860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223860).length < 2 ^ (prefixWord ++ tailWord_1223860).sum := by decide
  have hdescent : baseEnd_1223860 < baseStart_1223860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223894 : List Nat := [5, 2, 1, 2, 2, 1, 3, 5]
def baseStart_1223894 : Nat := 118140960795 + 1223894 * 2 ^ 59
def prefixEnd_1223894 : Nat := 4983230072969 + 3 ^ 40 * 1223894 * 2
def baseEnd_1223894 : Nat := 93103095133916998932803

theorem tailTrace_1223894 : CollatzResearch.WordTrace tailWord_1223894 prefixEnd_1223894 93103095133916998932803 := by
  unfold tailWord_1223894
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789942589253033581188921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29759387618699024866015157 2789942589253033581188921)
  ·
    refine ⟨2092456941939775185891691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2789942589253033581188921 2092456941939775185891691)
    ·
      refine ⟨3138685412909662778837537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2092456941939775185891691 3138685412909662778837537)
      ·
        refine ⟨2354014059682247084128153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3138685412909662778837537 2354014059682247084128153)
        ·
          refine ⟨1765510544761685313096115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2354014059682247084128153 1765510544761685313096115)
          ·
            refine ⟨2648265817142527969644173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765510544761685313096115 2648265817142527969644173)
            ·
              refine ⟨993099681428447988616565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2648265817142527969644173 993099681428447988616565)
              ·
                refine ⟨93103095133916998932803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 993099681428447988616565 93103095133916998932803)
                ·
                  rfl

theorem cell21_1223894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_1223894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223894 prefixEnd_1223894 := by exact prefixLift 1223894
  have htrace : WordTrace (prefixWord ++ tailWord_1223894) baseStart_1223894 baseEnd_1223894 := by
    simpa [prefixWord, tailWord_1223894, baseEnd_1223894] using wordTrace_append hprefix tailTrace_1223894
  have hstable : (prefixWord ++ tailWord_1223894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223894).length < 2 ^ (prefixWord ++ tailWord_1223894).sum := by decide
  have hdescent : baseEnd_1223894 < baseStart_1223894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223919 : List Nat := [1, 1, 2, 1, 7, 1, 8]
def baseStart_1223919 : Nat := 118140960795 + 1223919 * 2 ^ 59
def prefixEnd_1223919 : Nat := 4983230072969 + 3 ^ 40 * 1223919 * 2
def baseEnd_1223919 : Nat := 31034998971372945431299

theorem tailTrace_1223919 : CollatzResearch.WordTrace tailWord_1223919 prefixEnd_1223919 31034998971372945431299 := by
  unfold tailWord_1223919
  simp only [CollatzResearch.WordTrace]
  refine ⟨44639993252957966568682811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29759995501971977712455207 44639993252957966568682811)
  ·
    refine ⟨66959989879436949853024217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44639993252957966568682811 66959989879436949853024217)
    ·
      refine ⟨50219992409577712389768163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66959989879436949853024217 50219992409577712389768163)
      ·
        refine ⟨75329988614366568584652245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50219992409577712389768163 75329988614366568584652245)
        ·
          refine ⟨1765546608149216451202787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 75329988614366568584652245 1765546608149216451202787)
          ·
            refine ⟨2648319912223824676804181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765546608149216451202787 2648319912223824676804181)
            ·
              refine ⟨31034998971372945431299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2648319912223824676804181 31034998971372945431299)
              ·
                rfl

theorem cell21_1223919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 8].length) (baseStart_1223919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223919 prefixEnd_1223919 := by exact prefixLift 1223919
  have htrace : WordTrace (prefixWord ++ tailWord_1223919) baseStart_1223919 baseEnd_1223919 := by
    simpa [prefixWord, tailWord_1223919, baseEnd_1223919] using wordTrace_append hprefix tailTrace_1223919
  have hstable : (prefixWord ++ tailWord_1223919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223919).length < 2 ^ (prefixWord ++ tailWord_1223919).sum := by decide
  have hdescent : baseEnd_1223919 < baseStart_1223919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223950 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_1223950 : Nat := 118140960795 + 1223950 * 2 ^ 59
def prefixEnd_1223950 : Nat := 4983230072969 + 3 ^ 40 * 1223950 * 2
def baseEnd_1223950 : Nat := 279322065364707343864961

theorem tailTrace_1223950 : CollatzResearch.WordTrace tailWord_1223950 prefixEnd_1223950 279322065364707343864961 := by
  unfold tailWord_1223950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5580140489480707357882663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29760749277230439242040869 5580140489480707357882663)
  ·
    refine ⟨8370210734221061036823995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5580140489480707357882663 8370210734221061036823995)
    ·
      refine ⟨12555316101331591555235993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8370210734221061036823995 12555316101331591555235993)
      ·
        refine ⟨9416487075998693666426995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12555316101331591555235993 9416487075998693666426995)
        ·
          refine ⟨14124730613998040499640493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9416487075998693666426995 14124730613998040499640493)
          ·
            refine ⟨5296773980249265187365185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14124730613998040499640493 5296773980249265187365185)
            ·
              refine ⟨3972580485186948890523889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5296773980249265187365185 3972580485186948890523889)
              ·
                refine ⟨2979435363890211667892917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3972580485186948890523889 2979435363890211667892917)
                ·
                  refine ⟨279322065364707343864961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2979435363890211667892917 279322065364707343864961)
                  ·
                    rfl

theorem cell21_1223950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_1223950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223950 prefixEnd_1223950 := by exact prefixLift 1223950
  have htrace : WordTrace (prefixWord ++ tailWord_1223950) baseStart_1223950 baseEnd_1223950 := by
    simpa [prefixWord, tailWord_1223950, baseEnd_1223950] using wordTrace_append hprefix tailTrace_1223950
  have hstable : (prefixWord ++ tailWord_1223950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223950).length < 2 ^ (prefixWord ++ tailWord_1223950).sum := by decide
  have hdescent : baseEnd_1223950 < baseStart_1223950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1223964 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_1223964 : Nat := 118140960795 + 1223964 * 2 ^ 59
def prefixEnd_1223964 : Nat := 4983230072969 + 3 ^ 40 * 1223964 * 2
def baseEnd_1223964 : Nat := 279325260355446430631599

theorem tailTrace_1223964 : CollatzResearch.WordTrace tailWord_1223964 prefixEnd_1223964 279325260355446430631599 := by
  unfold tailWord_1223964
  simp only [CollatzResearch.WordTrace]
  refine ⟨22320817268897469627035473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29761089691863292836047297 22320817268897469627035473)
  ·
    refine ⟨16740612951673102220276605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22320817268897469627035473 16740612951673102220276605)
    ·
      refine ⟨6277729856877413332603727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16740612951673102220276605 6277729856877413332603727)
      ·
        refine ⟨9416594785316119998905591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6277729856877413332603727 9416594785316119998905591)
        ·
          refine ⟨14124892177974179998358387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9416594785316119998905591 14124892177974179998358387)
          ·
            refine ⟨21187338266961269997537581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14124892177974179998358387 21187338266961269997537581)
            ·
              refine ⟨7945251850110476249076593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21187338266961269997537581 7945251850110476249076593)
              ·
                refine ⟨5958938887582857186807445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7945251850110476249076593 5958938887582857186807445)
                ·
                  refine ⟨279325260355446430631599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5958938887582857186807445 279325260355446430631599)
                  ·
                    rfl

theorem cell21_1223964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_1223964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1223964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1223964 prefixEnd_1223964 := by exact prefixLift 1223964
  have htrace : WordTrace (prefixWord ++ tailWord_1223964) baseStart_1223964 baseEnd_1223964 := by
    simpa [prefixWord, tailWord_1223964, baseEnd_1223964] using wordTrace_append hprefix tailTrace_1223964
  have hstable : (prefixWord ++ tailWord_1223964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1223964).length < 2 ^ (prefixWord ++ tailWord_1223964).sum := by decide
  have hdescent : baseEnd_1223964 < baseStart_1223964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1223964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224009 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 5]
def baseStart_1224009 : Nat := 118140960795 + 1224009 * 2 ^ 59
def prefixEnd_1224009 : Nat := 4983230072969 + 3 ^ 40 * 1224009 * 2
def baseEnd_1224009 : Nat := 279335529968536352381507

theorem tailTrace_1224009 : CollatzResearch.WordTrace tailWord_1224009 prefixEnd_1224009 279335529968536352381507 := by
  unfold tailWord_1224009
  simp only [CollatzResearch.WordTrace]
  refine ⟨44643275822631911939459081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29762183881754607959639387 44643275822631911939459081)
  ·
    refine ⟨33482456866973933954594311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44643275822631911939459081 33482456866973933954594311)
    ·
      refine ⟨50223685300460900931891467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33482456866973933954594311 50223685300460900931891467)
      ·
        refine ⟨75335527950691351397837201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50223685300460900931891467 75335527950691351397837201)
        ·
          refine ⟨56501645963018513548377901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75335527950691351397837201 56501645963018513548377901)
          ·
            refine ⟨21188117236131942580641713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56501645963018513548377901 21188117236131942580641713)
            ·
              refine ⟨15891087927098956935481285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21188117236131942580641713 15891087927098956935481285)
              ·
                refine ⟨2979578986331054425402741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15891087927098956935481285 2979578986331054425402741)
                ·
                  refine ⟨279335529968536352381507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2979578986331054425402741 279335529968536352381507)
                  ·
                    rfl

theorem cell21_1224009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_1224009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224009 prefixEnd_1224009 := by exact prefixLift 1224009
  have htrace : WordTrace (prefixWord ++ tailWord_1224009) baseStart_1224009 baseEnd_1224009 := by
    simpa [prefixWord, tailWord_1224009, baseEnd_1224009] using wordTrace_append hprefix tailTrace_1224009
  have hstable : (prefixWord ++ tailWord_1224009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224009).length < 2 ^ (prefixWord ++ tailWord_1224009).sum := by decide
  have hdescent : baseEnd_1224009 < baseStart_1224009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224029 : List Nat := [1, 4, 5, 1, 1, 9]
def baseStart_1224029 : Nat := 118140960795 + 1224029 * 2 ^ 59
def prefixEnd_1224029 : Nat := 4983230072969 + 3 ^ 40 * 1224029 * 2
def baseEnd_1224029 : Nat := 10345929416334102298079

theorem tailTrace_1224029 : CollatzResearch.WordTrace tailWord_1224029 prefixEnd_1224029 10345929416334102298079 := by
  unfold tailWord_1224029
  simp only [CollatzResearch.WordTrace]
  refine ⟨44644005282559455355187141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29762670188372970236791427 44644005282559455355187141)
  ·
    refine ⟨8370750990479897879097589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44644005282559455355187141 8370750990479897879097589)
    ·
      refine ⟨784757905357490426165399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8370750990479897879097589 784757905357490426165399)
      ·
        refine ⟨1177136858036235639248099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784757905357490426165399 1177136858036235639248099)
        ·
          refine ⟨1765705287054353458872149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1177136858036235639248099 1765705287054353458872149)
          ·
            refine ⟨10345929416334102298079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1765705287054353458872149 10345929416334102298079)
            ·
              rfl

theorem cell21_1224029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 9].length) (baseStart_1224029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224029 prefixEnd_1224029 := by exact prefixLift 1224029
  have htrace : WordTrace (prefixWord ++ tailWord_1224029) baseStart_1224029 baseEnd_1224029 := by
    simpa [prefixWord, tailWord_1224029, baseEnd_1224029] using wordTrace_append hprefix tailTrace_1224029
  have hstable : (prefixWord ++ tailWord_1224029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224029).length < 2 ^ (prefixWord ++ tailWord_1224029).sum := by decide
  have hdescent : baseEnd_1224029 < baseStart_1224029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224046 : List Nat := [4, 1, 2, 4, 2, 1, 1, 6]
def baseStart_1224046 : Nat := 118140960795 + 1224046 * 2 ^ 59
def prefixEnd_1224046 : Nat := 4983230072969 + 3 ^ 40 * 1224046 * 2
def baseEnd_1224046 : Nat := 93114657957544170088255

theorem tailTrace_1224046 : CollatzResearch.WordTrace tailWord_1224046 prefixEnd_1224046 93114657957544170088255 := by
  unfold tailWord_1224046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5580578165437233407319499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29763083548998578172370661 5580578165437233407319499)
  ·
    refine ⟨8370867248155850110979249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5580578165437233407319499 8370867248155850110979249)
    ·
      refine ⟨6278150436116887583234437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8370867248155850110979249 6278150436116887583234437)
      ·
        refine ⟨1177153206771916421856457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6278150436116887583234437 1177153206771916421856457)
        ·
          refine ⟨882864905078937316392343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1177153206771916421856457 882864905078937316392343)
          ·
            refine ⟨1324297357618405974588515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882864905078937316392343 1324297357618405974588515)
            ·
              refine ⟨1986446036427608961882773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324297357618405974588515 1986446036427608961882773)
              ·
                refine ⟨93114657957544170088255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1986446036427608961882773 93114657957544170088255)
                ·
                  rfl

theorem cell21_1224046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_1224046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224046 prefixEnd_1224046 := by exact prefixLift 1224046
  have htrace : WordTrace (prefixWord ++ tailWord_1224046) baseStart_1224046 baseEnd_1224046 := by
    simpa [prefixWord, tailWord_1224046, baseEnd_1224046] using wordTrace_append hprefix tailTrace_1224046
  have hstable : (prefixWord ++ tailWord_1224046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224046).length < 2 ^ (prefixWord ++ tailWord_1224046).sum := by decide
  have hdescent : baseEnd_1224046 < baseStart_1224046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224198 : List Nat := [6, 2, 1, 1, 3, 8]
def baseStart_1224198 : Nat := 118140960795 + 1224198 * 2 ^ 59
def prefixEnd_1224198 : Nat := 4983230072969 + 3 ^ 40 * 1224198 * 2
def baseEnd_1224198 : Nat := 10347357864574593471523

theorem tailTrace_1224198 : CollatzResearch.WordTrace tailWord_1224198 prefixEnd_1224198 10347357864574593471523 := by
  unfold tailWord_1224198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1395317788092099913065289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29766779479298131478726165 1395317788092099913065289)
  ·
    refine ⟨1046488341069074934798967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1395317788092099913065289 1046488341069074934798967)
    ·
      refine ⟨1569732511603612402198451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1046488341069074934798967 1569732511603612402198451)
      ·
        refine ⟨2354598767405418603297677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569732511603612402198451 2354598767405418603297677)
        ·
          refine ⟨882974537777031976236629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2354598767405418603297677 882974537777031976236629)
          ·
            refine ⟨10347357864574593471523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 882974537777031976236629 10347357864574593471523)
            ·
              rfl

theorem cell21_1224198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 8].length) (baseStart_1224198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224198 prefixEnd_1224198 := by exact prefixLift 1224198
  have htrace : WordTrace (prefixWord ++ tailWord_1224198) baseStart_1224198 baseEnd_1224198 := by
    simpa [prefixWord, tailWord_1224198, baseEnd_1224198] using wordTrace_append hprefix tailTrace_1224198
  have hstable : (prefixWord ++ tailWord_1224198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224198).length < 2 ^ (prefixWord ++ tailWord_1224198).sum := by decide
  have hdescent : baseEnd_1224198 < baseStart_1224198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224206 : List Nat := [4, 1, 1, 2, 13]
def baseStart_1224206 : Nat := 118140960795 + 1224206 * 2 ^ 59
def prefixEnd_1224206 : Nat := 4983230072969 + 3 ^ 40 * 1224206 * 2
def baseEnd_1224206 : Nat := 3449141827808738118491

theorem tailTrace_1224206 : CollatzResearch.WordTrace tailWord_1224206 prefixEnd_1224206 3449141827808738118491 := by
  unfold tailWord_1224206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5581307625364776823047559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29766974001945476389586981 5581307625364776823047559)
  ·
    refine ⟨8371961438047165234571339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5581307625364776823047559 8371961438047165234571339)
    ·
      refine ⟨12557942157070747851857009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8371961438047165234571339 12557942157070747851857009)
      ·
        refine ⟨9418456617803060888892757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12557942157070747851857009 9418456617803060888892757)
        ·
          refine ⟨3449141827808738118491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9418456617803060888892757 3449141827808738118491)
          ·
            rfl

theorem cell21_1224206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 13].length) (baseStart_1224206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224206 prefixEnd_1224206 := by exact prefixLift 1224206
  have htrace : WordTrace (prefixWord ++ tailWord_1224206) baseStart_1224206 baseEnd_1224206 := by
    simpa [prefixWord, tailWord_1224206, baseEnd_1224206] using wordTrace_append hprefix tailTrace_1224206
  have hstable : (prefixWord ++ tailWord_1224206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224206).length < 2 ^ (prefixWord ++ tailWord_1224206).sum := by decide
  have hdescent : baseEnd_1224206 < baseStart_1224206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224268 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 6]
def baseStart_1224268 : Nat := 118140960795 + 1224268 * 2 ^ 59
def prefixEnd_1224268 : Nat := 4983230072969 + 3 ^ 40 * 1224268 * 2
def baseEnd_1224268 : Nat := 279394637297209457564311

theorem tailTrace_1224268 : CollatzResearch.WordTrace tailWord_1224268 prefixEnd_1224268 279394637297209457564311 := by
  unfold tailWord_1224268
  simp only [CollatzResearch.WordTrace]
  refine ⟨22326361164346799586568729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29768481552462399448758305 22326361164346799586568729)
  ·
    refine ⟨16744770873260099689926547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22326361164346799586568729 16744770873260099689926547)
    ·
      refine ⟨25117156309890149534889821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16744770873260099689926547 25117156309890149534889821)
      ·
        refine ⟨9418933616208806075583683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25117156309890149534889821 9418933616208806075583683)
        ·
          refine ⟨14128400424313209113375525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9418933616208806075583683 14128400424313209113375525)
          ·
            refine ⟨2649075079558726708757911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14128400424313209113375525 2649075079558726708757911)
            ·
              refine ⟨3973612619338090063136867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649075079558726708757911 3973612619338090063136867)
              ·
                refine ⟨5960418929007135094705301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3973612619338090063136867 5960418929007135094705301)
                ·
                  refine ⟨279394637297209457564311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5960418929007135094705301 279394637297209457564311)
                  ·
                    rfl

theorem cell21_1224268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_1224268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224268 prefixEnd_1224268 := by exact prefixLift 1224268
  have htrace : WordTrace (prefixWord ++ tailWord_1224268) baseStart_1224268 baseEnd_1224268 := by
    simpa [prefixWord, tailWord_1224268, baseEnd_1224268] using wordTrace_append hprefix tailTrace_1224268
  have hstable : (prefixWord ++ tailWord_1224268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224268).length < 2 ^ (prefixWord ++ tailWord_1224268).sum := by decide
  have hdescent : baseEnd_1224268 < baseStart_1224268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224330 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_1224330 : Nat := 118140960795 + 1224330 * 2 ^ 59
def prefixEnd_1224330 : Nat := 4983230072969 + 3 ^ 40 * 1224330 * 2
def baseEnd_1224330 : Nat := 279408786541911127530851

theorem tailTrace_1224330 : CollatzResearch.WordTrace tailWord_1224330 prefixEnd_1224330 279408786541911127530851 := by
  unfold tailWord_1224330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11163745913617245940473611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29769989102979322507929629 11163745913617245940473611)
  ·
    refine ⟨16745618870425868910710417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11163745913617245940473611 16745618870425868910710417)
    ·
      refine ⟨12559214152819401683032813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16745618870425868910710417 12559214152819401683032813)
      ·
        refine ⟨4709705307307275631137305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12559214152819401683032813 4709705307307275631137305)
        ·
          refine ⟨3532278980480456723352979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4709705307307275631137305 3532278980480456723352979)
          ·
            refine ⟨5298418470720685085029469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3532278980480456723352979 5298418470720685085029469)
            ·
              refine ⟨1986906926520256906886051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5298418470720685085029469 1986906926520256906886051)
              ·
                refine ⟨2980360389780385360329077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1986906926520256906886051 2980360389780385360329077)
                ·
                  refine ⟨279408786541911127530851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2980360389780385360329077 279408786541911127530851)
                  ·
                    rfl

theorem cell21_1224330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_1224330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224330 prefixEnd_1224330 := by exact prefixLift 1224330
  have htrace : WordTrace (prefixWord ++ tailWord_1224330) baseStart_1224330 baseEnd_1224330 := by
    simpa [prefixWord, tailWord_1224330, baseEnd_1224330] using wordTrace_append hprefix tailTrace_1224330
  have hstable : (prefixWord ++ tailWord_1224330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224330).length < 2 ^ (prefixWord ++ tailWord_1224330).sum := by decide
  have hdescent : baseEnd_1224330 < baseStart_1224330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224434 : List Nat := [3, 2, 1, 3, 1, 1, 10]
def baseStart_1224434 : Nat := 118140960795 + 1224434 * 2 ^ 59
def prefixEnd_1224434 : Nat := 4983230072969 + 3 ^ 40 * 1224434 * 2
def baseEnd_1224434 : Nat := 31048057862092228644145

theorem tailTrace_1224434 : CollatzResearch.WordTrace tailWord_1224434 prefixEnd_1224434 31048057862092228644145 := by
  unfold tailWord_1224434
  simp only [CollatzResearch.WordTrace]
  refine ⟨11164694211523052380920089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29772517897394806349120237 11164694211523052380920089)
  ·
    refine ⟨8373520658642289285690067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11164694211523052380920089 8373520658642289285690067)
    ·
      refine ⟨12560280987963433928535101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8373520658642289285690067 12560280987963433928535101)
      ·
        refine ⟨4710105370486287723200663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12560280987963433928535101 4710105370486287723200663)
        ·
          refine ⟨7065158055729431584800995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4710105370486287723200663 7065158055729431584800995)
          ·
            refine ⟨10597737083594147377201493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7065158055729431584800995 10597737083594147377201493)
            ·
              refine ⟨31048057862092228644145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10597737083594147377201493 31048057862092228644145)
              ·
                rfl

theorem cell21_1224434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 10].length) (baseStart_1224434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224434 prefixEnd_1224434 := by exact prefixLift 1224434
  have htrace : WordTrace (prefixWord ++ tailWord_1224434) baseStart_1224434 baseEnd_1224434 := by
    simpa [prefixWord, tailWord_1224434, baseEnd_1224434] using wordTrace_append hprefix tailTrace_1224434
  have hstable : (prefixWord ++ tailWord_1224434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224434).length < 2 ^ (prefixWord ++ tailWord_1224434).sum := by decide
  have hdescent : baseEnd_1224434 < baseStart_1224434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224448 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 9]
def baseStart_1224448 : Nat := 118140960795 + 1224448 * 2 ^ 59
def prefixEnd_1224448 : Nat := 4983230072969 + 3 ^ 40 * 1224448 * 2
def baseEnd_1224448 : Nat := 279435715749569144563943

theorem tailTrace_1224448 : CollatzResearch.WordTrace tailWord_1224448 prefixEnd_1224448 279435715749569144563943 := by
  unfold tailWord_1224448
  simp only [CollatzResearch.WordTrace]
  refine ⟨22329643734020744957344999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29772858312027659943126665 22329643734020744957344999)
  ·
    refine ⟨33494465601031117436017499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22329643734020744957344999 33494465601031117436017499)
    ·
      refine ⟨50241698401546676154026249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33494465601031117436017499 50241698401546676154026249)
      ·
        refine ⟨37681273801160007115519687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50241698401546676154026249 37681273801160007115519687)
        ·
          refine ⟨56521910701740010673279531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37681273801160007115519687 56521910701740010673279531)
          ·
            refine ⟨84782866052610016009919297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56521910701740010673279531 84782866052610016009919297)
            ·
              refine ⟨63587149539457512007439473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84782866052610016009919297 63587149539457512007439473)
              ·
                refine ⟨47690362154593134005579605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63587149539457512007439473 47690362154593134005579605)
                ·
                  refine ⟨279435715749569144563943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47690362154593134005579605 279435715749569144563943)
                  ·
                    rfl

theorem cell21_1224448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_1224448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224448 prefixEnd_1224448 := by exact prefixLift 1224448
  have htrace : WordTrace (prefixWord ++ tailWord_1224448) baseStart_1224448 baseEnd_1224448 := by
    simpa [prefixWord, tailWord_1224448, baseEnd_1224448] using wordTrace_append hprefix tailTrace_1224448
  have hstable : (prefixWord ++ tailWord_1224448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224448).length < 2 ^ (prefixWord ++ tailWord_1224448).sum := by decide
  have hdescent : baseEnd_1224448 < baseStart_1224448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224479 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 8]
def baseStart_1224479 : Nat := 118140960795 + 1224479 * 2 ^ 59
def prefixEnd_1224479 : Nat := 4983230072969 + 3 ^ 40 * 1224479 * 2
def baseEnd_1224479 : Nat := 279442790371919979547213

theorem tailTrace_1224479 : CollatzResearch.WordTrace tailWord_1224479 prefixEnd_1224479 279442790371919979547213 := by
  unfold tailWord_1224479
  simp only [CollatzResearch.WordTrace]
  refine ⟨44660418130929182209068491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29773612087286121472712327 44660418130929182209068491)
  ·
    refine ⟨66990627196393773313602737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44660418130929182209068491 66990627196393773313602737)
    ·
      refine ⟨50242970397295329985202053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66990627196393773313602737 50242970397295329985202053)
      ·
        refine ⟨9420556949492874372225385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50242970397295329985202053 9420556949492874372225385)
        ·
          refine ⟨7065417712119655779169039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9420556949492874372225385 7065417712119655779169039)
          ·
            refine ⟨10598126568179483668753559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7065417712119655779169039 10598126568179483668753559)
            ·
              refine ⟨15897189852269225503130339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10598126568179483668753559 15897189852269225503130339)
              ·
                refine ⟨23845784778403838254695509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15897189852269225503130339 23845784778403838254695509)
                ·
                  refine ⟨279442790371919979547213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23845784778403838254695509 279442790371919979547213)
                  ·
                    rfl

theorem cell21_1224479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_1224479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224479 prefixEnd_1224479 := by exact prefixLift 1224479
  have htrace : WordTrace (prefixWord ++ tailWord_1224479) baseStart_1224479 baseEnd_1224479 := by
    simpa [prefixWord, tailWord_1224479, baseEnd_1224479] using wordTrace_append hprefix tailTrace_1224479
  have hstable : (prefixWord ++ tailWord_1224479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224479).length < 2 ^ (prefixWord ++ tailWord_1224479).sum := by decide
  have hdescent : baseEnd_1224479 < baseStart_1224479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224499 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 5]
def baseStart_1224499 : Nat := 118140960795 + 1224499 * 2 ^ 59
def prefixEnd_1224499 : Nat := 4983230072969 + 3 ^ 40 * 1224499 * 2
def baseEnd_1224499 : Nat := 279447354644404389213839

theorem tailTrace_1224499 : CollatzResearch.WordTrace tailWord_1224499 prefixEnd_1224499 279447354644404389213839 := by
  unfold tailWord_1224499
  simp only [CollatzResearch.WordTrace]
  refine ⟨44661147590856725624796551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29774098393904483749864367 44661147590856725624796551)
  ·
    refine ⟨66991721386285088437194827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44661147590856725624796551 66991721386285088437194827)
    ·
      refine ⟨100487582079427632655792241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66991721386285088437194827 100487582079427632655792241)
      ·
        refine ⟨75365686559570724491844181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100487582079427632655792241 75365686559570724491844181)
        ·
          refine ⟨883191639369969427638799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 75365686559570724491844181 883191639369969427638799)
          ·
            refine ⟨1324787459054954141458199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883191639369969427638799 1324787459054954141458199)
            ·
              refine ⟨1987181188582431212187299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324787459054954141458199 1987181188582431212187299)
              ·
                refine ⟨2980771782873646818280949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987181188582431212187299 2980771782873646818280949)
                ·
                  refine ⟨279447354644404389213839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2980771782873646818280949 279447354644404389213839)
                  ·
                    rfl

theorem cell21_1224499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 5].length) (baseStart_1224499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224499 prefixEnd_1224499 := by exact prefixLift 1224499
  have htrace : WordTrace (prefixWord ++ tailWord_1224499) baseStart_1224499 baseEnd_1224499 := by
    simpa [prefixWord, tailWord_1224499, baseEnd_1224499] using wordTrace_append hprefix tailTrace_1224499
  have hstable : (prefixWord ++ tailWord_1224499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224499).length < 2 ^ (prefixWord ++ tailWord_1224499).sum := by decide
  have hdescent : baseEnd_1224499 < baseStart_1224499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224606 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1224606 : Nat := 118140960795 + 1224606 * 2 ^ 59
def prefixEnd_1224606 : Nat := 4983230072969 + 3 ^ 40 * 1224606 * 2
def baseEnd_1224606 : Nat := 279471773502195980930287

theorem tailTrace_1224606 : CollatzResearch.WordTrace tailWord_1224606 prefixEnd_1224606 279471773502195980930287 := by
  unfold tailWord_1224606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5583131275183635362367709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29776700134312721932627781 5583131275183635362367709)
  ·
    refine ⟨2093674228193863260887891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5583131275183635362367709 2093674228193863260887891)
    ·
      refine ⟨3140511342290794891331837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2093674228193863260887891 3140511342290794891331837)
      ·
        refine ⟨1177691753359048084249439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3140511342290794891331837 1177691753359048084249439)
        ·
          refine ⟨1766537630038572126374159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1177691753359048084249439 1766537630038572126374159)
          ·
            refine ⟨2649806445057858189561239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766537630038572126374159 2649806445057858189561239)
            ·
              refine ⟨3974709667586787284341859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649806445057858189561239 3974709667586787284341859)
              ·
                refine ⟨5962064501380180926512789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974709667586787284341859 5962064501380180926512789)
                ·
                  refine ⟨279471773502195980930287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5962064501380180926512789 279471773502195980930287)
                  ·
                    rfl

theorem cell21_1224606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1224606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224606 prefixEnd_1224606 := by exact prefixLift 1224606
  have htrace : WordTrace (prefixWord ++ tailWord_1224606) baseStart_1224606 baseEnd_1224606 := by
    simpa [prefixWord, tailWord_1224606, baseEnd_1224606] using wordTrace_append hprefix tailTrace_1224606
  have hstable : (prefixWord ++ tailWord_1224606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224606).length < 2 ^ (prefixWord ++ tailWord_1224606).sum := by decide
  have hdescent : baseEnd_1224606 < baseStart_1224606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224679 : List Nat := [1, 1, 5, 2, 3, 1, 2, 6]
def baseStart_1224679 : Nat := 118140960795 + 1224679 * 2 ^ 59
def prefixEnd_1224679 : Nat := 4983230072969 + 3 ^ 40 * 1224679 * 2
def baseEnd_1224679 : Nat := 93162811032254692071157

theorem tailTrace_1224679 : CollatzResearch.WordTrace tailWord_1224679 prefixEnd_1224679 93162811032254692071157 := by
  unfold tailWord_1224679
  simp only [CollatzResearch.WordTrace]
  refine ⟨44667712730204616366349091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29778475153469744244232727 44667712730204616366349091)
  ·
    refine ⟨67001569095306924549523637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44667712730204616366349091 67001569095306924549523637)
    ·
      refine ⟨6281397102685024176517841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67001569095306924549523637 6281397102685024176517841)
      ·
        refine ⟨4711047827013768132388381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6281397102685024176517841 4711047827013768132388381)
        ·
          refine ⟨1766642935130163049645643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4711047827013768132388381 1766642935130163049645643)
          ·
            refine ⟨2649964402695244574468465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766642935130163049645643 2649964402695244574468465)
            ·
              refine ⟨1987473302021433430851349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2649964402695244574468465 1987473302021433430851349)
              ·
                refine ⟨93162811032254692071157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1987473302021433430851349 93162811032254692071157)
                ·
                  rfl

theorem cell21_1224679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 6].length) (baseStart_1224679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224679 prefixEnd_1224679 := by exact prefixLift 1224679
  have htrace : WordTrace (prefixWord ++ tailWord_1224679) baseStart_1224679 baseEnd_1224679 := by
    simpa [prefixWord, tailWord_1224679, baseEnd_1224679] using wordTrace_append hprefix tailTrace_1224679
  have hstable : (prefixWord ++ tailWord_1224679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224679).length < 2 ^ (prefixWord ++ tailWord_1224679).sum := by decide
  have hdescent : baseEnd_1224679 < baseStart_1224679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224727 : List Nat := [1, 1, 3, 5, 2, 1, 1, 4, 3]
def baseStart_1224727 : Nat := 118140960795 + 1224727 * 2 ^ 59
def prefixEnd_1224727 : Nat := 4983230072969 + 3 ^ 40 * 1224727 * 2
def baseEnd_1224727 : Nat := 279499387350726659413373

theorem tailTrace_1224727 : CollatzResearch.WordTrace tailWord_1224727 prefixEnd_1224727 279499387350726659413373 := by
  unfold tailWord_1224727
  simp only [CollatzResearch.WordTrace]
  refine ⟨44669463434030720564096435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29779642289353813709397623 44669463434030720564096435)
  ·
    refine ⟨67004195151046080846144653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44669463434030720564096435 67004195151046080846144653)
    ·
      refine ⟨25126573181642280317304245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67004195151046080846144653 25126573181642280317304245)
      ·
        refine ⟨2355616235778963779747273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25126573181642280317304245 2355616235778963779747273)
        ·
          refine ⟨1766712176834222834810455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2355616235778963779747273 1766712176834222834810455)
          ·
            refine ⟨2650068265251334252215683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766712176834222834810455 2650068265251334252215683)
            ·
              refine ⟨3975102397877001378323525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650068265251334252215683 3975102397877001378323525)
              ·
                refine ⟨745331699601937758435661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3975102397877001378323525 745331699601937758435661)
                ·
                  refine ⟨279499387350726659413373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745331699601937758435661 279499387350726659413373)
                  ·
                    rfl

theorem cell21_1224727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 4, 3].length) (baseStart_1224727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224727 prefixEnd_1224727 := by exact prefixLift 1224727
  have htrace : WordTrace (prefixWord ++ tailWord_1224727) baseStart_1224727 baseEnd_1224727 := by
    simpa [prefixWord, tailWord_1224727, baseEnd_1224727] using wordTrace_append hprefix tailTrace_1224727
  have hstable : (prefixWord ++ tailWord_1224727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224727).length < 2 ^ (prefixWord ++ tailWord_1224727).sum := by decide
  have hdescent : baseEnd_1224727 < baseStart_1224727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224752 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_1224752 : Nat := 118140960795 + 1224752 * 2 ^ 59
def prefixEnd_1224752 : Nat := 4983230072969 + 3 ^ 40 * 1224752 * 2
def baseEnd_1224752 : Nat := 279505092691332171496655

theorem tailTrace_1224752 : CollatzResearch.WordTrace tailWord_1224752 prefixEnd_1224752 279505092691332171496655 := by
  unfold tailWord_1224752
  simp only [CollatzResearch.WordTrace]
  refine ⟨22335187629470074916878255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29780250172626766555837673 22335187629470074916878255)
  ·
    refine ⟨33502781444205112375317383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22335187629470074916878255 33502781444205112375317383)
    ·
      refine ⟨50254172166307668562976075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33502781444205112375317383 50254172166307668562976075)
      ·
        refine ⟨75381258249461502844464113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50254172166307668562976075 75381258249461502844464113)
        ·
          refine ⟨56535943687096127133348085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75381258249461502844464113 56535943687096127133348085)
          ·
            refine ⟨5300244720665261918751383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56535943687096127133348085 5300244720665261918751383)
            ·
              refine ⟨7950367080997892878127075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5300244720665261918751383 7950367080997892878127075)
              ·
                refine ⟨11925550621496839317190613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7950367080997892878127075 11925550621496839317190613)
                ·
                  refine ⟨279505092691332171496655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11925550621496839317190613 279505092691332171496655)
                  ·
                    rfl

theorem cell21_1224752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_1224752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224752 prefixEnd_1224752 := by exact prefixLift 1224752
  have htrace : WordTrace (prefixWord ++ tailWord_1224752) baseStart_1224752 baseEnd_1224752 := by
    simpa [prefixWord, tailWord_1224752, baseEnd_1224752] using wordTrace_append hprefix tailTrace_1224752
  have hstable : (prefixWord ++ tailWord_1224752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224752).length < 2 ^ (prefixWord ++ tailWord_1224752).sum := by decide
  have hdescent : baseEnd_1224752 < baseStart_1224752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224786 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_1224786 : Nat := 118140960795 + 1224786 * 2 ^ 59
def prefixEnd_1224786 : Nat := 4983230072969 + 3 ^ 40 * 1224786 * 2
def baseEnd_1224786 : Nat := 279512851954555667929919

theorem tailTrace_1224786 : CollatzResearch.WordTrace tailWord_1224786 prefixEnd_1224786 279512851954555667929919 := by
  unfold tailWord_1224786
  simp only [CollatzResearch.WordTrace]
  refine ⟨11167903835204243410123553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29781076893877982426996141 11167903835204243410123553)
  ·
    refine ⟨8375927876403182557592665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11167903835204243410123553 8375927876403182557592665)
    ·
      refine ⟨6281945907302386918194499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8375927876403182557592665 6281945907302386918194499)
      ·
        refine ⟨9422918860953580377291749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6281945907302386918194499 9422918860953580377291749)
        ·
          refine ⟨1766797286428796320742203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9422918860953580377291749 1766797286428796320742203)
          ·
            refine ⟨2650195929643194481113305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766797286428796320742203 2650195929643194481113305)
            ·
              refine ⟨1987646947232395860834979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2650195929643194481113305 1987646947232395860834979)
              ·
                refine ⟨2981470420848593791252469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987646947232395860834979 2981470420848593791252469)
                ·
                  refine ⟨279512851954555667929919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2981470420848593791252469 279512851954555667929919)
                  ·
                    rfl

theorem cell21_1224786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_1224786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224786 prefixEnd_1224786 := by exact prefixLift 1224786
  have htrace : WordTrace (prefixWord ++ tailWord_1224786) baseStart_1224786 baseEnd_1224786 := by
    simpa [prefixWord, tailWord_1224786, baseEnd_1224786] using wordTrace_append hprefix tailTrace_1224786
  have hstable : (prefixWord ++ tailWord_1224786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224786).length < 2 ^ (prefixWord ++ tailWord_1224786).sum := by decide
  have hdescent : baseEnd_1224786 < baseStart_1224786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224814 : List Nat := [4, 1, 2, 2, 1, 1, 3, 7]
def baseStart_1224814 : Nat := 118140960795 + 1224814 * 2 ^ 59
def prefixEnd_1224814 : Nat := 4983230072969 + 3 ^ 40 * 1224814 * 2
def baseEnd_1224814 : Nat := 93173080645344613821065

theorem tailTrace_1224814 : CollatzResearch.WordTrace tailWord_1224814 prefixEnd_1224814 93173080645344613821065 := by
  unfold tailWord_1224814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5584079573089441802814187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29781757723143689615008997 5584079573089441802814187)
  ·
    refine ⟨8376119359634162704221281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5584079573089441802814187 8376119359634162704221281)
    ·
      refine ⟨6282089519725622028165961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8376119359634162704221281 6282089519725622028165961)
      ·
        refine ⟨4711567139794216521124471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6282089519725622028165961 4711567139794216521124471)
        ·
          refine ⟨7067350709691324781686707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4711567139794216521124471 7067350709691324781686707)
          ·
            refine ⟨10601026064536987172530061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7067350709691324781686707 10601026064536987172530061)
            ·
              refine ⟨3975384774201370189698773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10601026064536987172530061 3975384774201370189698773)
              ·
                refine ⟨93173080645344613821065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3975384774201370189698773 93173080645344613821065)
                ·
                  rfl

theorem cell21_1224814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_1224814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224814 prefixEnd_1224814 := by exact prefixLift 1224814
  have htrace : WordTrace (prefixWord ++ tailWord_1224814) baseStart_1224814 baseEnd_1224814 := by
    simpa [prefixWord, tailWord_1224814, baseEnd_1224814] using wordTrace_append hprefix tailTrace_1224814
  have hstable : (prefixWord ++ tailWord_1224814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224814).length < 2 ^ (prefixWord ++ tailWord_1224814).sum := by decide
  have hdescent : baseEnd_1224814 < baseStart_1224814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224904 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_1224904 : Nat := 118140960795 + 1224904 * 2 ^ 59
def prefixEnd_1224904 : Nat := 4983230072969 + 3 ^ 40 * 1224904 * 2
def baseEnd_1224904 : Nat := 279539781162213684963011

theorem tailTrace_1224904 : CollatzResearch.WordTrace tailWord_1224904 prefixEnd_1224904 279539781162213684963011 := by
  unfold tailWord_1224904
  simp only [CollatzResearch.WordTrace]
  refine ⟨22337959577194739896644883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29783946102926319862193177 22337959577194739896644883)
  ·
    refine ⟨33506939365792109844967325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22337959577194739896644883 33506939365792109844967325)
    ·
      refine ⟨12565102262172041191862747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33506939365792109844967325 12565102262172041191862747)
      ·
        refine ⟨18847653393258061787794121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12565102262172041191862747 18847653393258061787794121)
        ·
          refine ⟨14135740044943546340845591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18847653393258061787794121 14135740044943546340845591)
          ·
            refine ⟨21203610067415319511268387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14135740044943546340845591 21203610067415319511268387)
            ·
              refine ⟨31805415101122979266902581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21203610067415319511268387 31805415101122979266902581)
              ·
                refine ⟨2981757665730279306272117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31805415101122979266902581 2981757665730279306272117)
                ·
                  refine ⟨279539781162213684963011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2981757665730279306272117 279539781162213684963011)
                  ·
                    rfl

theorem cell21_1224904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_1224904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224904 prefixEnd_1224904 := by exact prefixLift 1224904
  have htrace : WordTrace (prefixWord ++ tailWord_1224904) baseStart_1224904 baseEnd_1224904 := by
    simpa [prefixWord, tailWord_1224904, baseEnd_1224904] using wordTrace_append hprefix tailTrace_1224904
  have hstable : (prefixWord ++ tailWord_1224904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224904).length < 2 ^ (prefixWord ++ tailWord_1224904).sum := by decide
  have hdescent : baseEnd_1224904 < baseStart_1224904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224938 : List Nat := [3, 1, 3, 1, 1, 2, 4, 3, 3]
def baseStart_1224938 : Nat := 118140960795 + 1224938 * 2 ^ 59
def prefixEnd_1224938 : Nat := 4983230072969 + 3 ^ 40 * 1224938 * 2
def baseEnd_1224938 : Nat := 279547540425437181396275

theorem tailTrace_1224938 : CollatzResearch.WordTrace tailWord_1224938 prefixEnd_1224938 279547540425437181396275 := by
  unfold tailWord_1224938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11169289809066575900006867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29784772824177535733351645 11169289809066575900006867)
  ·
    refine ⟨16753934713599863850010301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11169289809066575900006867 16753934713599863850010301)
    ·
      refine ⟨6282725517599948943753863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16753934713599863850010301 6282725517599948943753863)
      ·
        refine ⟨9424088276399923415630795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6282725517599948943753863 9424088276399923415630795)
        ·
          refine ⟨14136132414599885123446193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9424088276399923415630795 14136132414599885123446193)
          ·
            refine ⟨10602099310949913842584645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14136132414599885123446193 10602099310949913842584645)
            ·
              refine ⟨1987893620803108845484621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10602099310949913842584645 1987893620803108845484621)
              ·
                refine ⟨745460107801165817056733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1987893620803108845484621 745460107801165817056733)
                ·
                  refine ⟨279547540425437181396275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745460107801165817056733 279547540425437181396275)
                  ·
                    rfl

theorem cell21_1224938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_1224938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224938 prefixEnd_1224938 := by exact prefixLift 1224938
  have htrace : WordTrace (prefixWord ++ tailWord_1224938) baseStart_1224938 baseEnd_1224938 := by
    simpa [prefixWord, tailWord_1224938, baseEnd_1224938] using wordTrace_append hprefix tailTrace_1224938
  have hstable : (prefixWord ++ tailWord_1224938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224938).length < 2 ^ (prefixWord ++ tailWord_1224938).sum := by decide
  have hdescent : baseEnd_1224938 < baseStart_1224938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1224983 : List Nat := [1, 1, 3, 4, 1, 4, 2, 5]
def baseStart_1224983 : Nat := 118140960795 + 1224983 * 2 ^ 59
def prefixEnd_1224983 : Nat := 4983230072969 + 3 ^ 40 * 1224983 * 2
def baseEnd_1224983 : Nat := 93185936679509034382061

theorem tailTrace_1224983 : CollatzResearch.WordTrace tailWord_1224983 prefixEnd_1224983 93185936679509034382061 := by
  unfold tailWord_1224983
  simp only [CollatzResearch.WordTrace]
  refine ⟨44678800521103276285415603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29785867014068850856943735 44678800521103276285415603)
  ·
    refine ⟨67018200781654914428123405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44678800521103276285415603 67018200781654914428123405)
    ·
      refine ⟨25131825293120592910546277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67018200781654914428123405 25131825293120592910546277)
      ·
        refine ⟨4712217242460111170727427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25131825293120592910546277 4712217242460111170727427)
        ·
          refine ⟨7068325863690166756091141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4712217242460111170727427 7068325863690166756091141)
          ·
            refine ⟨1325311099441906266767089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7068325863690166756091141 1325311099441906266767089)
            ·
              refine ⟨993983324581429700075317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1325311099441906266767089 993983324581429700075317)
              ·
                refine ⟨93185936679509034382061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 993983324581429700075317 93185936679509034382061)
                ·
                  rfl

theorem cell21_1224983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 5].length) (baseStart_1224983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1224983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1224983 prefixEnd_1224983 := by exact prefixLift 1224983
  have htrace : WordTrace (prefixWord ++ tailWord_1224983) baseStart_1224983 baseEnd_1224983 := by
    simpa [prefixWord, tailWord_1224983, baseEnd_1224983] using wordTrace_append hprefix tailTrace_1224983
  have hstable : (prefixWord ++ tailWord_1224983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1224983).length < 2 ^ (prefixWord ++ tailWord_1224983).sum := by decide
  have hdescent : baseEnd_1224983 < baseStart_1224983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1224983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225011 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 4]
def baseStart_1225011 : Nat := 118140960795 + 1225011 * 2 ^ 59
def prefixEnd_1225011 : Nat := 4983230072969 + 3 ^ 40 * 1225011 * 2
def baseEnd_1225011 : Nat := 279564200020005276679459

theorem tailTrace_1225011 : CollatzResearch.WordTrace tailWord_1225011 prefixEnd_1225011 279564200020005276679459 := by
  unfold tailWord_1225011
  simp only [CollatzResearch.WordTrace]
  refine ⟨44679821765001837067434887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29786547843334558044956591 44679821765001837067434887)
  ·
    refine ⟨67019732647502755601152331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44679821765001837067434887 67019732647502755601152331)
    ·
      refine ⟨100529598971254133401728497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67019732647502755601152331 100529598971254133401728497)
      ·
        refine ⟨75397199228440600051296373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100529598971254133401728497 75397199228440600051296373)
        ·
          refine ⟨7068487427666306254809035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75397199228440600051296373 7068487427666306254809035)
          ·
            refine ⟨10602731141499459382213553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7068487427666306254809035 10602731141499459382213553)
            ·
              refine ⟨7952048356124594536660165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10602731141499459382213553 7952048356124594536660165)
              ·
                refine ⟨1491009066773361475623781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7952048356124594536660165 1491009066773361475623781)
                ·
                  refine ⟨279564200020005276679459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1491009066773361475623781 279564200020005276679459)
                  ·
                    rfl

theorem cell21_1225011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 4].length) (baseStart_1225011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225011 prefixEnd_1225011 := by exact prefixLift 1225011
  have htrace : WordTrace (prefixWord ++ tailWord_1225011) baseStart_1225011 baseEnd_1225011 := by
    simpa [prefixWord, tailWord_1225011, baseEnd_1225011] using wordTrace_append hprefix tailTrace_1225011
  have hstable : (prefixWord ++ tailWord_1225011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225011).length < 2 ^ (prefixWord ++ tailWord_1225011).sum := by decide
  have hdescent : baseEnd_1225011 < baseStart_1225011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225194 : List Nat := [3, 1, 3, 1, 3, 2, 2, 6]
def baseStart_1225194 : Nat := 118140960795 + 1225194 * 2 ^ 59
def prefixEnd_1225194 : Nat := 4983230072969 + 3 ^ 40 * 1225194 * 2
def baseEnd_1225194 : Nat := 93201987704412541709695

theorem tailTrace_1225194 : CollatzResearch.WordTrace tailWord_1225194 prefixEnd_1225194 93201987704412541709695 := by
  unfold tailWord_1225194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11171624080834714830336659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29790997548892572880897757 11171624080834714830336659)
  ·
    refine ⟨16757436121252072245504989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11171624080834714830336659 16757436121252072245504989)
    ·
      refine ⟨6284038545469527092064371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16757436121252072245504989 6284038545469527092064371)
      ·
        refine ⟨9426057818204290638096557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6284038545469527092064371 9426057818204290638096557)
        ·
          refine ⟨3534771681826608989286209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9426057818204290638096557 3534771681826608989286209)
          ·
            refine ⟨2651078761369956741964657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3534771681826608989286209 2651078761369956741964657)
            ·
              refine ⟨1988309071027467556473493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2651078761369956741964657 1988309071027467556473493)
              ·
                refine ⟨93201987704412541709695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1988309071027467556473493 93201987704412541709695)
                ·
                  rfl

theorem cell21_1225194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_1225194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225194 prefixEnd_1225194 := by exact prefixLift 1225194
  have htrace : WordTrace (prefixWord ++ tailWord_1225194) baseStart_1225194 baseEnd_1225194 := by
    simpa [prefixWord, tailWord_1225194, baseEnd_1225194] using wordTrace_append hprefix tailTrace_1225194
  have hstable : (prefixWord ++ tailWord_1225194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225194).length < 2 ^ (prefixWord ++ tailWord_1225194).sum := by decide
  have hdescent : baseEnd_1225194 < baseStart_1225194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225197 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 4]
def baseStart_1225197 : Nat := 118140960795 + 1225197 * 2 ^ 59
def prefixEnd_1225197 : Nat := 4983230072969 + 3 ^ 40 * 1225197 * 2
def baseEnd_1225197 : Nat := 279606647754110286579079

theorem tailTrace_1225197 : CollatzResearch.WordTrace tailWord_1225197 prefixEnd_1225197 279606647754110286579079 := by
  unfold tailWord_1225197
  simp only [CollatzResearch.WordTrace]
  refine ⟨44686605742327990833705845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29791070494885327222470563 44686605742327990833705845)
  ·
    refine ⟨4189369288343249140659923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44686605742327990833705845 4189369288343249140659923)
    ·
      refine ⟨6284053932514873710989885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4189369288343249140659923 6284053932514873710989885)
      ·
        refine ⟨2356520224693077641621207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6284053932514873710989885 2356520224693077641621207)
        ·
          refine ⟨3534780337039616462431811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356520224693077641621207 3534780337039616462431811)
          ·
            refine ⟨5302170505559424693647717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534780337039616462431811 5302170505559424693647717)
            ·
              refine ⟨994156969792392130058947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5302170505559424693647717 994156969792392130058947)
              ·
                refine ⟨1491235454688588195088421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994156969792392130058947 1491235454688588195088421)
                ·
                  refine ⟨279606647754110286579079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1491235454688588195088421 279606647754110286579079)
                  ·
                    rfl

theorem cell21_1225197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_1225197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225197 prefixEnd_1225197 := by exact prefixLift 1225197
  have htrace : WordTrace (prefixWord ++ tailWord_1225197) baseStart_1225197 baseEnd_1225197 := by
    simpa [prefixWord, tailWord_1225197, baseEnd_1225197] using wordTrace_append hprefix tailTrace_1225197
  have hstable : (prefixWord ++ tailWord_1225197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225197).length < 2 ^ (prefixWord ++ tailWord_1225197).sum := by decide
  have hdescent : baseEnd_1225197 < baseStart_1225197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225242 : List Nat := [3, 1, 1, 3, 1, 1, 6, 2, 3]
def baseStart_1225242 : Nat := 118140960795 + 1225242 * 2 ^ 59
def prefixEnd_1225242 : Nat := 4983230072969 + 3 ^ 40 * 1225242 * 2
def baseEnd_1225242 : Nat := 279616917367200208328987

theorem tailTrace_1225242 : CollatzResearch.WordTrace tailWord_1225242 prefixEnd_1225242 279616917367200208328987 := by
  unfold tailWord_1225242
  simp only [CollatzResearch.WordTrace]
  refine ⟨11172061756791240879773495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29792164684776642346062653 11172061756791240879773495)
  ·
    refine ⟨16758092635186861319660243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11172061756791240879773495 16758092635186861319660243)
    ·
      refine ⟨25137138952780291979490365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16758092635186861319660243 25137138952780291979490365)
      ·
        refine ⟨9426427107292609492308887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25137138952780291979490365 9426427107292609492308887)
        ·
          refine ⟨14139640660938914238463331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9426427107292609492308887 14139640660938914238463331)
          ·
            refine ⟨21209460991408371357694997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14139640660938914238463331 21209460991408371357694997)
            ·
              refine ⟨994193483972267407391953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21209460991408371357694997 994193483972267407391953)
              ·
                refine ⟨745645112979200555543965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 994193483972267407391953 745645112979200555543965)
                ·
                  refine ⟨279616917367200208328987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745645112979200555543965 279616917367200208328987)
                  ·
                    rfl

theorem cell21_1225242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_1225242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225242 prefixEnd_1225242 := by exact prefixLift 1225242
  have htrace : WordTrace (prefixWord ++ tailWord_1225242) baseStart_1225242 baseEnd_1225242 := by
    simpa [prefixWord, tailWord_1225242, baseEnd_1225242] using wordTrace_append hprefix tailTrace_1225242
  have hstable : (prefixWord ++ tailWord_1225242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225242).length < 2 ^ (prefixWord ++ tailWord_1225242).sum := by decide
  have hdescent : baseEnd_1225242 < baseStart_1225242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225253 : List Nat := [1, 3, 1, 2, 2, 1, 5, 6]
def baseStart_1225253 : Nat := 118140960795 + 1225253 * 2 ^ 59
def prefixEnd_1225253 : Nat := 4983230072969 + 3 ^ 40 * 1225253 * 2
def baseEnd_1225253 : Nat := 93206475905688877881877

theorem tailTrace_1225253 : CollatzResearch.WordTrace tailWord_1225253 prefixEnd_1225253 93206475905688877881877 := by
  unfold tailWord_1225253
  simp only [CollatzResearch.WordTrace]
  refine ⟨44688648230125112397744413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29792432153416741598496275 44688648230125112397744413)
  ·
    refine ⟨16758243086296917149154155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44688648230125112397744413 16758243086296917149154155)
    ·
      refine ⟨25137364629445375723731233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16758243086296917149154155 25137364629445375723731233)
      ·
        refine ⟨18853023472084031792798425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25137364629445375723731233 18853023472084031792798425)
        ·
          refine ⟨14139767604063023844598819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18853023472084031792798425 14139767604063023844598819)
          ·
            refine ⟨21209651406094535766898229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14139767604063023844598819 21209651406094535766898229)
            ·
              refine ⟨1988404819321362728146709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21209651406094535766898229 1988404819321362728146709)
              ·
                refine ⟨93206475905688877881877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1988404819321362728146709 93206475905688877881877)
                ·
                  rfl

theorem cell21_1225253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 6].length) (baseStart_1225253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225253 prefixEnd_1225253 := by exact prefixLift 1225253
  have htrace : WordTrace (prefixWord ++ tailWord_1225253) baseStart_1225253 baseEnd_1225253 := by
    simpa [prefixWord, tailWord_1225253, baseEnd_1225253] using wordTrace_append hprefix tailTrace_1225253
  have hstable : (prefixWord ++ tailWord_1225253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225253).length < 2 ^ (prefixWord ++ tailWord_1225253).sum := by decide
  have hdescent : baseEnd_1225253 < baseStart_1225253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225256 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 4]
def baseStart_1225256 : Nat := 118140960795 + 1225256 * 2 ^ 59
def prefixEnd_1225256 : Nat := 4983230072969 + 3 ^ 40 * 1225256 * 2
def baseEnd_1225256 : Nat := 279620112357939295095625

theorem tailTrace_1225256 : CollatzResearch.WordTrace tailWord_1225256 prefixEnd_1225256 279620112357939295095625 := by
  unfold tailWord_1225256
  simp only [CollatzResearch.WordTrace]
  refine ⟨22344378824557121955051811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29792505099409495940069081 22344378824557121955051811)
  ·
    refine ⟨33516568236835682932577717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22344378824557121955051811 33516568236835682932577717)
    ·
      refine ⟨3142178272203345274929161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33516568236835682932577717 3142178272203345274929161)
      ·
        refine ⟨2356633704152508956196871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3142178272203345274929161 2356633704152508956196871)
        ·
          refine ⟨3534950556228763434295307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356633704152508956196871 3534950556228763434295307)
          ·
            refine ⟨5302425834343145151442961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534950556228763434295307 5302425834343145151442961)
            ·
              refine ⟨3976819375757358863582221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5302425834343145151442961 3976819375757358863582221)
              ·
                refine ⟨1491307265909009573843333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3976819375757358863582221 1491307265909009573843333)
                ·
                  refine ⟨279620112357939295095625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1491307265909009573843333 279620112357939295095625)
                  ·
                    rfl

theorem cell21_1225256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_1225256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225256 prefixEnd_1225256 := by exact prefixLift 1225256
  have htrace : WordTrace (prefixWord ++ tailWord_1225256) baseStart_1225256 baseEnd_1225256 := by
    simpa [prefixWord, tailWord_1225256, baseEnd_1225256] using wordTrace_append hprefix tailTrace_1225256
  have hstable : (prefixWord ++ tailWord_1225256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225256).length < 2 ^ (prefixWord ++ tailWord_1225256).sum := by decide
  have hdescent : baseEnd_1225256 < baseStart_1225256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225301 : List Nat := [1, 3, 2, 2, 1, 1, 4, 4, 3]
def baseStart_1225301 : Nat := 118140960795 + 1225301 * 2 ^ 59
def prefixEnd_1225301 : Nat := 4983230072969 + 3 ^ 40 * 1225301 * 2
def baseEnd_1225301 : Nat := 279630381971029216845533

theorem tailTrace_1225301 : CollatzResearch.WordTrace tailWord_1225301 prefixEnd_1225301 279630381971029216845533 := by
  unfold tailWord_1225301
  simp only [CollatzResearch.WordTrace]
  refine ⟨44690398933951216595491757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29793599289300811063661171 44690398933951216595491757)
  ·
    refine ⟨16758899600231706223309409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44690398933951216595491757 16758899600231706223309409)
    ·
      refine ⟨12569174700173779667482057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16758899600231706223309409 12569174700173779667482057)
      ·
        refine ⟨9426881025130334750611543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12569174700173779667482057 9426881025130334750611543)
        ·
          refine ⟨14140321537695502125917315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9426881025130334750611543 14140321537695502125917315)
          ·
            refine ⟨21210482306543253188875973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14140321537695502125917315 21210482306543253188875973)
            ·
              refine ⟨3976965432476859972914245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21210482306543253188875973 3976965432476859972914245)
              ·
                refine ⟨745681018589411244921421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3976965432476859972914245 745681018589411244921421)
                ·
                  refine ⟨279630381971029216845533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745681018589411244921421 279630381971029216845533)
                  ·
                    rfl

theorem cell21_1225301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4, 3].length) (baseStart_1225301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225301 prefixEnd_1225301 := by exact prefixLift 1225301
  have htrace : WordTrace (prefixWord ++ tailWord_1225301) baseStart_1225301 baseEnd_1225301 := by
    simpa [prefixWord, tailWord_1225301, baseEnd_1225301] using wordTrace_append hprefix tailTrace_1225301
  have hstable : (prefixWord ++ tailWord_1225301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225301).length < 2 ^ (prefixWord ++ tailWord_1225301).sum := by decide
  have hdescent : baseEnd_1225301 < baseStart_1225301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225422 : List Nat := [4, 1, 1, 1, 3, 4, 1, 6]
def baseStart_1225422 : Nat := 118140960795 + 1225422 * 2 ^ 59
def prefixEnd_1225422 : Nat := 4983230072969 + 3 ^ 40 * 1225422 * 2
def baseEnd_1225422 : Nat := 93219331939853298442873

theorem tailTrace_1225422 : CollatzResearch.WordTrace tailWord_1225422 prefixEnd_1225422 93219331939853298442873 := by
  unfold tailWord_1225422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586851520814106782580815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29796541444341902840431013 5586851520814106782580815)
  ·
    refine ⟨8380277281221160173871223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5586851520814106782580815 8380277281221160173871223)
    ·
      refine ⟨12570415921831740260806835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8380277281221160173871223 12570415921831740260806835)
      ·
        refine ⟨18855623882747610391210253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12570415921831740260806835 18855623882747610391210253)
        ·
          refine ⟨7070858956030353896703845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18855623882747610391210253 7070858956030353896703845)
          ·
            refine ⟨1325786054255691355631971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7070858956030353896703845 1325786054255691355631971)
            ·
              refine ⟨1988679081383537033447957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1325786054255691355631971 1988679081383537033447957)
              ·
                refine ⟨93219331939853298442873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1988679081383537033447957 93219331939853298442873)
                ·
                  rfl

theorem cell21_1225422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_1225422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225422 prefixEnd_1225422 := by exact prefixLift 1225422
  have htrace : WordTrace (prefixWord ++ tailWord_1225422) baseStart_1225422 baseEnd_1225422 := by
    simpa [prefixWord, tailWord_1225422, baseEnd_1225422] using wordTrace_append hprefix tailTrace_1225422
  have hstable : (prefixWord ++ tailWord_1225422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225422).length < 2 ^ (prefixWord ++ tailWord_1225422).sum := by decide
  have hdescent : baseEnd_1225422 < baseStart_1225422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225450 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 6]
def baseStart_1225450 : Nat := 118140960795 + 1225450 * 2 ^ 59
def prefixEnd_1225450 : Nat := 4983230072969 + 3 ^ 40 * 1225450 * 2
def baseEnd_1225450 : Nat := 279664385801038068861895

theorem tailTrace_1225450 : CollatzResearch.WordTrace tailWord_1225450 prefixEnd_1225450 279664385801038068861895 := by
  unfold tailWord_1225450
  simp only [CollatzResearch.WordTrace]
  refine ⟨11173958352602853760666451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29797222273607610028443869 11173958352602853760666451)
  ·
    refine ⟨16760937528904280640999677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11173958352602853760666451 16760937528904280640999677)
    ·
      refine ⟨6285351573339105240374879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16760937528904280640999677 6285351573339105240374879)
      ·
        refine ⟨9428027360008657860562319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6285351573339105240374879 9428027360008657860562319)
        ·
          refine ⟨14142041040012986790843479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9428027360008657860562319 14142041040012986790843479)
          ·
            refine ⟨21213061560019480186265219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14142041040012986790843479 21213061560019480186265219)
            ·
              refine ⟨31819592340029220279397829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21213061560019480186265219 31819592340029220279397829)
              ·
                refine ⟨5966173563755478802387093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31819592340029220279397829 5966173563755478802387093)
                ·
                  refine ⟨279664385801038068861895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5966173563755478802387093 279664385801038068861895)
                  ·
                    rfl

theorem cell21_1225450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_1225450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225450 prefixEnd_1225450 := by exact prefixLift 1225450
  have htrace : WordTrace (prefixWord ++ tailWord_1225450) baseStart_1225450 baseEnd_1225450 := by
    simpa [prefixWord, tailWord_1225450, baseEnd_1225450] using wordTrace_append hprefix tailTrace_1225450
  have hstable : (prefixWord ++ tailWord_1225450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225450).length < 2 ^ (prefixWord ++ tailWord_1225450).sum := by decide
  have hdescent : baseEnd_1225450 < baseStart_1225450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225464 : List Nat := [2, 1, 2, 1, 1, 2, 12]
def baseStart_1225464 : Nat := 118140960795 + 1225464 * 2 ^ 59
def prefixEnd_1225464 : Nat := 4983230072969 + 3 ^ 40 * 1225464 * 2
def baseEnd_1225464 : Nat := 31074175643530795069837

theorem tailTrace_1225464 : CollatzResearch.WordTrace tailWord_1225464 prefixEnd_1225464 31074175643530795069837 := by
  unfold tailWord_1225464
  simp only [CollatzResearch.WordTrace]
  refine ⟨22348172016180347716837723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29797562688240463622450297 22348172016180347716837723)
  ·
    refine ⟨33522258024270521575256585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22348172016180347716837723 33522258024270521575256585)
    ·
      refine ⟨25141693518202891181442439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33522258024270521575256585 25141693518202891181442439)
      ·
        refine ⟨37712540277304336772163659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25141693518202891181442439 37712540277304336772163659)
        ·
          refine ⟨56568810415956505158245489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37712540277304336772163659 56568810415956505158245489)
          ·
            refine ⟨42426607811967378868684117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56568810415956505158245489 42426607811967378868684117)
            ·
              refine ⟨31074175643530795069837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 42426607811967378868684117 31074175643530795069837)
              ·
                rfl

theorem cell21_1225464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 12].length) (baseStart_1225464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225464 prefixEnd_1225464 := by exact prefixLift 1225464
  have htrace : WordTrace (prefixWord ++ tailWord_1225464) baseStart_1225464 baseEnd_1225464 := by
    simpa [prefixWord, tailWord_1225464, baseEnd_1225464] using wordTrace_append hprefix tailTrace_1225464
  have hstable : (prefixWord ++ tailWord_1225464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225464).length < 2 ^ (prefixWord ++ tailWord_1225464).sum := by decide
  have hdescent : baseEnd_1225464 < baseStart_1225464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225470 : List Nat := [4, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_1225470 : Nat := 118140960795 + 1225470 * 2 ^ 59
def prefixEnd_1225470 : Nat := 4983230072969 + 3 ^ 40 * 1225470 * 2
def baseEnd_1225470 : Nat := 279668950073522478528521

theorem tailTrace_1225470 : CollatzResearch.WordTrace tailWord_1225470 prefixEnd_1225470 279668950073522478528521 := by
  unfold tailWord_1225470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5587070358792369807299233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29797708580225972305595909 5587070358792369807299233)
  ·
    refine ⟨4190302769094277355474425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5587070358792369807299233 4190302769094277355474425)
    ·
      refine ⟨3142727076820708016605819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4190302769094277355474425 3142727076820708016605819)
      ·
        refine ⟨4714090615231062024908729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3142727076820708016605819 4714090615231062024908729)
        ·
          refine ⟨3535567961423296518681547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4714090615231062024908729 3535567961423296518681547)
          ·
            refine ⟨5303351942134944778022321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535567961423296518681547 5303351942134944778022321)
            ·
              refine ⟨3977513956601208583516741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5303351942134944778022321 3977513956601208583516741)
              ·
                refine ⟨745783866862726609409389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3977513956601208583516741 745783866862726609409389)
                ·
                  refine ⟨279668950073522478528521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745783866862726609409389 279668950073522478528521)
                  ·
                    rfl

theorem cell21_1225470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_1225470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225470 prefixEnd_1225470 := by exact prefixLift 1225470
  have htrace : WordTrace (prefixWord ++ tailWord_1225470) baseStart_1225470 baseEnd_1225470 := by
    simpa [prefixWord, tailWord_1225470, baseEnd_1225470] using wordTrace_append hprefix tailTrace_1225470
  have hstable : (prefixWord ++ tailWord_1225470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225470).length < 2 ^ (prefixWord ++ tailWord_1225470).sum := by decide
  have hdescent : baseEnd_1225470 < baseStart_1225470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225633 : List Nat := [1, 2, 3, 4, 1, 2, 8]
def baseStart_1225633 : Nat := 118140960795 + 1225633 * 2 ^ 59
def prefixEnd_1225633 : Nat := 4983230072969 + 3 ^ 40 * 1225633 * 2
def baseEnd_1225633 : Nat := 31078460988252268590169

theorem tailTrace_1225633 : CollatzResearch.WordTrace tailWord_1225633 prefixEnd_1225633 31078460988252268590169 := by
  unfold tailWord_1225633
  simp only [CollatzResearch.WordTrace]
  refine ⟨44702507968748437296577553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29801671979165624864385035 44702507968748437296577553)
  ·
    refine ⟨33526880976561327972433165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44702507968748437296577553 33526880976561327972433165)
    ·
      refine ⟨12572580366210497989662437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33526880976561327972433165 12572580366210497989662437)
      ·
        refine ⟨2357358818664468373061707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12572580366210497989662437 2357358818664468373061707)
        ·
          refine ⟨3536038227996702559592561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357358818664468373061707 3536038227996702559592561)
          ·
            refine ⟨2652028670997526919694421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3536038227996702559592561 2652028670997526919694421)
            ·
              refine ⟨31078460988252268590169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2652028670997526919694421 31078460988252268590169)
              ·
                rfl

theorem cell21_1225633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 8].length) (baseStart_1225633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225633 prefixEnd_1225633 := by exact prefixLift 1225633
  have htrace : WordTrace (prefixWord ++ tailWord_1225633) baseStart_1225633 baseEnd_1225633 := by
    simpa [prefixWord, tailWord_1225633, baseEnd_1225633] using wordTrace_append hprefix tailTrace_1225633
  have hstable : (prefixWord ++ tailWord_1225633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225633).length < 2 ^ (prefixWord ++ tailWord_1225633).sum := by decide
  have hdescent : baseEnd_1225633 < baseStart_1225633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225678 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_1225678 : Nat := 118140960795 + 1225678 * 2 ^ 59
def prefixEnd_1225678 : Nat := 4983230072969 + 3 ^ 40 * 1225678 * 2
def baseEnd_1225678 : Nat := 279716418507360339061429

theorem tailTrace_1225678 : CollatzResearch.WordTrace tailWord_1225678 prefixEnd_1225678 279716418507360339061429 := by
  unfold tailWord_1225678
  simp only [CollatzResearch.WordTrace]
  refine ⟨5588018656698176247745711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29802766169056939987977125 5588018656698176247745711)
  ·
    refine ⟨8382027985047264371618567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5588018656698176247745711 8382027985047264371618567)
    ·
      refine ⟨12573041977570896557427851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8382027985047264371618567 12573041977570896557427851)
      ·
        refine ⟨18859562966356344836141777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12573041977570896557427851 18859562966356344836141777)
        ·
          refine ⟨14144672224767258627106333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18859562966356344836141777 14144672224767258627106333)
          ·
            refine ⟨5304252084287721985164875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14144672224767258627106333 5304252084287721985164875)
            ·
              refine ⟨7956378126431582977747313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5304252084287721985164875 7956378126431582977747313)
              ·
                refine ⟨5967283594823687233310485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7956378126431582977747313 5967283594823687233310485)
                ·
                  refine ⟨279716418507360339061429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5967283594823687233310485 279716418507360339061429)
                  ·
                    rfl

theorem cell21_1225678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_1225678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225678 prefixEnd_1225678 := by exact prefixLift 1225678
  have htrace : WordTrace (prefixWord ++ tailWord_1225678) baseStart_1225678 baseEnd_1225678 := by
    simpa [prefixWord, tailWord_1225678, baseEnd_1225678] using wordTrace_append hprefix tailTrace_1225678
  have hstable : (prefixWord ++ tailWord_1225678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225678).length < 2 ^ (prefixWord ++ tailWord_1225678).sum := by decide
  have hdescent : baseEnd_1225678 < baseStart_1225678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225698 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_1225698 : Nat := 118140960795 + 1225698 * 2 ^ 59
def prefixEnd_1225698 : Nat := 4983230072969 + 3 ^ 40 * 1225698 * 2
def baseEnd_1225698 : Nat := 279720982779844748728055

theorem tailTrace_1225698 : CollatzResearch.WordTrace tailWord_1225698 prefixEnd_1225698 279720982779844748728055 := by
  unfold tailWord_1225698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11176219678378238349423437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29803252475675302265129165 11176219678378238349423437)
  ·
    refine ⟨4191082379391839381033789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11176219678378238349423437 4191082379391839381033789)
    ·
      refine ⟨1571655892271939767887671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4191082379391839381033789 1571655892271939767887671)
      ·
        refine ⟨2357483838407909651831507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571655892271939767887671 2357483838407909651831507)
        ·
          refine ⟨3536225757611864477747261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357483838407909651831507 3536225757611864477747261)
          ·
            refine ⟨1326084659104449179155223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3536225757611864477747261 1326084659104449179155223)
            ·
              refine ⟨1989126988656673768732835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326084659104449179155223 1989126988656673768732835)
              ·
                refine ⟨2983690482985010653099253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989126988656673768732835 2983690482985010653099253)
                ·
                  refine ⟨279720982779844748728055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2983690482985010653099253 279720982779844748728055)
                  ·
                    rfl

theorem cell21_1225698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_1225698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225698 prefixEnd_1225698 := by exact prefixLift 1225698
  have htrace : WordTrace (prefixWord ++ tailWord_1225698) baseStart_1225698 baseEnd_1225698 := by
    simpa [prefixWord, tailWord_1225698, baseEnd_1225698] using wordTrace_append hprefix tailTrace_1225698
  have hstable : (prefixWord ++ tailWord_1225698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225698).length < 2 ^ (prefixWord ++ tailWord_1225698).sum := by decide
  have hdescent : baseEnd_1225698 < baseStart_1225698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225737 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 8]
def baseStart_1225737 : Nat := 118140960795 + 1225737 * 2 ^ 59
def prefixEnd_1225737 : Nat := 4983230072969 + 3 ^ 40 * 1225737 * 2
def baseEnd_1225737 : Nat := 279729883111189347577975

theorem tailTrace_1225737 : CollatzResearch.WordTrace tailWord_1225737 prefixEnd_1225737 279729883111189347577975 := by
  unfold tailWord_1225737
  simp only [CollatzResearch.WordTrace]
  refine ⟨44706301160371663058363465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29804200773581108705575643 44706301160371663058363465)
  ·
    refine ⟨33529725870278747293772599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44706301160371663058363465 33529725870278747293772599)
    ·
      refine ⟨50294588805418120940658899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33529725870278747293772599 50294588805418120940658899)
      ·
        refine ⟨75441883208127181410988349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50294588805418120940658899 75441883208127181410988349)
        ·
          refine ⟨28290706203047693029120631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75441883208127181410988349 28290706203047693029120631)
          ·
            refine ⟨42436059304571539543680947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28290706203047693029120631 42436059304571539543680947)
            ·
              refine ⟨63654088956857309315521421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42436059304571539543680947 63654088956857309315521421)
              ·
                refine ⟨23870283358821490993320533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63654088956857309315521421 23870283358821490993320533)
                ·
                  refine ⟨279729883111189347577975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23870283358821490993320533 279729883111189347577975)
                  ·
                    rfl

theorem cell21_1225737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 8].length) (baseStart_1225737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225737 prefixEnd_1225737 := by exact prefixLift 1225737
  have htrace : WordTrace (prefixWord ++ tailWord_1225737) baseStart_1225737 baseEnd_1225737 := by
    simpa [prefixWord, tailWord_1225737, baseEnd_1225737] using wordTrace_append hprefix tailTrace_1225737
  have hstable : (prefixWord ++ tailWord_1225737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225737).length < 2 ^ (prefixWord ++ tailWord_1225737).sum := by decide
  have hdescent : baseEnd_1225737 < baseStart_1225737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225746 : List Nat := [3, 2, 5, 1, 1, 1, 2, 2, 4]
def baseStart_1225746 : Nat := 118140960795 + 1225746 * 2 ^ 59
def prefixEnd_1225746 : Nat := 4983230072969 + 3 ^ 40 * 1225746 * 2
def baseEnd_1225746 : Nat := 279731937033807331927957

theorem tailTrace_1225746 : CollatzResearch.WordTrace tailWord_1225746 prefixEnd_1225746 279731937033807331927957 := by
  unfold tailWord_1225746
  simp only [CollatzResearch.WordTrace]
  refine ⟨11176657354334764398860273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29804419611559371730294061 11176657354334764398860273)
  ·
    refine ⟨8382493015751073299145205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11176657354334764398860273 8382493015751073299145205)
    ·
      refine ⟨785858720226663121794863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8382493015751073299145205 785858720226663121794863)
      ·
        refine ⟨1178788080339994682692295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785858720226663121794863 1178788080339994682692295)
        ·
          refine ⟨1768182120509992024038443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178788080339994682692295 1768182120509992024038443)
          ·
            refine ⟨2652273180764988036057665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768182120509992024038443 2652273180764988036057665)
            ·
              refine ⟨1989204885573741027043249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2652273180764988036057665 1989204885573741027043249)
              ·
                refine ⟨1491903664180305770282437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989204885573741027043249 1491903664180305770282437)
                ·
                  refine ⟨279731937033807331927957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1491903664180305770282437 279731937033807331927957)
                  ·
                    rfl

theorem cell21_1225746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_1225746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225746 prefixEnd_1225746 := by exact prefixLift 1225746
  have htrace : WordTrace (prefixWord ++ tailWord_1225746) baseStart_1225746 baseEnd_1225746 := by
    simpa [prefixWord, tailWord_1225746, baseEnd_1225746] using wordTrace_append hprefix tailTrace_1225746
  have hstable : (prefixWord ++ tailWord_1225746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225746).length < 2 ^ (prefixWord ++ tailWord_1225746).sum := by decide
  have hdescent : baseEnd_1225746 < baseStart_1225746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225816 : List Nat := [2, 1, 2, 2, 1, 3, 1, 6, 3]
def baseStart_1225816 : Nat := 118140960795 + 1225816 * 2 ^ 59
def prefixEnd_1225816 : Nat := 4983230072969 + 3 ^ 40 * 1225816 * 2
def baseEnd_1225816 : Nat := 279747911987502765761147

theorem tailTrace_1225816 : CollatzResearch.WordTrace tailWord_1225816 prefixEnd_1225816 279747911987502765761147 := by
  unfold tailWord_1225816
  simp only [CollatzResearch.WordTrace]
  refine ⟨22354591263542729775244651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29806121684723639700326201 22354591263542729775244651)
  ·
    refine ⟨33531886895314094662866977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22354591263542729775244651 33531886895314094662866977)
    ·
      refine ⟨25148915171485570997150233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33531886895314094662866977 25148915171485570997150233)
      ·
        refine ⟨18861686378614178247862675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25148915171485570997150233 18861686378614178247862675)
        ·
          refine ⟨28292529567921267371794013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18861686378614178247862675 28292529567921267371794013)
          ·
            refine ⟨10609698587970475264422755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28292529567921267371794013 10609698587970475264422755)
            ·
              refine ⟨15914547881955712896634133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10609698587970475264422755 15914547881955712896634133)
              ·
                refine ⟨745994431966674042029725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15914547881955712896634133 745994431966674042029725)
                ·
                  refine ⟨279747911987502765761147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 745994431966674042029725 279747911987502765761147)
                  ·
                    rfl

theorem cell21_1225816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 3].length) (baseStart_1225816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225816 prefixEnd_1225816 := by exact prefixLift 1225816
  have htrace : WordTrace (prefixWord ++ tailWord_1225816) baseStart_1225816 baseEnd_1225816 := by
    simpa [prefixWord, tailWord_1225816, baseEnd_1225816] using wordTrace_append hprefix tailTrace_1225816
  have hstable : (prefixWord ++ tailWord_1225816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225816).length < 2 ^ (prefixWord ++ tailWord_1225816).sum := by decide
  have hdescent : baseEnd_1225816 < baseStart_1225816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225822 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1225822 : Nat := 118140960795 + 1225822 * 2 ^ 59
def prefixEnd_1225822 : Nat := 4983230072969 + 3 ^ 40 * 1225822 * 2
def baseEnd_1225822 : Nat := 279749281269248088661135

theorem tailTrace_1225822 : CollatzResearch.WordTrace tailWord_1225822 prefixEnd_1225822 279749281269248088661135 := by
  unfold tailWord_1225822
  simp only [CollatzResearch.WordTrace]
  refine ⟨5588675170632965321900965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29806267576709148383471813 5588675170632965321900965)
  ·
    refine ⟨1047876594493680997856431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5588675170632965321900965 1047876594493680997856431)
    ·
      refine ⟨1571814891740521496784647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1047876594493680997856431 1571814891740521496784647)
      ·
        refine ⟨2357722337610782245176971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571814891740521496784647 2357722337610782245176971)
        ·
          refine ⟨3536583506416173367765457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357722337610782245176971 3536583506416173367765457)
          ·
            refine ⟨2652437629812130025824093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3536583506416173367765457 2652437629812130025824093)
            ·
              refine ⟨994664111179548759684035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2652437629812130025824093 994664111179548759684035)
              ·
                refine ⟨1491996166769323139526053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994664111179548759684035 1491996166769323139526053)
                ·
                  refine ⟨279749281269248088661135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1491996166769323139526053 279749281269248088661135)
                  ·
                    rfl

theorem cell21_1225822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1225822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225822 prefixEnd_1225822 := by exact prefixLift 1225822
  have htrace : WordTrace (prefixWord ++ tailWord_1225822) baseStart_1225822 baseEnd_1225822 := by
    simpa [prefixWord, tailWord_1225822, baseEnd_1225822] using wordTrace_append hprefix tailTrace_1225822
  have hstable : (prefixWord ++ tailWord_1225822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225822).length < 2 ^ (prefixWord ++ tailWord_1225822).sum := by decide
  have hdescent : baseEnd_1225822 < baseStart_1225822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225861 : List Nat := [1, 3, 1, 1, 6, 2, 7]
def baseStart_1225861 : Nat := 118140960795 + 1225861 * 2 ^ 59
def prefixEnd_1225861 : Nat := 4983230072969 + 3 ^ 40 * 1225861 * 2
def baseEnd_1225861 : Nat := 31084242400065854167895

theorem tailTrace_1225861 : CollatzResearch.WordTrace tailWord_1225861 prefixEnd_1225861 31084242400065854167895 := by
  unfold tailWord_1225861
  simp only [CollatzResearch.WordTrace]
  refine ⟨44710823811922432235877437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29807215874614954823918291 44710823811922432235877437)
  ·
    refine ⟨16766558929470912088454039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44710823811922432235877437 16766558929470912088454039)
    ·
      refine ⟨25149838394206368132681059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16766558929470912088454039 25149838394206368132681059)
      ·
        refine ⟨37724757591309552199021589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25149838394206368132681059 37724757591309552199021589)
        ·
          refine ⟨1768348012092635259329137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37724757591309552199021589 1768348012092635259329137)
          ·
            refine ⟨1326261009069476444496853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1768348012092635259329137 1326261009069476444496853)
            ·
              refine ⟨31084242400065854167895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1326261009069476444496853 31084242400065854167895)
              ·
                rfl

theorem cell21_1225861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 7].length) (baseStart_1225861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225861 prefixEnd_1225861 := by exact prefixLift 1225861
  have htrace : WordTrace (prefixWord ++ tailWord_1225861) baseStart_1225861 baseEnd_1225861 := by
    simpa [prefixWord, tailWord_1225861, baseEnd_1225861] using wordTrace_append hprefix tailTrace_1225861
  have hstable : (prefixWord ++ tailWord_1225861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225861).length < 2 ^ (prefixWord ++ tailWord_1225861).sum := by decide
  have hdescent : baseEnd_1225861 < baseStart_1225861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225875 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 5]
def baseStart_1225875 : Nat := 118140960795 + 1225875 * 2 ^ 59
def prefixEnd_1225875 : Nat := 4983230072969 + 3 ^ 40 * 1225875 * 2
def baseEnd_1225875 : Nat := 279761376591331774277693

theorem tailTrace_1225875 : CollatzResearch.WordTrace tailWord_1225875 prefixEnd_1225875 279761376591331774277693 := by
  unfold tailWord_1225875
  simp only [CollatzResearch.WordTrace]
  refine ⟨44711334433871712626887079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29807556289247808417924719 44711334433871712626887079)
  ·
    refine ⟨67067001650807568940330619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44711334433871712626887079 67067001650807568940330619)
    ·
      refine ⟨100600502476211353410495929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67067001650807568940330619 100600502476211353410495929)
      ·
        refine ⟨75450376857158515057871947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100600502476211353410495929 75450376857158515057871947)
        ·
          refine ⟨113175565285737772586807921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75450376857158515057871947 113175565285737772586807921)
          ·
            refine ⟨84881673964303329440105941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113175565285737772586807921 84881673964303329440105941)
            ·
              refine ⟨1989414233538359283752483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 84881673964303329440105941 1989414233538359283752483)
              ·
                refine ⟨2984121350307538925628725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989414233538359283752483 2984121350307538925628725)
                ·
                  refine ⟨279761376591331774277693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2984121350307538925628725 279761376591331774277693)
                  ·
                    rfl

theorem cell21_1225875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 5].length) (baseStart_1225875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225875 prefixEnd_1225875 := by exact prefixLift 1225875
  have htrace : WordTrace (prefixWord ++ tailWord_1225875) baseStart_1225875 baseEnd_1225875 := by
    simpa [prefixWord, tailWord_1225875, baseEnd_1225875] using wordTrace_append hprefix tailTrace_1225875
  have hstable : (prefixWord ++ tailWord_1225875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225875).length < 2 ^ (prefixWord ++ tailWord_1225875).sum := by decide
  have hdescent : baseEnd_1225875 < baseStart_1225875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1225920 : List Nat := [2, 1, 1, 2, 6, 9]
def baseStart_1225920 : Nat := 118140960795 + 1225920 * 2 ^ 59
def prefixEnd_1225920 : Nat := 4983230072969 + 3 ^ 40 * 1225920 * 2
def baseEnd_1225920 : Nat := 10361912822385988741763

theorem tailTrace_1225920 : CollatzResearch.WordTrace tailWord_1225920 prefixEnd_1225920 10361912822385988741763 := by
  unfold tailWord_1225920
  simp only [CollatzResearch.WordTrace]
  refine ⟨22356487859354342656137607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29808650479139123541516809 22356487859354342656137607)
  ·
    refine ⟨33534731789031513984206411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22356487859354342656137607 33534731789031513984206411)
    ·
      refine ⟨50302097683547270976309617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33534731789031513984206411 50302097683547270976309617)
      ·
        refine ⟨37726573262660453232232213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50302097683547270976309617 37726573262660453232232213)
        ·
          refine ⟨1768433121687208745260885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37726573262660453232232213 1768433121687208745260885)
          ·
            refine ⟨10361912822385988741763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1768433121687208745260885 10361912822385988741763)
            ·
              rfl

theorem cell21_1225920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 9].length) (baseStart_1225920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1225920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1225920 prefixEnd_1225920 := by exact prefixLift 1225920
  have htrace : WordTrace (prefixWord ++ tailWord_1225920) baseStart_1225920 baseEnd_1225920 := by
    simpa [prefixWord, tailWord_1225920, baseEnd_1225920] using wordTrace_append hprefix tailTrace_1225920
  have hstable : (prefixWord ++ tailWord_1225920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1225920).length < 2 ^ (prefixWord ++ tailWord_1225920).sum := by decide
  have hdescent : baseEnd_1225920 < baseStart_1225920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1225920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226013 : List Nat := [1, 4, 2, 3, 1, 2, 1, 7]
def baseStart_1226013 : Nat := 118140960795 + 1226013 * 2 ^ 59
def prefixEnd_1226013 : Nat := 4983230072969 + 3 ^ 40 * 1226013 * 2
def baseEnd_1226013 : Nat := 93264290023824733659137

theorem tailTrace_1226013 : CollatzResearch.WordTrace tailWord_1226013 prefixEnd_1226013 93264290023824733659137 := by
  unfold tailWord_1226013
  simp only [CollatzResearch.WordTrace]
  refine ⟨44716367707371762195410693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29810911804914508130273795 44716367707371762195410693)
  ·
    refine ⟨8384318945132205411639505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44716367707371762195410693 8384318945132205411639505)
    ·
      refine ⟨6288239208849154058729629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8384318945132205411639505 6288239208849154058729629)
      ·
        refine ⟨2358089703318432772023611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6288239208849154058729629 2358089703318432772023611)
        ·
          refine ⟨3537134554977649158035417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358089703318432772023611 3537134554977649158035417)
          ·
            refine ⟨2652850916233236868526563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3537134554977649158035417 2652850916233236868526563)
            ·
              refine ⟨3979276374349855302789845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652850916233236868526563 3979276374349855302789845)
              ·
                refine ⟨93264290023824733659137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3979276374349855302789845 93264290023824733659137)
                ·
                  rfl

theorem cell21_1226013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 7].length) (baseStart_1226013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226013 prefixEnd_1226013 := by exact prefixLift 1226013
  have htrace : WordTrace (prefixWord ++ tailWord_1226013) baseStart_1226013 baseEnd_1226013 := by
    simpa [prefixWord, tailWord_1226013, baseEnd_1226013] using wordTrace_append hprefix tailTrace_1226013
  have hstable : (prefixWord ++ tailWord_1226013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226013).length < 2 ^ (prefixWord ++ tailWord_1226013).sum := by decide
  have hdescent : baseEnd_1226013 < baseStart_1226013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226044 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 5]
def baseStart_1226044 : Nat := 118140960795 + 1226044 * 2 ^ 59
def prefixEnd_1226044 : Nat := 4983230072969 + 3 ^ 40 * 1226044 * 2
def baseEnd_1226044 : Nat := 279799944693825035960681

theorem tailTrace_1226044 : CollatzResearch.WordTrace tailWord_1226044 prefixEnd_1226044 279799944693825035960681 := by
  unfold tailWord_1226044
  simp only [CollatzResearch.WordTrace]
  refine ⟨22358749185129727244894593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29811665580172969659859457 22358749185129727244894593)
  ·
    refine ⟨16769061888847295433670945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22358749185129727244894593 16769061888847295433670945)
    ·
      refine ⟨12576796416635471575253209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16769061888847295433670945 12576796416635471575253209)
      ·
        refine ⟨9432597312476603681439907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12576796416635471575253209 9432597312476603681439907)
        ·
          refine ⟨14148895968714905522159861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9432597312476603681439907 14148895968714905522159861)
          ·
            refine ⟨1326458997067022392702487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14148895968714905522159861 1326458997067022392702487)
            ·
              refine ⟨1989688495600533589053731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326458997067022392702487 1989688495600533589053731)
              ·
                refine ⟨2984532743400800383580597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989688495600533589053731 2984532743400800383580597)
                ·
                  refine ⟨279799944693825035960681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2984532743400800383580597 279799944693825035960681)
                  ·
                    rfl

theorem cell21_1226044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_1226044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226044 prefixEnd_1226044 := by exact prefixLift 1226044
  have htrace : WordTrace (prefixWord ++ tailWord_1226044) baseStart_1226044 baseEnd_1226044 := by
    simpa [prefixWord, tailWord_1226044, baseEnd_1226044] using wordTrace_append hprefix tailTrace_1226044
  have hstable : (prefixWord ++ tailWord_1226044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226044).length < 2 ^ (prefixWord ++ tailWord_1226044).sum := by decide
  have hdescent : baseEnd_1226044 < baseStart_1226044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226224 : List Nat := [2, 1, 1, 1, 3, 5, 2, 6]
def baseStart_1226224 : Nat := 118140960795 + 1226224 * 2 ^ 59
def prefixEnd_1226224 : Nat := 4983230072969 + 3 ^ 40 * 1226224 * 2
def baseEnd_1226224 : Nat := 93280341048728240986771

theorem tailTrace_1226224 : CollatzResearch.WordTrace tailWord_1226224 prefixEnd_1226224 93280341048728240986771 := by
  unfold tailWord_1226224
  simp only [CollatzResearch.WordTrace]
  refine ⟨22362031754803672615670863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29816042339738230154227817 22362031754803672615670863)
  ·
    refine ⟨33543047632205508923506295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22362031754803672615670863 33543047632205508923506295)
    ·
      refine ⟨50314571448308263385259443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33543047632205508923506295 50314571448308263385259443)
      ·
        refine ⟨75471857172462395077889165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50314571448308263385259443 75471857172462395077889165)
        ·
          refine ⟨28301946439673398154208437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75471857172462395077889165 28301946439673398154208437)
          ·
            refine ⟨2653307478719381076957041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28301946439673398154208437 2653307478719381076957041)
            ·
              refine ⟨1989980609039535807717781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2653307478719381076957041 1989980609039535807717781)
              ·
                refine ⟨93280341048728240986771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1989980609039535807717781 93280341048728240986771)
                ·
                  rfl

theorem cell21_1226224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 6].length) (baseStart_1226224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226224 prefixEnd_1226224 := by exact prefixLift 1226224
  have htrace : WordTrace (prefixWord ++ tailWord_1226224) baseStart_1226224 baseEnd_1226224 := by
    simpa [prefixWord, tailWord_1226224, baseEnd_1226224] using wordTrace_append hprefix tailTrace_1226224
  have hstable : (prefixWord ++ tailWord_1226224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226224).length < 2 ^ (prefixWord ++ tailWord_1226224).sum := by decide
  have hdescent : baseEnd_1226224 < baseStart_1226224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226314 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 7]
def baseStart_1226314 : Nat := 118140960795 + 1226314 * 2 ^ 59
def prefixEnd_1226314 : Nat := 4983230072969 + 3 ^ 40 * 1226314 * 2
def baseEnd_1226314 : Nat := 279861562372364566460129

theorem tailTrace_1226314 : CollatzResearch.WordTrace tailWord_1226314 prefixEnd_1226314 279861562372364566460129 := by
  unfold tailWord_1226314
  simp only [CollatzResearch.WordTrace]
  refine ⟨11181836519820322650529499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29818230719520860401411997 11181836519820322650529499)
  ·
    refine ⟨16772754779730483975794249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11181836519820322650529499 16772754779730483975794249)
    ·
      refine ⟨12579566084797862981845687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16772754779730483975794249 12579566084797862981845687)
      ·
        refine ⟨18869349127196794472768531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12579566084797862981845687 18869349127196794472768531)
        ·
          refine ⟨28304023690795191709152797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18869349127196794472768531 28304023690795191709152797)
          ·
            refine ⟨10614008884048196890932299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28304023690795191709152797 10614008884048196890932299)
            ·
              refine ⟨15921013326072295336398449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10614008884048196890932299 15921013326072295336398449)
              ·
                refine ⟨11940759994554221502298837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15921013326072295336398449 11940759994554221502298837)
                ·
                  refine ⟨279861562372364566460129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11940759994554221502298837 279861562372364566460129)
                  ·
                    rfl

theorem cell21_1226314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_1226314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226314 prefixEnd_1226314 := by exact prefixLift 1226314
  have htrace : WordTrace (prefixWord ++ tailWord_1226314) baseStart_1226314 baseEnd_1226314 := by
    simpa [prefixWord, tailWord_1226314, baseEnd_1226314] using wordTrace_append hprefix tailTrace_1226314
  have hstable : (prefixWord ++ tailWord_1226314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226314).length < 2 ^ (prefixWord ++ tailWord_1226314).sum := by decide
  have hdescent : baseEnd_1226314 < baseStart_1226314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226317 : List Nat := [1, 6, 1, 1, 3, 1, 8]
def baseStart_1226317 : Nat := 118140960795 + 1226317 * 2 ^ 59
def prefixEnd_1226317 : Nat := 4983230072969 + 3 ^ 40 * 1226317 * 2
def baseEnd_1226317 : Nat := 31095805223693025323347

theorem tailTrace_1226317 : CollatzResearch.WordTrace tailWord_1226317 prefixEnd_1226317 31095805223693025323347 := by
  unfold tailWord_1226317
  simp only [CollatzResearch.WordTrace]
  refine ⟨44727455498270422114477205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29818303665513614742984803 44727455498270422114477205)
  ·
    refine ⟨2096599476481426036616119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44727455498270422114477205 2096599476481426036616119)
    ·
      refine ⟨3144899214722139054924179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2096599476481426036616119 3144899214722139054924179)
      ·
        refine ⟨4717348822083208582386269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3144899214722139054924179 4717348822083208582386269)
        ·
          refine ⟨1769005808281203218394851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4717348822083208582386269 1769005808281203218394851)
          ·
            refine ⟨2653508712421804827592277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769005808281203218394851 2653508712421804827592277)
            ·
              refine ⟨31095805223693025323347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2653508712421804827592277 31095805223693025323347)
              ·
                rfl

theorem cell21_1226317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 8].length) (baseStart_1226317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226317 prefixEnd_1226317 := by exact prefixLift 1226317
  have htrace : WordTrace (prefixWord ++ tailWord_1226317) baseStart_1226317 baseEnd_1226317 := by
    simpa [prefixWord, tailWord_1226317, baseEnd_1226317] using wordTrace_append hprefix tailTrace_1226317
  have hstable : (prefixWord ++ tailWord_1226317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226317).length < 2 ^ (prefixWord ++ tailWord_1226317).sum := by decide
  have hdescent : baseEnd_1226317 < baseStart_1226317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226345 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 4]
def baseStart_1226345 : Nat := 118140960795 + 1226345 * 2 ^ 59
def prefixEnd_1226345 : Nat := 4983230072969 + 3 ^ 40 * 1226345 * 2
def baseEnd_1226345 : Nat := 279868636994715401443399

theorem tailTrace_1226345 : CollatzResearch.WordTrace tailWord_1226345 prefixEnd_1226345 279868636994715401443399 := by
  unfold tailWord_1226345
  simp only [CollatzResearch.WordTrace]
  refine ⟨44728476742168982896496489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29818984494779321930997659 44728476742168982896496489)
  ·
    refine ⟨33546357556626737172372367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44728476742168982896496489 33546357556626737172372367)
    ·
      refine ⟨50319536334940105758558551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33546357556626737172372367 50319536334940105758558551)
      ·
        refine ⟨75479304502410158637837827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50319536334940105758558551 75479304502410158637837827)
        ·
          refine ⟨113218956753615237956756741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75479304502410158637837827 113218956753615237956756741)
          ·
            refine ⟨21228554391302857116891889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113218956753615237956756741 21228554391302857116891889)
            ·
              refine ⟨15921415793477142837668917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21228554391302857116891889 15921415793477142837668917)
              ·
                refine ⟨1492632730638482141031461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15921415793477142837668917 1492632730638482141031461)
                ·
                  refine ⟨279868636994715401443399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1492632730638482141031461 279868636994715401443399)
                  ·
                    rfl

theorem cell21_1226345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_1226345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226345 prefixEnd_1226345 := by exact prefixLift 1226345
  have htrace : WordTrace (prefixWord ++ tailWord_1226345) baseStart_1226345 baseEnd_1226345 := by
    simpa [prefixWord, tailWord_1226345, baseEnd_1226345] using wordTrace_append hprefix tailTrace_1226345
  have hstable : (prefixWord ++ tailWord_1226345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226345).length < 2 ^ (prefixWord ++ tailWord_1226345).sum := by decide
  have hdescent : baseEnd_1226345 < baseStart_1226345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226365 : List Nat := [1, 4, 1, 1, 4, 3, 1, 3, 3]
def baseStart_1226365 : Nat := 118140960795 + 1226365 * 2 ^ 59
def prefixEnd_1226365 : Nat := 4983230072969 + 3 ^ 40 * 1226365 * 2
def baseEnd_1226365 : Nat := 279873201267199811110025

theorem tailTrace_1226365 : CollatzResearch.WordTrace tailWord_1226365 prefixEnd_1226365 279873201267199811110025 := by
  unfold tailWord_1226365
  simp only [CollatzResearch.WordTrace]
  refine ⟨44729206202096526312224549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29819470801397684208149699 44729206202096526312224549)
  ·
    refine ⟨8386726162893098683542103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44729206202096526312224549 8386726162893098683542103)
    ·
      refine ⟨12580089244339648025313155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8386726162893098683542103 12580089244339648025313155)
      ·
        refine ⟨18870133866509472037969733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12580089244339648025313155 18870133866509472037969733)
        ·
          refine ⟨3538150099970526007119325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18870133866509472037969733 3538150099970526007119325)
          ·
            refine ⟨1326806287488947252669747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3538150099970526007119325 1326806287488947252669747)
            ·
              refine ⟨1990209431233420879004621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326806287488947252669747 1990209431233420879004621)
              ·
                refine ⟨746328536712532829626733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1990209431233420879004621 746328536712532829626733)
                ·
                  refine ⟨279873201267199811110025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746328536712532829626733 279873201267199811110025)
                  ·
                    rfl

theorem cell21_1226365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_1226365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226365 prefixEnd_1226365 := by exact prefixLift 1226365
  have htrace : WordTrace (prefixWord ++ tailWord_1226365) baseStart_1226365 baseEnd_1226365 := by
    simpa [prefixWord, tailWord_1226365, baseEnd_1226365] using wordTrace_append hprefix tailTrace_1226365
  have hstable : (prefixWord ++ tailWord_1226365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226365).length < 2 ^ (prefixWord ++ tailWord_1226365).sum := by decide
  have hdescent : baseEnd_1226365 < baseStart_1226365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226396 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 4]
def baseStart_1226396 : Nat := 118140960795 + 1226396 * 2 ^ 59
def prefixEnd_1226396 : Nat := 4983230072969 + 3 ^ 40 * 1226396 * 2
def baseEnd_1226396 : Nat := 279880275889550646093295

theorem tailTrace_1226396 : CollatzResearch.WordTrace tailWord_1226396 prefixEnd_1226396 279880275889550646093295 := by
  unfold tailWord_1226396
  simp only [CollatzResearch.WordTrace]
  refine ⟨22365168432492109303301521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29820224576656145737735361 22365168432492109303301521)
  ·
    refine ⟨16773876324369081977476141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22365168432492109303301521 16773876324369081977476141)
    ·
      refine ⟨6290203621638405741553553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16773876324369081977476141 6290203621638405741553553)
      ·
        refine ⟨4717652716228804306165165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6290203621638405741553553 4717652716228804306165165)
        ·
          refine ⟨1769119768585801614811937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4717652716228804306165165 1769119768585801614811937)
          ·
            refine ⟨1326839826439351211108953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1769119768585801614811937 1326839826439351211108953)
            ·
              refine ⟨995129869829513408331715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1326839826439351211108953 995129869829513408331715)
              ·
                refine ⟨1492694804744270112497573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995129869829513408331715 1492694804744270112497573)
                ·
                  refine ⟨279880275889550646093295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1492694804744270112497573 279880275889550646093295)
                  ·
                    rfl

theorem cell21_1226396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_1226396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226396 prefixEnd_1226396 := by exact prefixLift 1226396
  have htrace : WordTrace (prefixWord ++ tailWord_1226396) baseStart_1226396 baseEnd_1226396 := by
    simpa [prefixWord, tailWord_1226396, baseEnd_1226396] using wordTrace_append hprefix tailTrace_1226396
  have hstable : (prefixWord ++ tailWord_1226396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226396).length < 2 ^ (prefixWord ++ tailWord_1226396).sum := by decide
  have hdescent : baseEnd_1226396 < baseStart_1226396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226483 : List Nat := [1, 1, 1, 2, 2, 3, 3, 5, 3]
def baseStart_1226483 : Nat := 118140960795 + 1226483 * 2 ^ 59
def prefixEnd_1226483 : Nat := 4983230072969 + 3 ^ 40 * 1226483 * 2
def baseEnd_1226483 : Nat := 279900130474857828143117

theorem tailTrace_1226483 : CollatzResearch.WordTrace tailWord_1226483 prefixEnd_1226483 279900130474857828143117 := by
  unfold tailWord_1226483
  simp only [CollatzResearch.WordTrace]
  refine ⟨44733510015669032465020103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29822340010446021643346735 44733510015669032465020103)
  ·
    refine ⟨67100265023503548697530155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44733510015669032465020103 67100265023503548697530155)
    ·
      refine ⟨100650397535255323046295233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67100265023503548697530155 100650397535255323046295233)
      ·
        refine ⟨75487798151441492284721425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100650397535255323046295233 75487798151441492284721425)
        ·
          refine ⟨56615848613581119213541069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75487798151441492284721425 56615848613581119213541069)
          ·
            refine ⟨21230943230092919705077901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56615848613581119213541069 21230943230092919705077901)
            ·
              refine ⟨7961603711284844889404213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21230943230092919705077901 7961603711284844889404213)
              ·
                refine ⟨746400347932954208381645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7961603711284844889404213 746400347932954208381645)
                ·
                  refine ⟨279900130474857828143117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746400347932954208381645 279900130474857828143117)
                  ·
                    rfl

theorem cell21_1226483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 5, 3].length) (baseStart_1226483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226483 prefixEnd_1226483 := by exact prefixLift 1226483
  have htrace : WordTrace (prefixWord ++ tailWord_1226483) baseStart_1226483 baseEnd_1226483 := by
    simpa [prefixWord, tailWord_1226483, baseEnd_1226483] using wordTrace_append hprefix tailTrace_1226483
  have hstable : (prefixWord ++ tailWord_1226483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226483).length < 2 ^ (prefixWord ++ tailWord_1226483).sum := by decide
  have hdescent : baseEnd_1226483 < baseStart_1226483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226500 : List Nat := [2, 3, 2, 2, 1, 2, 2, 4, 3]
def baseStart_1226500 : Nat := 118140960795 + 1226500 * 2 ^ 59
def prefixEnd_1226500 : Nat := 4983230072969 + 3 ^ 40 * 1226500 * 2
def baseEnd_1226500 : Nat := 279904010106469576359749

theorem tailTrace_1226500 : CollatzResearch.WordTrace tailWord_1226500 prefixEnd_1226500 279904010106469576359749 := by
  unfold tailWord_1226500
  simp only [CollatzResearch.WordTrace]
  refine ⟨22367065028303722184194477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29822753371071629578925969 22367065028303722184194477)
  ·
    refine ⟨8387649385613895819072929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22367065028303722184194477 8387649385613895819072929)
    ·
      refine ⟨6290737039210421864304697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8387649385613895819072929 6290737039210421864304697)
      ·
        refine ⟨4718052779407816398228523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6290737039210421864304697 4718052779407816398228523)
        ·
          refine ⟨7077079169111724597342785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4718052779407816398228523 7077079169111724597342785)
          ·
            refine ⟨5307809376833793448007089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7077079169111724597342785 5307809376833793448007089)
            ·
              refine ⟨3980857032625345086005317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5307809376833793448007089 3980857032625345086005317)
              ·
                refine ⟨746410693617252203625997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3980857032625345086005317 746410693617252203625997)
                ·
                  refine ⟨279904010106469576359749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746410693617252203625997 279904010106469576359749)
                  ·
                    rfl

theorem cell21_1226500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_1226500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226500 prefixEnd_1226500 := by exact prefixLift 1226500
  have htrace : WordTrace (prefixWord ++ tailWord_1226500) baseStart_1226500 baseEnd_1226500 := by
    simpa [prefixWord, tailWord_1226500, baseEnd_1226500] using wordTrace_append hprefix tailTrace_1226500
  have hstable : (prefixWord ++ tailWord_1226500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226500).length < 2 ^ (prefixWord ++ tailWord_1226500).sum := by decide
  have hdescent : baseEnd_1226500 < baseStart_1226500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226638 : List Nat := [4, 1, 1, 5, 1, 1, 3, 5]
def baseStart_1226638 : Nat := 118140960795 + 1226638 * 2 ^ 59
def prefixEnd_1226638 : Nat := 4983230072969 + 3 ^ 40 * 1226638 * 2
def baseEnd_1226638 : Nat := 93311834528870667686489

theorem tailTrace_1226638 : CollatzResearch.WordTrace tailWord_1226638 prefixEnd_1226638 93311834528870667686489 := by
  unfold tailWord_1226638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5592395416263436742114071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29826108886738329291275045 5592395416263436742114071)
  ·
    refine ⟨8388593124395155113171107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5592395416263436742114071 8388593124395155113171107)
    ·
      refine ⟨12582889686592732669756661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8388593124395155113171107 12582889686592732669756661)
      ·
        refine ⟨1179645908118068687789687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12582889686592732669756661 1179645908118068687789687)
        ·
          refine ⟨1769468862177103031684531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1179645908118068687789687 1769468862177103031684531)
          ·
            refine ⟨2654203293265654547526797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1769468862177103031684531 2654203293265654547526797)
            ·
              refine ⟨995326234974620455322549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2654203293265654547526797 995326234974620455322549)
              ·
                refine ⟨93311834528870667686489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 995326234974620455322549 93311834528870667686489)
                ·
                  rfl

theorem cell21_1226638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_1226638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226638 prefixEnd_1226638 := by exact prefixLift 1226638
  have htrace : WordTrace (prefixWord ++ tailWord_1226638) baseStart_1226638 baseEnd_1226638 := by
    simpa [prefixWord, tailWord_1226638, baseEnd_1226638] using wordTrace_append hprefix tailTrace_1226638
  have hstable : (prefixWord ++ tailWord_1226638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226638).length < 2 ^ (prefixWord ++ tailWord_1226638).sum := by decide
  have hdescent : baseEnd_1226638 < baseStart_1226638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226652 : List Nat := [2, 2, 3, 3, 1, 1, 1, 5, 3]
def baseStart_1226652 : Nat := 118140960795 + 1226652 * 2 ^ 59
def prefixEnd_1226652 : Nat := 4983230072969 + 3 ^ 40 * 1226652 * 2
def baseEnd_1226652 : Nat := 279938698577351089826105

theorem tailTrace_1226652 : CollatzResearch.WordTrace tailWord_1226652 prefixEnd_1226652 279938698577351089826105 := by
  unfold tailWord_1226652
  simp only [CollatzResearch.WordTrace]
  refine ⟨22369836976028387163961105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29826449301371182885281473 22369836976028387163961105)
  ·
    refine ⟨16777377732021290372970829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22369836976028387163961105 16777377732021290372970829)
    ·
      refine ⟨6291516649507983889864061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16777377732021290372970829 6291516649507983889864061)
      ·
        refine ⟨2359318743565493958699023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6291516649507983889864061 2359318743565493958699023)
        ·
          refine ⟨3538978115348240938048535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359318743565493958699023 3538978115348240938048535)
          ·
            refine ⟨5308467173022361407072803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3538978115348240938048535 5308467173022361407072803)
            ·
              refine ⟨7962700759533542110609205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5308467173022361407072803 7962700759533542110609205)
              ·
                refine ⟨746503196206269572869613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7962700759533542110609205 746503196206269572869613)
                ·
                  refine ⟨279938698577351089826105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746503196206269572869613 279938698577351089826105)
                  ·
                    rfl

theorem cell21_1226652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_1226652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226652 prefixEnd_1226652 := by exact prefixLift 1226652
  have htrace : WordTrace (prefixWord ++ tailWord_1226652) baseStart_1226652 baseEnd_1226652 := by
    simpa [prefixWord, tailWord_1226652, baseEnd_1226652] using wordTrace_append hprefix tailTrace_1226652
  have hstable : (prefixWord ++ tailWord_1226652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226652).length < 2 ^ (prefixWord ++ tailWord_1226652).sum := by decide
  have hdescent : baseEnd_1226652 < baseStart_1226652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226787 : List Nat := [1, 1, 1, 4, 3, 1, 3, 4, 3]
def baseStart_1226787 : Nat := 118140960795 + 1226787 * 2 ^ 59
def prefixEnd_1226787 : Nat := 4983230072969 + 3 ^ 40 * 1226787 * 2
def baseEnd_1226787 : Nat := 279969507416620855075829

theorem tailTrace_1226787 : CollatzResearch.WordTrace tailWord_1226787 prefixEnd_1226787 279969507416620855075829 := by
  unfold tailWord_1226787
  simp only [CollatzResearch.WordTrace]
  refine ⟨44744597806567692384086615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29829731871045128256057743 44744597806567692384086615)
  ·
    refine ⟨67116896709851538576129923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44744597806567692384086615 67116896709851538576129923)
    ·
      refine ⟨100675345064777307864194885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67116896709851538576129923 100675345064777307864194885)
      ·
        refine ⟨18876627199645745224536541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100675345064777307864194885 18876627199645745224536541)
        ·
          refine ⟨7078735199867154459201203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18876627199645745224536541 7078735199867154459201203)
          ·
            refine ⟨10618102799800731688801805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7078735199867154459201203 10618102799800731688801805)
            ·
              refine ⟨3981788549925274383300677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10618102799800731688801805 3981788549925274383300677)
              ·
                refine ⟨746585353110988946868877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3981788549925274383300677 746585353110988946868877)
                ·
                  refine ⟨279969507416620855075829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 746585353110988946868877 279969507416620855075829)
                  ·
                    rfl

theorem cell21_1226787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 4, 3].length) (baseStart_1226787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226787 prefixEnd_1226787 := by exact prefixLift 1226787
  have htrace : WordTrace (prefixWord ++ tailWord_1226787) baseStart_1226787 baseEnd_1226787 := by
    simpa [prefixWord, tailWord_1226787, baseEnd_1226787] using wordTrace_append hprefix tailTrace_1226787
  have hstable : (prefixWord ++ tailWord_1226787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226787).length < 2 ^ (prefixWord ++ tailWord_1226787).sum := by decide
  have hdescent : baseEnd_1226787 < baseStart_1226787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1226801 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 4]
def baseStart_1226801 : Nat := 118140960795 + 1226801 * 2 ^ 59
def prefixEnd_1226801 : Nat := 4983230072969 + 3 ^ 40 * 1226801 * 2
def baseEnd_1226801 : Nat := 279972702407359941842467

theorem tailTrace_1226801 : CollatzResearch.WordTrace tailWord_1226801 prefixEnd_1226801 279972702407359941842467 := by
  unfold tailWord_1226801
  simp only [CollatzResearch.WordTrace]
  refine ⟨44745108428516972775096257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29830072285677981850064171 44745108428516972775096257)
  ·
    refine ⟨33558831321387729581322193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44745108428516972775096257 33558831321387729581322193)
    ·
      refine ⟨25169123491040797185991645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33558831321387729581322193 25169123491040797185991645)
      ·
        refine ⟨9438421309140298944746867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25169123491040797185991645 9438421309140298944746867)
        ·
          refine ⟨14157631963710448417120301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9438421309140298944746867 14157631963710448417120301)
          ·
            refine ⟨5309111986391418156420113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14157631963710448417120301 5309111986391418156420113)
            ·
              refine ⟨3981833989793563617315085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5309111986391418156420113 3981833989793563617315085)
              ·
                refine ⟨1493187746172586356493157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3981833989793563617315085 1493187746172586356493157)
                ·
                  refine ⟨279972702407359941842467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1493187746172586356493157 279972702407359941842467)
                  ·
                    rfl

theorem cell21_1226801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_1226801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1226801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1226801 prefixEnd_1226801 := by exact prefixLift 1226801
  have htrace : WordTrace (prefixWord ++ tailWord_1226801) baseStart_1226801 baseEnd_1226801 := by
    simpa [prefixWord, tailWord_1226801, baseEnd_1226801] using wordTrace_append hprefix tailTrace_1226801
  have hstable : (prefixWord ++ tailWord_1226801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1226801).length < 2 ^ (prefixWord ++ tailWord_1226801).sum := by decide
  have hdescent : baseEnd_1226801 < baseStart_1226801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1226801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
