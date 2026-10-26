import V185TrunkScan23Chunk1085

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6429832 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 7]
def baseStart_6429832 : Nat := 118140960795 + 6429832 * 2 ^ 59
def prefixEnd_6429832 : Nat := 4983230072969 + 3 ^ 40 * 6429832 * 2
def baseEnd_6429832 : Nat := 366843815962221387381083

theorem tailTrace_6429832 : CollatzResearch.WordTrace tailWord_6429832 prefixEnd_6429832 366843815962221387381083 := by
  unfold tailWord_6429832
  simp only [CollatzResearch.WordTrace]
  refine ⟨117257619620912133362141875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156343492827882844482855833 117257619620912133362141875)
  ·
    refine ⟨175886429431368200043212813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117257619620912133362141875 175886429431368200043212813)
    ·
      refine ⟨65957411036763075016204805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175886429431368200043212813 65957411036763075016204805)
      ·
        refine ⟨12367014569393076565538401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65957411036763075016204805 12367014569393076565538401)
        ·
          refine ⟨9275260927044807424153801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12367014569393076565538401 9275260927044807424153801)
          ·
            refine ⟨6956445695283605568115351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9275260927044807424153801 6956445695283605568115351)
            ·
              refine ⟨10434668542925408352173027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6956445695283605568115351 10434668542925408352173027)
              ·
                refine ⟨15652002814388112528259541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10434668542925408352173027 15652002814388112528259541)
                ·
                  refine ⟨366843815962221387381083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15652002814388112528259541 366843815962221387381083)
                  ·
                    rfl

theorem cell23_6429832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 7].length) (baseStart_6429832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429832 prefixEnd_6429832 := by exact prefixLift 6429832
  have htrace : WordTrace (prefixWord ++ tailWord_6429832) baseStart_6429832 baseEnd_6429832 := by
    simpa [prefixWord, tailWord_6429832, baseEnd_6429832] using wordTrace_append hprefix tailTrace_6429832
  have hstable : (prefixWord ++ tailWord_6429832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429832).length < 2 ^ (prefixWord ++ tailWord_6429832).sum := by decide
  have hdescent : baseEnd_6429832 < baseStart_6429832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429975 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_6429975 : Nat := 118140960795 + 6429975 * 2 ^ 59
def prefixEnd_6429975 : Nat := 4983230072969 + 3 ^ 40 * 6429975 * 2
def baseEnd_6429975 : Nat := 3301667771393585426941589

theorem tailTrace_6429975 : CollatzResearch.WordTrace tailWord_6429975 prefixEnd_6429975 3301667771393585426941589 := by
  unfold tailWord_6429975
  simp only [CollatzResearch.WordTrace]
  refine ⟨234520454880306202146739379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156346969920204134764492919 234520454880306202146739379)
  ·
    refine ⟨351780682320459303220109069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234520454880306202146739379 351780682320459303220109069)
    ·
      refine ⟨131917755870172238707540901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351780682320459303220109069 131917755870172238707540901)
      ·
        refine ⟨24734579225657294757663919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131917755870172238707540901 24734579225657294757663919)
        ·
          refine ⟨37101868838485942136495879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24734579225657294757663919 37101868838485942136495879)
          ·
            refine ⟨55652803257728913204743819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37101868838485942136495879 55652803257728913204743819)
            ·
              refine ⟨83479204886593369807115729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55652803257728913204743819 83479204886593369807115729)
              ·
                refine ⟨62609403664945027355336797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83479204886593369807115729 62609403664945027355336797)
                ·
                  refine ⟨23478526374354385258251299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62609403664945027355336797 23478526374354385258251299)
                  ·
                    refine ⟨35217789561531577887376949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23478526374354385258251299 35217789561531577887376949)
                    ·
                      refine ⟨3301667771393585426941589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35217789561531577887376949 3301667771393585426941589)
                      ·
                        rfl

theorem cell23_6429975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_6429975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429975 prefixEnd_6429975 := by exact prefixLift 6429975
  have htrace : WordTrace (prefixWord ++ tailWord_6429975) baseStart_6429975 baseEnd_6429975 := by
    simpa [prefixWord, tailWord_6429975, baseEnd_6429975] using wordTrace_append hprefix tailTrace_6429975
  have hstable : (prefixWord ++ tailWord_6429975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429975).length < 2 ^ (prefixWord ++ tailWord_6429975).sum := by decide
  have hdescent : baseEnd_6429975 < baseStart_6429975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429983 : List Nat := [1, 1, 2, 4, 4, 2, 1, 3, 1, 1, 3]
def baseStart_6429983 : Nat := 118140960795 + 6429983 * 2 ^ 59
def prefixEnd_6429983 : Nat := 4983230072969 + 3 ^ 40 * 6429983 * 2
def baseEnd_6429983 : Nat := 3301671879238821395641553

theorem tailTrace_6429983 : CollatzResearch.WordTrace tailWord_6429983 prefixEnd_6429983 3301671879238821395641553 := by
  unfold tailWord_6429983
  simp only [CollatzResearch.WordTrace]
  refine ⟨234520746664277219513030603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156347164442851479675353735 234520746664277219513030603)
  ·
    refine ⟨351781119996415829269545905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234520746664277219513030603 351781119996415829269545905)
    ·
      refine ⟨263835839997311871952159429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351781119996415829269545905 263835839997311871952159429)
      ·
        refine ⟨49469219999495975991029893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263835839997311871952159429 49469219999495975991029893)
        ·
          refine ⟨9275478749905495498318105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49469219999495975991029893 9275478749905495498318105)
          ·
            refine ⟨6956609062429121623738579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9275478749905495498318105 6956609062429121623738579)
            ·
              refine ⟨10434913593643682435607869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6956609062429121623738579 10434913593643682435607869)
              ·
                refine ⟨3913092597616380913352951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10434913593643682435607869 3913092597616380913352951)
                ·
                  refine ⟨5869638896424571370029427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3913092597616380913352951 5869638896424571370029427)
                  ·
                    refine ⟨8804458344636857055044141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5869638896424571370029427 8804458344636857055044141)
                    ·
                      refine ⟨3301671879238821395641553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8804458344636857055044141 3301671879238821395641553)
                      ·
                        rfl

theorem cell23_6429983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_6429983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429983 prefixEnd_6429983 := by exact prefixLift 6429983
  have htrace : WordTrace (prefixWord ++ tailWord_6429983) baseStart_6429983 baseEnd_6429983 := by
    simpa [prefixWord, tailWord_6429983, baseEnd_6429983] using wordTrace_append hprefix tailTrace_6429983
  have hstable : (prefixWord ++ tailWord_6429983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429983).length < 2 ^ (prefixWord ++ tailWord_6429983).sum := by decide
  have hdescent : baseEnd_6429983 < baseStart_6429983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429985 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_6429985 : Nat := 118140960795 + 6429985 * 2 ^ 59
def prefixEnd_6429985 : Nat := 4983230072969 + 3 ^ 40 * 6429985 * 2
def baseEnd_6429985 : Nat := 3301672906200130387816543

theorem tailTrace_6429985 : CollatzResearch.WordTrace tailWord_6429985 prefixEnd_6429985 3301672906200130387816543 := by
  unfold tailWord_6429985
  simp only [CollatzResearch.WordTrace]
  refine ⟨234520819610269973854603409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156347213073513315903068939 234520819610269973854603409)
  ·
    refine ⟨175890614707702480390952557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234520819610269973854603409 175890614707702480390952557)
    ·
      refine ⟨65958980515388430146607209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175890614707702480390952557 65958980515388430146607209)
      ·
        refine ⟨49469235386541322609955407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65958980515388430146607209 49469235386541322609955407)
        ·
          refine ⟨74203853079811983914933111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49469235386541322609955407 74203853079811983914933111)
          ·
            refine ⟨111305779619717975872399667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74203853079811983914933111 111305779619717975872399667)
            ·
              refine ⟨166958669429576963808599501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111305779619717975872399667 166958669429576963808599501)
              ·
                refine ⟨62609501036091361428224813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166958669429576963808599501 62609501036091361428224813)
                ·
                  refine ⟨23478562888534260535584305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62609501036091361428224813 23478562888534260535584305)
                  ·
                    refine ⟨17608922166400695401688229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23478562888534260535584305 17608922166400695401688229)
                    ·
                      refine ⟨3301672906200130387816543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17608922166400695401688229 3301672906200130387816543)
                      ·
                        rfl

theorem cell23_6429985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_6429985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429985 prefixEnd_6429985 := by exact prefixLift 6429985
  have htrace : WordTrace (prefixWord ++ tailWord_6429985) baseStart_6429985 baseEnd_6429985 := by
    simpa [prefixWord, tailWord_6429985, baseEnd_6429985] using wordTrace_append hprefix tailTrace_6429985
  have hstable : (prefixWord ++ tailWord_6429985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429985).length < 2 ^ (prefixWord ++ tailWord_6429985).sum := by decide
  have hdescent : baseEnd_6429985 < baseStart_6429985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6429992 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_6429992 : Nat := 118140960795 + 6429992 * 2 ^ 59
def prefixEnd_6429992 : Nat := 4983230072969 + 3 ^ 40 * 6429992 * 2
def baseEnd_6429992 : Nat := 3301676500564711860429011

theorem tailTrace_6429992 : CollatzResearch.WordTrace tailWord_6429992 prefixEnd_6429992 3301676500564711860429011 := by
  unfold tailWord_6429992
  simp only [CollatzResearch.WordTrace]
  refine ⟨117260537460622307025054115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156347383280829742700072153 117260537460622307025054115)
  ·
    refine ⟨175890806190933460537581173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117260537460622307025054115 175890806190933460537581173)
    ·
      refine ⟨16489763080400011925398235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175890806190933460537581173 16489763080400011925398235)
      ·
        refine ⟨24734644620600017888097353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16489763080400011925398235 24734644620600017888097353)
        ·
          refine ⟨18550983465450013416073015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24734644620600017888097353 18550983465450013416073015)
          ·
            refine ⟨27826475198175020124109523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18550983465450013416073015 27826475198175020124109523)
            ·
              refine ⟨41739712797262530186164285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27826475198175020124109523 41739712797262530186164285)
              ·
                refine ⟨15652392298973448819811607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41739712797262530186164285 15652392298973448819811607)
                ·
                  refine ⟨23478588448460173229717411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15652392298973448819811607 23478588448460173229717411)
                  ·
                    refine ⟨35217882672690259844576117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23478588448460173229717411 35217882672690259844576117)
                    ·
                      refine ⟨3301676500564711860429011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35217882672690259844576117 3301676500564711860429011)
                      ·
                        rfl

theorem cell23_6429992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_6429992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6429992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6429992 prefixEnd_6429992 := by exact prefixLift 6429992
  have htrace : WordTrace (prefixWord ++ tailWord_6429992) baseStart_6429992 baseEnd_6429992 := by
    simpa [prefixWord, tailWord_6429992, baseEnd_6429992] using wordTrace_append hprefix tailTrace_6429992
  have hstable : (prefixWord ++ tailWord_6429992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6429992).length < 2 ^ (prefixWord ++ tailWord_6429992).sum := by decide
  have hdescent : baseEnd_6429992 < baseStart_6429992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6429992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430049 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 1, 3, 2]
def baseStart_6430049 : Nat := 118140960795 + 6430049 * 2 ^ 59
def prefixEnd_6430049 : Nat := 4983230072969 + 3 ^ 40 * 6430049 * 2
def baseEnd_6430049 : Nat := 3301705768962018137416249

theorem tailTrace_6430049 : CollatzResearch.WordTrace tailWord_6430049 prefixEnd_6430049 3301705768962018137416249 := by
  unfold tailWord_6430049
  simp only [CollatzResearch.WordTrace]
  refine ⟨234523153882038112784933201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156348769254692075189955467 234523153882038112784933201)
  ·
    refine ⟨175892365411528584588699901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234523153882038112784933201 175892365411528584588699901)
    ·
      refine ⟨65959637029323219220762463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175892365411528584588699901 65959637029323219220762463)
      ·
        refine ⟨98939455543984828831143695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65959637029323219220762463 98939455543984828831143695)
        ·
          refine ⟨148409183315977243246715543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98939455543984828831143695 148409183315977243246715543)
          ·
            refine ⟨222613774973965864870073315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148409183315977243246715543 222613774973965864870073315)
            ·
              refine ⟨333920662460948797305109973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222613774973965864870073315 333920662460948797305109973)
              ·
                refine ⟨7826265526428487436838515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 333920662460948797305109973 7826265526428487436838515)
                ·
                  refine ⟨11739398289642731155257773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7826265526428487436838515 11739398289642731155257773)
                  ·
                    refine ⟨4402274358616024183221665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11739398289642731155257773 4402274358616024183221665)
                    ·
                      refine ⟨3301705768962018137416249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402274358616024183221665 3301705768962018137416249)
                      ·
                        rfl

theorem cell23_6430049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_6430049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430049 prefixEnd_6430049 := by exact prefixLift 6430049
  have htrace : WordTrace (prefixWord ++ tailWord_6430049) baseStart_6430049 baseEnd_6430049 := by
    simpa [prefixWord, tailWord_6430049, baseEnd_6430049] using wordTrace_append hprefix tailTrace_6430049
  have hstable : (prefixWord ++ tailWord_6430049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430049).length < 2 ^ (prefixWord ++ tailWord_6430049).sum := by decide
  have hdescent : baseEnd_6430049 < baseStart_6430049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430065 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_6430065 : Nat := 118140960795 + 6430065 * 2 ^ 59
def prefixEnd_6430065 : Nat := 4983230072969 + 3 ^ 40 * 6430065 * 2
def baseEnd_6430065 : Nat := 3301713984652490074816175

theorem tailTrace_6430065 : CollatzResearch.WordTrace tailWord_6430065 prefixEnd_6430065 3301713984652490074816175 := by
  unfold tailWord_6430065
  simp only [CollatzResearch.WordTrace]
  refine ⟨234523737449980147517515649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156349158299986765011677099 234523737449980147517515649)
  ·
    refine ⟨175892803087485110638136737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234523737449980147517515649 175892803087485110638136737)
    ·
      refine ⟨131919602315613832978602553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175892803087485110638136737 131919602315613832978602553)
      ·
        refine ⟨98939701736710374733951915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131919602315613832978602553 98939701736710374733951915)
        ·
          refine ⟨148409552605065562100927873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98939701736710374733951915 148409552605065562100927873)
          ·
            refine ⟨111307164453799171575695905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148409552605065562100927873 111307164453799171575695905)
            ·
              refine ⟨83480373340349378681771929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111307164453799171575695905 83480373340349378681771929)
              ·
                refine ⟨62610280005262034011328947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83480373340349378681771929 62610280005262034011328947)
                ·
                  refine ⟨93915420007893051016993421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62610280005262034011328947 93915420007893051016993421)
                  ·
                    refine ⟨35218282502959894131372533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93915420007893051016993421 35218282502959894131372533)
                    ·
                      refine ⟨3301713984652490074816175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35218282502959894131372533 3301713984652490074816175)
                      ·
                        rfl

theorem cell23_6430065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_6430065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430065 prefixEnd_6430065 := by exact prefixLift 6430065
  have htrace : WordTrace (prefixWord ++ tailWord_6430065) baseStart_6430065 baseEnd_6430065 := by
    simpa [prefixWord, tailWord_6430065, baseEnd_6430065] using wordTrace_append hprefix tailTrace_6430065
  have hstable : (prefixWord ++ tailWord_6430065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430065).length < 2 ^ (prefixWord ++ tailWord_6430065).sum := by decide
  have hdescent : baseEnd_6430065 < baseStart_6430065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430085 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 9]
def baseStart_6430085 : Nat := 118140960795 + 6430085 * 2 ^ 59
def prefixEnd_6430085 : Nat := 4983230072969 + 3 ^ 40 * 6430085 * 2
def baseEnd_6430085 : Nat := 366858250473953332951787

theorem tailTrace_6430085 : CollatzResearch.WordTrace tailWord_6430085 prefixEnd_6430085 366858250473953332951787 := by
  unfold tailWord_6430085
  simp only [CollatzResearch.WordTrace]
  refine ⟨234524466909907690933243709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156349644606605127288829139 234524466909907690933243709)
  ·
    refine ⟨87946675091215384099966391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234524466909907690933243709 87946675091215384099966391)
    ·
      refine ⟨131920012636823076149949587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87946675091215384099966391 131920012636823076149949587)
      ·
        refine ⟨197880018955234614224924381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131920012636823076149949587 197880018955234614224924381)
        ·
          refine ⟨74205007108212980334346643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197880018955234614224924381 74205007108212980334346643)
          ·
            refine ⟨111307510662319470501519965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74205007108212980334346643 111307510662319470501519965)
            ·
              refine ⟨41740316498369801438069987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111307510662319470501519965 41740316498369801438069987)
              ·
                refine ⟨62610474747554702157104981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41740316498369801438069987 62610474747554702157104981)
                ·
                  refine ⟨366858250473953332951787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62610474747554702157104981 366858250473953332951787)
                  ·
                    rfl

theorem cell23_6430085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_6430085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430085 prefixEnd_6430085 := by exact prefixLift 6430085
  have htrace : WordTrace (prefixWord ++ tailWord_6430085) baseStart_6430085 baseEnd_6430085 := by
    simpa [prefixWord, tailWord_6430085, baseEnd_6430085] using wordTrace_append hprefix tailTrace_6430085
  have hstable : (prefixWord ++ tailWord_6430085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430085).length < 2 ^ (prefixWord ++ tailWord_6430085).sum := by decide
  have hdescent : baseEnd_6430085 < baseStart_6430085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430100 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_6430100 : Nat := 118140960795 + 6430100 * 2 ^ 59
def prefixEnd_6430100 : Nat := 4983230072969 + 3 ^ 40 * 6430100 * 2
def baseEnd_6430100 : Nat := 3301731956475397437878515

theorem tailTrace_6430100 : CollatzResearch.WordTrace tailWord_6430100 prefixEnd_6430100 3301731956475397437878515 := by
  unfold tailWord_6430100
  simp only [CollatzResearch.WordTrace]
  refine ⟨117262507002426674247519877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156350009336568898996693169 117262507002426674247519877)
  ·
    refine ⟨21986720062955001421409977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117262507002426674247519877 21986720062955001421409977)
    ·
      refine ⟨16490040047216251066057483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21986720062955001421409977 16490040047216251066057483)
      ·
        refine ⟨24735060070824376599086225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16490040047216251066057483 24735060070824376599086225)
        ·
          refine ⟨18551295053118282449314669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24735060070824376599086225 18551295053118282449314669)
          ·
            refine ⟨6956735644919355918493001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18551295053118282449314669 6956735644919355918493001)
            ·
              refine ⟨5217551733689516938869751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6956735644919355918493001 5217551733689516938869751)
              ·
                refine ⟨7826327600534275408304627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5217551733689516938869751 7826327600534275408304627)
                ·
                  refine ⟨11739491400801413112456941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7826327600534275408304627 11739491400801413112456941)
                  ·
                    refine ⟨4402309275300529917171353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11739491400801413112456941 4402309275300529917171353)
                    ·
                      refine ⟨3301731956475397437878515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402309275300529917171353 3301731956475397437878515)
                      ·
                        rfl

theorem cell23_6430100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_6430100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430100 prefixEnd_6430100 := by exact prefixLift 6430100
  have htrace : WordTrace (prefixWord ++ tailWord_6430100) baseStart_6430100 baseEnd_6430100 := by
    simpa [prefixWord, tailWord_6430100, baseEnd_6430100] using wordTrace_append hprefix tailTrace_6430100
  have hstable : (prefixWord ++ tailWord_6430100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430100).length < 2 ^ (prefixWord ++ tailWord_6430100).sum := by decide
  have hdescent : baseEnd_6430100 < baseStart_6430100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430112 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 3]
def baseStart_6430112 : Nat := 118140960795 + 6430112 * 2 ^ 59
def prefixEnd_6430112 : Nat := 4983230072969 + 3 ^ 40 * 6430112 * 2
def baseEnd_6430112 : Nat := 3301738118243251390928459

theorem tailTrace_6430112 : CollatzResearch.WordTrace tailWord_6430112 prefixEnd_6430112 3301738118243251390928459 := by
  unfold tailWord_6430112
  simp only [CollatzResearch.WordTrace]
  refine ⟨117262725840404937272238295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156350301120539916362984393 117262725840404937272238295)
  ·
    refine ⟨175894088760607405908357443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117262725840404937272238295 175894088760607405908357443)
    ·
      refine ⟨263841133140911108862536165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175894088760607405908357443 263841133140911108862536165)
      ·
        refine ⟨49470212463920832911725531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263841133140911108862536165 49470212463920832911725531)
        ·
          refine ⟨74205318695881249367588297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49470212463920832911725531 74205318695881249367588297)
          ·
            refine ⟨55653989021910937025691223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74205318695881249367588297 55653989021910937025691223)
            ·
              refine ⟨83480983532866405538536835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55653989021910937025691223 83480983532866405538536835)
              ·
                refine ⟨125221475299299608307805253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83480983532866405538536835 125221475299299608307805253)
                ·
                  refine ⟨23479026618618676557713485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125221475299299608307805253 23479026618618676557713485)
                  ·
                    refine ⟨8804634981982003709142557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23479026618618676557713485 8804634981982003709142557)
                    ·
                      refine ⟨3301738118243251390928459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8804634981982003709142557 3301738118243251390928459)
                      ·
                        rfl

theorem cell23_6430112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_6430112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430112 prefixEnd_6430112 := by exact prefixLift 6430112
  have htrace : WordTrace (prefixWord ++ tailWord_6430112) baseStart_6430112 baseEnd_6430112 := by
    simpa [prefixWord, tailWord_6430112, baseEnd_6430112] using wordTrace_append hprefix tailTrace_6430112
  have hstable : (prefixWord ++ tailWord_6430112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430112).length < 2 ^ (prefixWord ++ tailWord_6430112).sum := by decide
  have hdescent : baseEnd_6430112 < baseStart_6430112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430119 : List Nat := [1, 1, 6, 1, 1, 1, 1, 6, 5]
def baseStart_6430119 : Nat := 118140960795 + 6430119 * 2 ^ 59
def prefixEnd_6430119 : Nat := 4983230072969 + 3 ^ 40 * 6430119 * 2
def baseEnd_6430119 : Nat := 366860190289759207060103

theorem tailTrace_6430119 : CollatzResearch.WordTrace tailWord_6430119 prefixEnd_6430119 366860190289759207060103 := by
  unfold tailWord_6430119
  simp only [CollatzResearch.WordTrace]
  refine ⟨234525706991784514739981411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156350471327856343159987607 234525706991784514739981411)
  ·
    refine ⟨351788560487676772109972117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234525706991784514739981411 351788560487676772109972117)
    ·
      refine ⟨16490088772859848692654943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 351788560487676772109972117 16490088772859848692654943)
      ·
        refine ⟨24735133159289773038982415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16490088772859848692654943 24735133159289773038982415)
        ·
          refine ⟨37102699738934659558473623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24735133159289773038982415 37102699738934659558473623)
          ·
            refine ⟨55654049608401989337710435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37102699738934659558473623 55654049608401989337710435)
            ·
              refine ⟨83481074412602984006565653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55654049608401989337710435 83481074412602984006565653)
              ·
                refine ⟨3913175363090764875307765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83481074412602984006565653 3913175363090764875307765)
                ·
                  refine ⟨366860190289759207060103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3913175363090764875307765 366860190289759207060103)
                  ·
                    rfl

theorem cell23_6430119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 5].length) (baseStart_6430119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430119 prefixEnd_6430119 := by exact prefixLift 6430119
  have htrace : WordTrace (prefixWord ++ tailWord_6430119) baseStart_6430119 baseEnd_6430119 := by
    simpa [prefixWord, tailWord_6430119, baseEnd_6430119] using wordTrace_append hprefix tailTrace_6430119
  have hstable : (prefixWord ++ tailWord_6430119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430119).length < 2 ^ (prefixWord ++ tailWord_6430119).sum := by decide
  have hdescent : baseEnd_6430119 < baseStart_6430119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430142 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_6430142 : Nat := 118140960795 + 6430142 * 2 ^ 59
def prefixEnd_6430142 : Nat := 4983230072969 + 3 ^ 40 * 6430142 * 2
def baseEnd_6430142 : Nat := 3301753522662886273553321

theorem tailTrace_6430142 : CollatzResearch.WordTrace tailWord_6430142 prefixEnd_6430142 3301753522662886273553321 := by
  unfold tailWord_6430142
  simp only [CollatzResearch.WordTrace]
  refine ⟨29315818233837648708508585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156351030580467459778712453 29315818233837648708508585)
  ·
    refine ⟨21986863675378236531381439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29315818233837648708508585 21986863675378236531381439)
    ·
      refine ⟨32980295513067354797072159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21986863675378236531381439 32980295513067354797072159)
      ·
        refine ⟨49470443269601032195608239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32980295513067354797072159 49470443269601032195608239)
        ·
          refine ⟨74205664904401548293412359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49470443269601032195608239 74205664904401548293412359)
          ·
            refine ⟨111308497356602322440118539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74205664904401548293412359 111308497356602322440118539)
            ·
              refine ⟨166962746034903483660177809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111308497356602322440118539 166962746034903483660177809)
              ·
                refine ⟨125222059526177612745133357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166962746034903483660177809 125222059526177612745133357)
                ·
                  refine ⟨46958272322316604779425009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125222059526177612745133357 46958272322316604779425009)
                  ·
                    refine ⟨35218704241737453584568757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46958272322316604779425009 35218704241737453584568757)
                    ·
                      refine ⟨3301753522662886273553321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35218704241737453584568757 3301753522662886273553321)
                      ·
                        rfl

theorem cell23_6430142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_6430142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430142 prefixEnd_6430142 := by exact prefixLift 6430142
  have htrace : WordTrace (prefixWord ++ tailWord_6430142) baseStart_6430142 baseEnd_6430142 := by
    simpa [prefixWord, tailWord_6430142, baseEnd_6430142] using wordTrace_append hprefix tailTrace_6430142
  have hstable : (prefixWord ++ tailWord_6430142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430142).length < 2 ^ (prefixWord ++ tailWord_6430142).sum := by decide
  have hdescent : baseEnd_6430142 < baseStart_6430142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430152 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_6430152 : Nat := 118140960795 + 6430152 * 2 ^ 59
def prefixEnd_6430152 : Nat := 4983230072969 + 3 ^ 40 * 6430152 * 2
def baseEnd_6430152 : Nat := 3301758657469431234428275

theorem tailTrace_6430152 : CollatzResearch.WordTrace tailWord_6430152 prefixEnd_6430152 3301758657469431234428275 := by
  unfold tailWord_6430152
  simp only [CollatzResearch.WordTrace]
  refine ⟨117263455300332480687966355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156351273733776640917288473 117263455300332480687966355)
  ·
    refine ⟨175895182950498721031949533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117263455300332480687966355 175895182950498721031949533)
    ·
      refine ⟨65960693606437020386981075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175895182950498721031949533 65960693606437020386981075)
      ·
        refine ⟨98941040409655530580471613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65960693606437020386981075 98941040409655530580471613)
        ·
          refine ⟨37102890153620823967676855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98941040409655530580471613 37102890153620823967676855)
          ·
            refine ⟨55654335230431235951515283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37102890153620823967676855 55654335230431235951515283)
            ·
              refine ⟨83481502845646853927272925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55654335230431235951515283 83481502845646853927272925)
              ·
                refine ⟨31305563567117570222727347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83481502845646853927272925 31305563567117570222727347)
                ·
                  refine ⟨46958345350676355334091021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31305563567117570222727347 46958345350676355334091021)
                  ·
                    refine ⟨17609379506503633250284133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46958345350676355334091021 17609379506503633250284133)
                    ·
                      refine ⟨3301758657469431234428275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17609379506503633250284133 3301758657469431234428275)
                      ·
                        rfl

theorem cell23_6430152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_6430152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430152 prefixEnd_6430152 := by exact prefixLift 6430152
  have htrace : WordTrace (prefixWord ++ tailWord_6430152) baseStart_6430152 baseEnd_6430152 := by
    simpa [prefixWord, tailWord_6430152, baseEnd_6430152] using wordTrace_append hprefix tailTrace_6430152
  have hstable : (prefixWord ++ tailWord_6430152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430152).length < 2 ^ (prefixWord ++ tailWord_6430152).sum := by decide
  have hdescent : baseEnd_6430152 < baseStart_6430152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430166 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_6430166 : Nat := 118140960795 + 6430166 * 2 ^ 59
def prefixEnd_6430166 : Nat := 4983230072969 + 3 ^ 40 * 6430166 * 2
def baseEnd_6430166 : Nat := 1100588615399531393217737

theorem tailTrace_6430166 : CollatzResearch.WordTrace tailWord_6430166 prefixEnd_6430166 1100588615399531393217737 := by
  unfold tailWord_6430166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14657963826413390110433897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156351614148409494511294901 14657963826413390110433897)
  ·
    refine ⟨10993472869810042582825423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14657963826413390110433897 10993472869810042582825423)
    ·
      refine ⟨16490209304715063874238135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10993472869810042582825423 16490209304715063874238135)
      ·
        refine ⟨24735313957072595811357203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16490209304715063874238135 24735313957072595811357203)
        ·
          refine ⟨37102970935608893717035805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24735313957072595811357203 37102970935608893717035805)
          ·
            refine ⟨13913614100853335143888427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37102970935608893717035805 13913614100853335143888427)
            ·
              refine ⟨20870421151280002715832641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13913614100853335143888427 20870421151280002715832641)
              ·
                refine ⟨15652815863460002036874481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20870421151280002715832641 15652815863460002036874481)
                ·
                  refine ⟨11739611897595001527655861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15652815863460002036874481 11739611897595001527655861)
                  ·
                    refine ⟨1100588615399531393217737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11739611897595001527655861 1100588615399531393217737)
                    ·
                      rfl

theorem cell23_6430166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_6430166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430166 prefixEnd_6430166 := by exact prefixLift 6430166
  have htrace : WordTrace (prefixWord ++ tailWord_6430166) baseStart_6430166 baseEnd_6430166 := by
    simpa [prefixWord, tailWord_6430166, baseEnd_6430166] using wordTrace_append hprefix tailTrace_6430166
  have hstable : (prefixWord ++ tailWord_6430166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430166).length < 2 ^ (prefixWord ++ tailWord_6430166).sum := by decide
  have hdescent : baseEnd_6430166 < baseStart_6430166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430169 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 4]
def baseStart_6430169 : Nat := 118140960795 + 6430169 * 2 ^ 59
def prefixEnd_6430169 : Nat := 4983230072969 + 3 ^ 40 * 6430169 * 2
def baseEnd_6430169 : Nat := 3301767386640557667915697

theorem tailTrace_6430169 : CollatzResearch.WordTrace tailWord_6430169 prefixEnd_6430169 3301767386640557667915697 := by
  unfold tailWord_6430169
  simp only [CollatzResearch.WordTrace]
  refine ⟨234527530641603373279301561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156351687094402248852867707 234527530641603373279301561)
  ·
    refine ⟨175895647981202529959476171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234527530641603373279301561 175895647981202529959476171)
    ·
      refine ⟨263843471971803794939214257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175895647981202529959476171 263843471971803794939214257)
      ·
        refine ⟨197882603978852846204410693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263843471971803794939214257 197882603978852846204410693)
        ·
          refine ⟨37102988246034908663327005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197882603978852846204410693 37102988246034908663327005)
          ·
            refine ⟨13913620592263090748747627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37102988246034908663327005 13913620592263090748747627)
            ·
              refine ⟨20870430888394636123121441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13913620592263090748747627 20870430888394636123121441)
              ·
                refine ⟨15652823166295977092341081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20870430888394636123121441 15652823166295977092341081)
                ·
                  refine ⟨11739617374721982819255811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15652823166295977092341081 11739617374721982819255811)
                  ·
                    refine ⟨17609426062082974228883717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11739617374721982819255811 17609426062082974228883717)
                    ·
                      refine ⟨3301767386640557667915697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17609426062082974228883717 3301767386640557667915697)
                      ·
                        rfl

theorem cell23_6430169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_6430169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430169 prefixEnd_6430169 := by exact prefixLift 6430169
  have htrace : WordTrace (prefixWord ++ tailWord_6430169) baseStart_6430169 baseEnd_6430169 := by
    simpa [prefixWord, tailWord_6430169, baseEnd_6430169] using wordTrace_append hprefix tailTrace_6430169
  have hstable : (prefixWord ++ tailWord_6430169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430169).length < 2 ^ (prefixWord ++ tailWord_6430169).sum := by decide
  have hdescent : baseEnd_6430169 < baseStart_6430169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430236 : List Nat := [2, 2, 3, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_6430236 : Nat := 118140960795 + 6430236 * 2 ^ 59
def prefixEnd_6430236 : Nat := 4983230072969 + 3 ^ 40 * 6430236 * 2
def baseEnd_6430236 : Nat := 3301801789844408905777889

theorem tailTrace_6430236 : CollatzResearch.WordTrace tailWord_6430236 prefixEnd_6430236 3301801789844408905777889 := by
  unfold tailWord_6430236
  simp only [CollatzResearch.WordTrace]
  refine ⟨117264987166180321860995281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156353316221573762481327041 117264987166180321860995281)
  ·
    refine ⟨87948740374635241395746461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117264987166180321860995281 87948740374635241395746461)
    ·
      refine ⟨32980777640488215523404923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87948740374635241395746461 32980777640488215523404923)
      ·
        refine ⟨49471166460732323285107385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32980777640488215523404923 49471166460732323285107385)
        ·
          refine ⟨37103374845549242463830539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49471166460732323285107385 37103374845549242463830539)
          ·
            refine ⟨55655062268323863695745809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37103374845549242463830539 55655062268323863695745809)
            ·
              refine ⟨41741296701242897771809357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55655062268323863695745809 41741296701242897771809357)
              ·
                refine ⟨15652986262966086664428509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41741296701242897771809357 15652986262966086664428509)
                ·
                  refine ⟨5869869848612282499160691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15652986262966086664428509 5869869848612282499160691)
                  ·
                    refine ⟨8804804772918423748741037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5869869848612282499160691 8804804772918423748741037)
                    ·
                      refine ⟨3301801789844408905777889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8804804772918423748741037 3301801789844408905777889)
                      ·
                        rfl

theorem cell23_6430236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_6430236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430236 prefixEnd_6430236 := by exact prefixLift 6430236
  have htrace : WordTrace (prefixWord ++ tailWord_6430236) baseStart_6430236 baseEnd_6430236 := by
    simpa [prefixWord, tailWord_6430236, baseEnd_6430236] using wordTrace_append hprefix tailTrace_6430236
  have hstable : (prefixWord ++ tailWord_6430236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430236).length < 2 ^ (prefixWord ++ tailWord_6430236).sum := by decide
  have hdescent : baseEnd_6430236 < baseStart_6430236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430259 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 4]
def baseStart_6430259 : Nat := 118140960795 + 6430259 * 2 ^ 59
def prefixEnd_6430259 : Nat := 4983230072969 + 3 ^ 40 * 6430259 * 2
def baseEnd_6430259 : Nat := 3301813599899462315790283

theorem tailTrace_6430259 : CollatzResearch.WordTrace tailWord_6430259 prefixEnd_6430259 3301813599899462315790283 := by
  unfold tailWord_6430259
  simp only [CollatzResearch.WordTrace]
  refine ⟨234530813211277318650077831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156353875474184879100051887 234530813211277318650077831)
  ·
    refine ⟨351796219816915977975116747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234530813211277318650077831 351796219816915977975116747)
    ·
      refine ⟨527694329725373966962675121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351796219816915977975116747 527694329725373966962675121)
      ·
        refine ⟨395770747294030475222006341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527694329725373966962675121 395770747294030475222006341)
        ·
          refine ⟨74207015117630714104126189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395770747294030475222006341 74207015117630714104126189)
          ·
            refine ⟨27827630669111517789047321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74207015117630714104126189 27827630669111517789047321)
            ·
              refine ⟨20870723001833638341785491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27827630669111517789047321 20870723001833638341785491)
              ·
                refine ⟨31306084502750457512678237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20870723001833638341785491 31306084502750457512678237)
                ·
                  refine ⟨11739781688531421567254339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31306084502750457512678237 11739781688531421567254339)
                  ·
                    refine ⟨17609672532797132350881509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11739781688531421567254339 17609672532797132350881509)
                    ·
                      refine ⟨3301813599899462315790283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17609672532797132350881509 3301813599899462315790283)
                      ·
                        rfl

theorem cell23_6430259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_6430259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430259 prefixEnd_6430259 := by exact prefixLift 6430259
  have htrace : WordTrace (prefixWord ++ tailWord_6430259) baseStart_6430259 baseEnd_6430259 := by
    simpa [prefixWord, tailWord_6430259, baseEnd_6430259] using wordTrace_append hprefix tailTrace_6430259
  have hstable : (prefixWord ++ tailWord_6430259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430259).length < 2 ^ (prefixWord ++ tailWord_6430259).sum := by decide
  have hdescent : baseEnd_6430259 < baseStart_6430259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430263 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 2, 3, 2]
def baseStart_6430263 : Nat := 118140960795 + 6430263 * 2 ^ 59
def prefixEnd_6430263 : Nat := 4983230072969 + 3 ^ 40 * 6430263 * 2
def baseEnd_6430263 : Nat := 3301815653822080300140265

theorem tailTrace_6430263 : CollatzResearch.WordTrace tailWord_6430263 prefixEnd_6430263 3301815653822080300140265 := by
  unfold tailWord_6430263
  simp only [CollatzResearch.WordTrace]
  refine ⟨234530959103262827333223443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156353972735508551555482295 234530959103262827333223443)
  ·
    refine ⟨351796438654894240999835165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234530959103262827333223443 351796438654894240999835165)
    ·
      refine ⟨131923664495585340374938187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351796438654894240999835165 131923664495585340374938187)
      ·
        refine ⟨197885496743378010562407281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131923664495585340374938187 197885496743378010562407281)
        ·
          refine ⟨148414122557533507921805461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197885496743378010562407281 148414122557533507921805461)
          ·
            refine ⟨6956911994884383183834631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 148414122557533507921805461 6956911994884383183834631)
            ·
              refine ⟨10435367992326574775751947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6956911994884383183834631 10435367992326574775751947)
              ·
                refine ⟨15653051988489862163627921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10435367992326574775751947 15653051988489862163627921)
                ·
                  refine ⟨11739788991367396622720941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15653051988489862163627921 11739788991367396622720941)
                  ·
                    refine ⟨4402420871762773733520353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11739788991367396622720941 4402420871762773733520353)
                    ·
                      refine ⟨3301815653822080300140265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402420871762773733520353 3301815653822080300140265)
                      ·
                        rfl

theorem cell23_6430263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 3, 2].length) (baseStart_6430263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430263 prefixEnd_6430263 := by exact prefixLift 6430263
  have htrace : WordTrace (prefixWord ++ tailWord_6430263) baseStart_6430263 baseEnd_6430263 := by
    simpa [prefixWord, tailWord_6430263, baseEnd_6430263] using wordTrace_append hprefix tailTrace_6430263
  have hstable : (prefixWord ++ tailWord_6430263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430263).length < 2 ^ (prefixWord ++ tailWord_6430263).sum := by decide
  have hdescent : baseEnd_6430263 < baseStart_6430263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430272 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_6430272 : Nat := 118140960795 + 6430272 * 2 ^ 59
def prefixEnd_6430272 : Nat := 4983230072969 + 3 ^ 40 * 6430272 * 2
def baseEnd_6430272 : Nat := 3301820275147970764927723

theorem tailTrace_6430272 : CollatzResearch.WordTrace tailWord_6430272 prefixEnd_6430272 3301820275147970764927723 := by
  unfold tailWord_6430272
  simp only [CollatzResearch.WordTrace]
  refine ⟨117265643680115110935150535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156354191573486814580200713 117265643680115110935150535)
  ·
    refine ⟨175898465520172666402725803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117265643680115110935150535 175898465520172666402725803)
    ·
      refine ⟨263847698280258999604088705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175898465520172666402725803 263847698280258999604088705)
      ·
        refine ⟨197885773710194249703066529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263847698280258999604088705 197885773710194249703066529)
        ·
          refine ⟨148414330282645687277299897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197885773710194249703066529 148414330282645687277299897)
          ·
            refine ⟨111310747711984265457974923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148414330282645687277299897 111310747711984265457974923)
            ·
              refine ⟨166966121567976398186962385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111310747711984265457974923 166966121567976398186962385)
              ·
                refine ⟨125224591175982298640221789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166966121567976398186962385 125224591175982298640221789)
                ·
                  refine ⟨46959221690993361990083171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125224591175982298640221789 46959221690993361990083171)
                  ·
                    refine ⟨70438832536490042985124757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46959221690993361990083171 70438832536490042985124757)
                    ·
                      refine ⟨3301820275147970764927723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70438832536490042985124757 3301820275147970764927723)
                      ·
                        rfl

theorem cell23_6430272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_6430272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430272 prefixEnd_6430272 := by exact prefixLift 6430272
  have htrace : WordTrace (prefixWord ++ tailWord_6430272) baseStart_6430272 baseEnd_6430272 := by
    simpa [prefixWord, tailWord_6430272, baseEnd_6430272] using wordTrace_append hprefix tailTrace_6430272
  have hstable : (prefixWord ++ tailWord_6430272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430272).length < 2 ^ (prefixWord ++ tailWord_6430272).sum := by decide
  have hdescent : baseEnd_6430272 < baseStart_6430272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430282 : List Nat := [3, 1, 2, 1, 1, 3, 12]
def baseStart_6430282 : Nat := 118140960795 + 6430282 * 2 ^ 59
def prefixEnd_6430282 : Nat := 4983230072969 + 3 ^ 40 * 6430282 * 2
def baseEnd_6430282 : Nat := 40763276666105132417317

theorem tailTrace_6430282 : CollatzResearch.WordTrace tailWord_6430282 prefixEnd_6430282 40763276666105132417317 := by
  unfold tailWord_6430282
  simp only [CollatzResearch.WordTrace]
  refine ⟨58632913022548498394541275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156354434726795995718776733 58632913022548498394541275)
  ·
    refine ⟨87949369533822747591811913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58632913022548498394541275 87949369533822747591811913)
    ·
      refine ⟨65962027150367060693858935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87949369533822747591811913 65962027150367060693858935)
      ·
        refine ⟨98943040725550591040788403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65962027150367060693858935 98943040725550591040788403)
        ·
          refine ⟨148414561088325886561182605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98943040725550591040788403 148414561088325886561182605)
          ·
            refine ⟨55655460408122207460443477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148414561088325886561182605 55655460408122207460443477)
            ·
              refine ⟨40763276666105132417317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 55655460408122207460443477 40763276666105132417317)
              ·
                rfl

theorem cell23_6430282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 12].length) (baseStart_6430282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430282 prefixEnd_6430282 := by exact prefixLift 6430282
  have htrace : WordTrace (prefixWord ++ tailWord_6430282) baseStart_6430282 baseEnd_6430282 := by
    simpa [prefixWord, tailWord_6430282, baseEnd_6430282] using wordTrace_append hprefix tailTrace_6430282
  have hstable : (prefixWord ++ tailWord_6430282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430282).length < 2 ^ (prefixWord ++ tailWord_6430282).sum := by decide
  have hdescent : baseEnd_6430282 < baseStart_6430282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430344 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6430344 : Nat := 118140960795 + 6430344 * 2 ^ 59
def prefixEnd_6430344 : Nat := 4983230072969 + 3 ^ 40 * 6430344 * 2
def baseEnd_6430344 : Nat := 3301857245755094483227393

theorem tailTrace_6430344 : CollatzResearch.WordTrace tailWord_6430344 prefixEnd_6430344 3301857245755094483227393 := by
  unfold tailWord_6430344
  simp only [CollatzResearch.WordTrace]
  refine ⟨117266956707984689083461043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156355942277312918777948057 117266956707984689083461043)
  ·
    refine ⟨175900435061977033625191565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117266956707984689083461043 175900435061977033625191565)
    ·
      refine ⟨65962663148241387609446837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175900435061977033625191565 65962663148241387609446837)
      ·
        refine ⟨6183999670147630088385641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65962663148241387609446837 6183999670147630088385641)
        ·
          refine ⟨4637999752610722566289231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6183999670147630088385641 4637999752610722566289231)
          ·
            refine ⟨6956999628916083849433847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4637999752610722566289231 6956999628916083849433847)
            ·
              refine ⟨10435499443374125774150771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6956999628916083849433847 10435499443374125774150771)
              ·
                refine ⟨15653249165061188661226157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10435499443374125774150771 15653249165061188661226157)
                ·
                  refine ⟨5869968436897945747959809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15653249165061188661226157 5869968436897945747959809)
                  ·
                    refine ⟨4402476327673459310969857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5869968436897945747959809 4402476327673459310969857)
                    ·
                      refine ⟨3301857245755094483227393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402476327673459310969857 3301857245755094483227393)
                      ·
                        rfl

theorem cell23_6430344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6430344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430344 prefixEnd_6430344 := by exact prefixLift 6430344
  have htrace : WordTrace (prefixWord ++ tailWord_6430344) baseStart_6430344 baseEnd_6430344 := by
    simpa [prefixWord, tailWord_6430344, baseEnd_6430344] using wordTrace_append hprefix tailTrace_6430344
  have hstable : (prefixWord ++ tailWord_6430344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430344).length < 2 ^ (prefixWord ++ tailWord_6430344).sum := by decide
  have hdescent : baseEnd_6430344 < baseStart_6430344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430360 : List Nat := [2, 1, 2, 4, 1, 2, 4, 1, 2, 1, 3]
def baseStart_6430360 : Nat := 118140960795 + 6430360 * 2 ^ 59
def prefixEnd_6430360 : Nat := 4983230072969 + 3 ^ 40 * 6430360 * 2
def baseEnd_6430360 : Nat := 3301865461445566420627319

theorem tailTrace_6430360 : CollatzResearch.WordTrace tailWord_6430360 prefixEnd_6430360 3301865461445566420627319 := by
  unfold tailWord_6430360
  simp only [CollatzResearch.WordTrace]
  refine ⟨117267248491955706449752267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156356331322607608599669689 117267248491955706449752267)
  ·
    refine ⟨175900872737933559674628401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117267248491955706449752267 175900872737933559674628401)
    ·
      refine ⟨131925654553450169755971301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175900872737933559674628401 131925654553450169755971301)
      ·
        refine ⟨24736060228771906829244619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131925654553450169755971301 24736060228771906829244619)
        ·
          refine ⟨37104090343157860243866929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24736060228771906829244619 37104090343157860243866929)
          ·
            refine ⟨27828067757368395182900197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37104090343157860243866929 27828067757368395182900197)
            ·
              refine ⟨5217762704506574096793787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27828067757368395182900197 5217762704506574096793787)
              ·
                refine ⟨7826644056759861145190681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5217762704506574096793787 7826644056759861145190681)
                ·
                  refine ⟨5869983042569895858893011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7826644056759861145190681 5869983042569895858893011)
                  ·
                    refine ⟨8804974563854843788339517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5869983042569895858893011 8804974563854843788339517)
                    ·
                      refine ⟨3301865461445566420627319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8804974563854843788339517 3301865461445566420627319)
                      ·
                        rfl

theorem cell23_6430360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_6430360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430360 prefixEnd_6430360 := by exact prefixLift 6430360
  have htrace : WordTrace (prefixWord ++ tailWord_6430360) baseStart_6430360 baseEnd_6430360 := by
    simpa [prefixWord, tailWord_6430360, baseEnd_6430360] using wordTrace_append hprefix tailTrace_6430360
  have hstable : (prefixWord ++ tailWord_6430360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430360).length < 2 ^ (prefixWord ++ tailWord_6430360).sum := by decide
  have hdescent : baseEnd_6430360 < baseStart_6430360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430400 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 2, 2, 2]
def baseStart_6430400 : Nat := 118140960795 + 6430400 * 2 ^ 59
def prefixEnd_6430400 : Nat := 4983230072969 + 3 ^ 40 * 6430400 * 2
def baseEnd_6430400 : Nat := 3301886000671746264127135

theorem tailTrace_6430400 : CollatzResearch.WordTrace tailWord_6430400 prefixEnd_6430400 3301886000671746264127135 := by
  unfold tailWord_6430400
  simp only [CollatzResearch.WordTrace]
  refine ⟨117267977951883249865480327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156357303935844333153973769 117267977951883249865480327)
  ·
    refine ⟨175901966927824874798220491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117267977951883249865480327 175901966927824874798220491)
    ·
      refine ⟨263852950391737312197330737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175901966927824874798220491 263852950391737312197330737)
      ·
        refine ⟨197889712793802984147998053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263852950391737312197330737 197889712793802984147998053)
        ·
          refine ⟨37104321148838059527749635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197889712793802984147998053 37104321148838059527749635)
          ·
            refine ⟨55656481723257089291624453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37104321148838059527749635 55656481723257089291624453)
            ·
              refine ⟨10435590323110704242179585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55656481723257089291624453 10435590323110704242179585)
              ·
                refine ⟨7826692742333028181634689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10435590323110704242179585 7826692742333028181634689)
                ·
                  refine ⟨5870019556749771136226017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7826692742333028181634689 5870019556749771136226017)
                  ·
                    refine ⟨4402514667562328352169513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5870019556749771136226017 4402514667562328352169513)
                    ·
                      refine ⟨3301886000671746264127135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402514667562328352169513 3301886000671746264127135)
                      ·
                        rfl

theorem cell23_6430400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 2, 2, 2].length) (baseStart_6430400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430400 prefixEnd_6430400 := by exact prefixLift 6430400
  have htrace : WordTrace (prefixWord ++ tailWord_6430400) baseStart_6430400 baseEnd_6430400 := by
    simpa [prefixWord, tailWord_6430400, baseEnd_6430400] using wordTrace_append hprefix tailTrace_6430400
  have hstable : (prefixWord ++ tailWord_6430400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430400).length < 2 ^ (prefixWord ++ tailWord_6430400).sum := by decide
  have hdescent : baseEnd_6430400 < baseStart_6430400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430413 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_6430413 : Nat := 118140960795 + 6430413 * 2 ^ 59
def prefixEnd_6430413 : Nat := 4983230072969 + 3 ^ 40 * 6430413 * 2
def baseEnd_6430413 : Nat := 3301892675920254713264575

theorem tailTrace_6430413 : CollatzResearch.WordTrace tailWord_6430413 prefixEnd_6430413 3301892675920254713264575 := by
  unfold tailWord_6430413
  simp only [CollatzResearch.WordTrace]
  refine ⟨234536430052719402951183893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156357620035146268634122595 234536430052719402951183893)
  ·
    refine ⟨10993895158721222013336745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 234536430052719402951183893 10993895158721222013336745)
    ·
      refine ⟨8245421369040916510002559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10993895158721222013336745 8245421369040916510002559)
      ·
        refine ⟨12368132053561374765003839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8245421369040916510002559 12368132053561374765003839)
        ·
          refine ⟨18552198080342062147505759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12368132053561374765003839 18552198080342062147505759)
          ·
            refine ⟨27828297120513093221258639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18552198080342062147505759 27828297120513093221258639)
            ·
              refine ⟨41742445680769639831887959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27828297120513093221258639 41742445680769639831887959)
              ·
                refine ⟨62613668521154459747831939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41742445680769639831887959 62613668521154459747831939)
                ·
                  refine ⟨93920502781731689621747909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62613668521154459747831939 93920502781731689621747909)
                  ·
                    refine ⟨17610094271574691804077733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93920502781731689621747909 17610094271574691804077733)
                    ·
                      refine ⟨3301892675920254713264575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17610094271574691804077733 3301892675920254713264575)
                      ·
                        rfl

theorem cell23_6430413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_6430413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430413 prefixEnd_6430413 := by exact prefixLift 6430413
  have htrace : WordTrace (prefixWord ++ tailWord_6430413) baseStart_6430413 baseEnd_6430413 := by
    simpa [prefixWord, tailWord_6430413, baseEnd_6430413] using wordTrace_append hprefix tailTrace_6430413
  have hstable : (prefixWord ++ tailWord_6430413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430413).length < 2 ^ (prefixWord ++ tailWord_6430413).sum := by decide
  have hdescent : baseEnd_6430413 < baseStart_6430413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430476 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 1, 4, 3]
def baseStart_6430476 : Nat := 118140960795 + 6430476 * 2 ^ 59
def prefixEnd_6430476 : Nat := 4983230072969 + 3 ^ 40 * 6430476 * 2
def baseEnd_6430476 : Nat := 3301925025201487966776785

theorem tailTrace_6430476 : CollatzResearch.WordTrace tailWord_6430476 prefixEnd_6430476 3301925025201487966776785 := by
  unfold tailWord_6430476
  simp only [CollatzResearch.WordTrace]
  refine ⟨117269363925745582355363641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156359151900994109807151521 117269363925745582355363641)
  ·
    refine ⟨87952022944309186766522731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117269363925745582355363641 87952022944309186766522731)
    ·
      refine ⟨131928034416463780149784097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87952022944309186766522731 131928034416463780149784097)
      ·
        refine ⟨98946025812347835112338073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131928034416463780149784097 98946025812347835112338073)
        ·
          refine ⟨74209519359260876334253555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98946025812347835112338073 74209519359260876334253555)
          ·
            refine ⟨111314279038891314501380333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74209519359260876334253555 111314279038891314501380333)
            ·
              refine ⟨41742854639584242938017625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111314279038891314501380333 41742854639584242938017625)
              ·
                refine ⟨31307140979688182203513219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41742854639584242938017625 31307140979688182203513219)
                ·
                  refine ⟨46960711469532273305269829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31307140979688182203513219 46960711469532273305269829)
                  ·
                    refine ⟨8805133400537301244738093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46960711469532273305269829 8805133400537301244738093)
                    ·
                      refine ⟨3301925025201487966776785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8805133400537301244738093 3301925025201487966776785)
                      ·
                        rfl

theorem cell23_6430476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_6430476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430476 prefixEnd_6430476 := by exact prefixLift 6430476
  have htrace : WordTrace (prefixWord ++ tailWord_6430476) baseStart_6430476 baseEnd_6430476 := by
    simpa [prefixWord, tailWord_6430476, baseEnd_6430476] using wordTrace_append hprefix tailTrace_6430476
  have hstable : (prefixWord ++ tailWord_6430476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430476).length < 2 ^ (prefixWord ++ tailWord_6430476).sum := by decide
  have hdescent : baseEnd_6430476 < baseStart_6430476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430517 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 3, 4]
def baseStart_6430517 : Nat := 118140960795 + 6430517 * 2 ^ 59
def prefixEnd_6430517 : Nat := 4983230072969 + 3 ^ 40 * 6430517 * 2
def baseEnd_6430517 : Nat := 1100648692636107435454699

theorem tailTrace_6430517 : CollatzResearch.WordTrace tailWord_6430517 prefixEnd_6430517 1100648692636107435454699 := by
  unfold tailWord_6430517
  simp only [CollatzResearch.WordTrace]
  refine ⟨234540223244342628712969805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156360148829561752475313203 234540223244342628712969805)
  ·
    refine ⟨87952583716628485767363677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234540223244342628712969805 87952583716628485767363677)
    ·
      refine ⟨32982218893735682162761379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87952583716628485767363677 32982218893735682162761379)
      ·
        refine ⟨49473328340603523244142069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32982218893735682162761379 49473328340603523244142069)
        ·
          refine ⟨4638124531931580304138319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49473328340603523244142069 4638124531931580304138319)
          ·
            refine ⟨6957186797897370456207479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638124531931580304138319 6957186797897370456207479)
            ·
              refine ⟨10435780196846055684311219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6957186797897370456207479 10435780196846055684311219)
              ·
                refine ⟨15653670295269083526466829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10435780196846055684311219 15653670295269083526466829)
                ·
                  refine ⟨5870126360725906322425061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15653670295269083526466829 5870126360725906322425061)
                  ·
                    refine ⟨1100648692636107435454699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5870126360725906322425061 1100648692636107435454699)
                    ·
                      rfl

theorem cell23_6430517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_6430517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430517 prefixEnd_6430517 := by exact prefixLift 6430517
  have htrace : WordTrace (prefixWord ++ tailWord_6430517) baseStart_6430517 baseEnd_6430517 := by
    simpa [prefixWord, tailWord_6430517, baseEnd_6430517] using wordTrace_append hprefix tailTrace_6430517
  have hstable : (prefixWord ++ tailWord_6430517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430517).length < 2 ^ (prefixWord ++ tailWord_6430517).sum := by decide
  have hdescent : baseEnd_6430517 < baseStart_6430517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430533 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 4, 3, 2]
def baseStart_6430533 : Nat := 118140960795 + 6430533 * 2 ^ 59
def prefixEnd_6430533 : Nat := 4983230072969 + 3 ^ 40 * 6430533 * 2
def baseEnd_6430533 : Nat := 3301954293598794243764023

theorem tailTrace_6430533 : CollatzResearch.WordTrace tailWord_6430533 prefixEnd_6430533 3301954293598794243764023 := by
  unfold tailWord_6430533
  simp only [CollatzResearch.WordTrace]
  refine ⟨234540806812284663445552253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156360537874856442297034835 234540806812284663445552253)
  ·
    refine ⟨87952802554606748792082095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234540806812284663445552253 87952802554606748792082095)
    ·
      refine ⟨131929203831910123188123143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87952802554606748792082095 131929203831910123188123143)
      ·
        refine ⟨197893805747865184782184715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131929203831910123188123143 197893805747865184782184715)
        ·
          refine ⟨296840708621797777173277073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197893805747865184782184715 296840708621797777173277073)
          ·
            refine ⟨222630531466348332879957805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296840708621797777173277073 222630531466348332879957805)
            ·
              refine ⟨83486449299880624829984177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222630531466348332879957805 83486449299880624829984177)
              ·
                refine ⟨62614836974910468622488133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83486449299880624829984177 62614836974910468622488133)
                ·
                  refine ⟨11740281932795712866716525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62614836974910468622488133 11740281932795712866716525)
                  ·
                    refine ⟨4402605724798392325018697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11740281932795712866716525 4402605724798392325018697)
                    ·
                      refine ⟨3301954293598794243764023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402605724798392325018697 3301954293598794243764023)
                      ·
                        rfl

theorem cell23_6430533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 4, 3, 2].length) (baseStart_6430533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430533 prefixEnd_6430533 := by exact prefixLift 6430533
  have htrace : WordTrace (prefixWord ++ tailWord_6430533) baseStart_6430533 baseEnd_6430533 := by
    simpa [prefixWord, tailWord_6430533, baseEnd_6430533] using wordTrace_append hprefix tailTrace_6430533
  have hstable : (prefixWord ++ tailWord_6430533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430533).length < 2 ^ (prefixWord ++ tailWord_6430533).sum := by decide
  have hdescent : baseEnd_6430533 < baseStart_6430533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430560 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 1, 5]
def baseStart_6430560 : Nat := 118140960795 + 6430560 * 2 ^ 59
def prefixEnd_6430560 : Nat := 4983230072969 + 3 ^ 40 * 6430560 * 2
def baseEnd_6430560 : Nat := 1100656052525488546042133

theorem tailTrace_6430560 : CollatzResearch.WordTrace tailWord_6430560 prefixEnd_6430560 1100656052525488546042133 := by
  unfold tailWord_6430560
  simp only [CollatzResearch.WordTrace]
  refine ⟨117270895791593423528392567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156361194388791231371190089 117270895791593423528392567)
  ·
    refine ⟨175906343687390135292588851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117270895791593423528392567 175906343687390135292588851)
    ·
      refine ⟨263859515531085202938883277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175906343687390135292588851 263859515531085202938883277)
      ·
        refine ⟨98947318324156951102081229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263859515531085202938883277 98947318324156951102081229)
        ·
          refine ⟨37105244371558856663280461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98947318324156951102081229 37105244371558856663280461)
          ·
            refine ⟨13914466639334571248730173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37105244371558856663280461 13914466639334571248730173)
            ·
              refine ⟨5217924989750464218273815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13914466639334571248730173 5217924989750464218273815)
              ·
                refine ⟨7826887484625696327410723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5217924989750464218273815 7826887484625696327410723)
                ·
                  refine ⟨11740331226938544491116085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7826887484625696327410723 11740331226938544491116085)
                  ·
                    refine ⟨1100656052525488546042133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11740331226938544491116085 1100656052525488546042133)
                    ·
                      rfl

theorem cell23_6430560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 1, 5].length) (baseStart_6430560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430560 prefixEnd_6430560 := by exact prefixLift 6430560
  have htrace : WordTrace (prefixWord ++ tailWord_6430560) baseStart_6430560 baseEnd_6430560 := by
    simpa [prefixWord, tailWord_6430560, baseEnd_6430560] using wordTrace_append hprefix tailTrace_6430560
  have hstable : (prefixWord ++ tailWord_6430560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430560).length < 2 ^ (prefixWord ++ tailWord_6430560).sum := by decide
  have hdescent : baseEnd_6430560 < baseStart_6430560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430573 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_6430573 : Nat := 118140960795 + 6430573 * 2 ^ 59
def prefixEnd_6430573 : Nat := 4983230072969 + 3 ^ 40 * 6430573 * 2
def baseEnd_6430573 : Nat := 1100658277608324695754613

theorem tailTrace_6430573 : CollatzResearch.WordTrace tailWord_6430573 prefixEnd_6430573 1100658277608324695754613 := by
  unfold tailWord_6430573
  simp only [CollatzResearch.WordTrace]
  refine ⟨234542265732139750277008373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156361510488093166851338915 234542265732139750277008373)
  ·
    refine ⟨21988337412388101588469535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234542265732139750277008373 21988337412388101588469535)
    ·
      refine ⟨32982506118582152382704303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21988337412388101588469535 32982506118582152382704303)
      ·
        refine ⟨49473759177873228574056455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32982506118582152382704303 49473759177873228574056455)
        ·
          refine ⟨74210638766809842861084683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49473759177873228574056455 74210638766809842861084683)
          ·
            refine ⟨111315958150214764291627025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74210638766809842861084683 111315958150214764291627025)
            ·
              refine ⟨83486968612661073218720269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111315958150214764291627025 83486968612661073218720269)
              ·
                refine ⟨31307613229747902457020101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83486968612661073218720269 31307613229747902457020101)
                ·
                  refine ⟨5870177480577731710691269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31307613229747902457020101 5870177480577731710691269)
                  ·
                    refine ⟨1100658277608324695754613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5870177480577731710691269 1100658277608324695754613)
                    ·
                      rfl

theorem cell23_6430573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_6430573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430573 prefixEnd_6430573 := by exact prefixLift 6430573
  have htrace : WordTrace (prefixWord ++ tailWord_6430573) baseStart_6430573 baseEnd_6430573 := by
    simpa [prefixWord, tailWord_6430573, baseEnd_6430573] using wordTrace_append hprefix tailTrace_6430573
  have hstable : (prefixWord ++ tailWord_6430573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430573).length < 2 ^ (prefixWord ++ tailWord_6430573).sum := by decide
  have hdescent : baseEnd_6430573 < baseStart_6430573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430574 : List Nat := [4, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_6430574 : Nat := 118140960795 + 6430574 * 2 ^ 59
def prefixEnd_6430574 : Nat := 4983230072969 + 3 ^ 40 * 6430574 * 2
def baseEnd_6430574 : Nat := 3301975346305628583351335

theorem tailTrace_6430574 : CollatzResearch.WordTrace tailWord_6430574 prefixEnd_6430574 3301975346305628583351335 := by
  unfold tailWord_6430574
  simp only [CollatzResearch.WordTrace]
  refine ⟨29317787775642015930974347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156361534803424084965196517 29317787775642015930974347)
  ·
    refine ⟨43976681663463023896461521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29317787775642015930974347 43976681663463023896461521)
    ·
      refine ⟨32982511247597267922346141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43976681663463023896461521 32982511247597267922346141)
      ·
        refine ⟨12368441717848975470879803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32982511247597267922346141 12368441717848975470879803)
        ·
          refine ⟨18552662576773463206319705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12368441717848975470879803 18552662576773463206319705)
          ·
            refine ⟨13914496932580097404739779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18552662576773463206319705 13914496932580097404739779)
            ·
              refine ⟨20871745398870146107109669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13914496932580097404739779 20871745398870146107109669)
              ·
                refine ⟨3913452262288152395083063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20871745398870146107109669 3913452262288152395083063)
                ·
                  refine ⟨5870178393432228592624595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3913452262288152395083063 5870178393432228592624595)
                  ·
                    refine ⟨8805267590148342888936893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5870178393432228592624595 8805267590148342888936893)
                    ·
                      refine ⟨3301975346305628583351335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8805267590148342888936893 3301975346305628583351335)
                      ·
                        rfl

theorem cell23_6430574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_6430574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430574 prefixEnd_6430574 := by exact prefixLift 6430574
  have htrace : WordTrace (prefixWord ++ tailWord_6430574) baseStart_6430574 baseEnd_6430574 := by
    simpa [prefixWord, tailWord_6430574, baseEnd_6430574] using wordTrace_append hprefix tailTrace_6430574
  have hstable : (prefixWord ++ tailWord_6430574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430574).length < 2 ^ (prefixWord ++ tailWord_6430574).sum := by decide
  have hdescent : baseEnd_6430574 < baseStart_6430574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430576 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 4]
def baseStart_6430576 : Nat := 118140960795 + 6430576 * 2 ^ 59
def prefixEnd_6430576 : Nat := 4983230072969 + 3 ^ 40 * 6430576 * 2
def baseEnd_6430576 : Nat := 3301976373266937575526325

theorem tailTrace_6430576 : CollatzResearch.WordTrace tailWord_6430576 prefixEnd_6430576 3301976373266937575526325 := by
  unfold tailWord_6430576
  simp only [CollatzResearch.WordTrace]
  refine ⟨117271187575564440894683791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156361583434085921192911721 117271187575564440894683791)
  ·
    refine ⟨175906781363346661342025687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117271187575564440894683791 175906781363346661342025687)
    ·
      refine ⟨263860172045019992013038531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175906781363346661342025687 263860172045019992013038531)
      ·
        refine ⟨395790258067529988019557797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263860172045019992013038531 395790258067529988019557797)
        ·
          refine ⟨74210673387661872753667087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395790258067529988019557797 74210673387661872753667087)
          ·
            refine ⟨111316010081492809130500631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74210673387661872753667087 111316010081492809130500631)
            ·
              refine ⟨166974015122239213695750947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111316010081492809130500631 166974015122239213695750947)
              ·
                refine ⟨250461022683358820543626421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166974015122239213695750947 250461022683358820543626421)
                ·
                  refine ⟨23480720876564889425964977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250461022683358820543626421 23480720876564889425964977)
                  ·
                    refine ⟨17610540657423667069473733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23480720876564889425964977 17610540657423667069473733)
                    ·
                      refine ⟨3301976373266937575526325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17610540657423667069473733 3301976373266937575526325)
                      ·
                        rfl

theorem cell23_6430576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_6430576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430576 prefixEnd_6430576 := by exact prefixLift 6430576
  have htrace : WordTrace (prefixWord ++ tailWord_6430576) baseStart_6430576 baseEnd_6430576 := by
    simpa [prefixWord, tailWord_6430576, baseEnd_6430576] using wordTrace_append hprefix tailTrace_6430576
  have hstable : (prefixWord ++ tailWord_6430576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430576).length < 2 ^ (prefixWord ++ tailWord_6430576).sum := by decide
  have hdescent : baseEnd_6430576 < baseStart_6430576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430586 : List Nat := [3, 1, 1, 1, 1, 1, 7, 8]
def baseStart_6430586 : Nat := 118140960795 + 6430586 * 2 ^ 59
def prefixEnd_6430586 : Nat := 4983230072969 + 3 ^ 40 * 6430586 * 2
def baseEnd_6430586 : Nat := 122295611410128982829677

theorem tailTrace_6430586 : CollatzResearch.WordTrace tailWord_6430586 prefixEnd_6430586 122295611410128982829677 := by
  unfold tailWord_6430586
  simp only [CollatzResearch.WordTrace]
  refine ⟨58635684970273163374307903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156361826587395102331487741 58635684970273163374307903)
  ·
    refine ⟨87953527455409745061461855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58635684970273163374307903 87953527455409745061461855)
    ·
      refine ⟨131930291183114617592192783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87953527455409745061461855 131930291183114617592192783)
      ·
        refine ⟨197895436774671926388289175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131930291183114617592192783 197895436774671926388289175)
        ·
          refine ⟨296843155162007889582433763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197895436774671926388289175 296843155162007889582433763)
          ·
            refine ⟨445264732743011834373650645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296843155162007889582433763 445264732743011834373650645)
            ·
              refine ⟨10435892173664339868132437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 445264732743011834373650645 10435892173664339868132437)
              ·
                refine ⟨122295611410128982829677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10435892173664339868132437 122295611410128982829677)
                ·
                  rfl

theorem cell23_6430586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 8].length) (baseStart_6430586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430586 prefixEnd_6430586 := by exact prefixLift 6430586
  have htrace : WordTrace (prefixWord ++ tailWord_6430586) baseStart_6430586 baseEnd_6430586 := by
    simpa [prefixWord, tailWord_6430586, baseEnd_6430586] using wordTrace_append hprefix tailTrace_6430586
  have hstable : (prefixWord ++ tailWord_6430586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430586).length < 2 ^ (prefixWord ++ tailWord_6430586).sum := by decide
  have hdescent : baseEnd_6430586 < baseStart_6430586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430590 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_6430590 : Nat := 118140960795 + 6430590 * 2 ^ 59
def prefixEnd_6430590 : Nat := 4983230072969 + 3 ^ 40 * 6430590 * 2
def baseEnd_6430590 : Nat := 1100661187332033506917087

theorem tailTrace_6430590 : CollatzResearch.WordTrace tailWord_6430590 prefixEnd_6430590 1100661187332033506917087 := by
  unfold tailWord_6430590
  simp only [CollatzResearch.WordTrace]
  refine ⟨29317860721634770272547153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156361923848718774786918149 29317860721634770272547153)
  ·
    refine ⟨21988395541226077704410365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29317860721634770272547153 21988395541226077704410365)
    ·
      refine ⟨8245648327959779139153887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21988395541226077704410365 8245648327959779139153887)
      ·
        refine ⟨12368472491939668708730831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8245648327959779139153887 12368472491939668708730831)
        ·
          refine ⟨18552708737909503063096247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12368472491939668708730831 18552708737909503063096247)
          ·
            refine ⟨27829063106864254594644371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18552708737909503063096247 27829063106864254594644371)
            ·
              refine ⟨41743594660296381891966557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27829063106864254594644371 41743594660296381891966557)
              ·
                refine ⟨15653847997611143209487459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41743594660296381891966557 15653847997611143209487459)
                ·
                  refine ⟨23480771996416714814231189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15653847997611143209487459 23480771996416714814231189)
                  ·
                    refine ⟨1100661187332033506917087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23480771996416714814231189 1100661187332033506917087)
                    ·
                      rfl

theorem cell23_6430590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_6430590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430590 prefixEnd_6430590 := by exact prefixLift 6430590
  have htrace : WordTrace (prefixWord ++ tailWord_6430590) baseStart_6430590 baseEnd_6430590 := by
    simpa [prefixWord, tailWord_6430590, baseEnd_6430590] using wordTrace_append hprefix tailTrace_6430590
  have hstable : (prefixWord ++ tailWord_6430590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430590).length < 2 ^ (prefixWord ++ tailWord_6430590).sum := by decide
  have hdescent : baseEnd_6430590 < baseStart_6430590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430610 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_6430610 : Nat := 118140960795 + 6430610 * 2 ^ 59
def prefixEnd_6430610 : Nat := 4983230072969 + 3 ^ 40 * 6430610 * 2
def baseEnd_6430610 : Nat := 3301993831609190442501169

theorem tailTrace_6430610 : CollatzResearch.WordTrace tailWord_6430610 prefixEnd_6430610 3301993831609190442501169 := by
  unfold tailWord_6430610
  simp only [CollatzResearch.WordTrace]
  refine ⟨58635903808251426399026321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156362410155337137064070189 58635903808251426399026321)
  ·
    refine ⟨43976927856188569799269741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58635903808251426399026321 43976927856188569799269741)
    ·
      refine ⟨16491347946070713674726153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43976927856188569799269741 16491347946070713674726153)
      ·
        refine ⟨12368510959553035256044615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16491347946070713674726153 12368510959553035256044615)
        ·
          refine ⟨18552766439329552884066923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12368510959553035256044615 18552766439329552884066923)
          ·
            refine ⟨27829149658994329326100385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18552766439329552884066923 27829149658994329326100385)
            ·
              refine ⟨20871862244245746994575289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27829149658994329326100385 20871862244245746994575289)
              ·
                refine ⟨15653896683184310245931467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20871862244245746994575289 15653896683184310245931467)
                ·
                  refine ⟨23480845024776465368897201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15653896683184310245931467 23480845024776465368897201)
                  ·
                    refine ⟨17610633768582349026672901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23480845024776465368897201 17610633768582349026672901)
                    ·
                      refine ⟨3301993831609190442501169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17610633768582349026672901 3301993831609190442501169)
                      ·
                        rfl

theorem cell23_6430610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_6430610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430610 prefixEnd_6430610 := by exact prefixLift 6430610
  have htrace : WordTrace (prefixWord ++ tailWord_6430610) baseStart_6430610 baseEnd_6430610 := by
    simpa [prefixWord, tailWord_6430610, baseEnd_6430610] using wordTrace_append hprefix tailTrace_6430610
  have hstable : (prefixWord ++ tailWord_6430610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430610).length < 2 ^ (prefixWord ++ tailWord_6430610).sum := by decide
  have hdescent : baseEnd_6430610 < baseStart_6430610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430613 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_6430613 : Nat := 118140960795 + 6430613 * 2 ^ 59
def prefixEnd_6430613 : Nat := 4983230072969 + 3 ^ 40 * 6430613 * 2
def baseEnd_6430613 : Nat := 3301995372051153930763655

theorem tailTrace_6430613 : CollatzResearch.WordTrace tailWord_6430613 prefixEnd_6430613 3301995372051153930763655 := by
  unfold tailWord_6430613
  simp only [CollatzResearch.WordTrace]
  refine ⟨234543724651994837108464493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156362483101329891405642995 234543724651994837108464493)
  ·
    refine ⟨87953896744498063915674185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234543724651994837108464493 87953896744498063915674185)
    ·
      refine ⟨65965422558373547936755639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87953896744498063915674185 65965422558373547936755639)
      ·
        refine ⟨98948133837560321905133459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65965422558373547936755639 98948133837560321905133459)
        ·
          refine ⟨148422200756340482857700189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98948133837560321905133459 148422200756340482857700189)
          ·
            refine ⟨55658325283627681071637571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148422200756340482857700189 55658325283627681071637571)
            ·
              refine ⟨83487487925441521607456357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55658325283627681071637571 83487487925441521607456357)
              ·
                refine ⟨15653903986020285301398067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83487487925441521607456357 15653903986020285301398067)
                ·
                  refine ⟨23480855979030427952097101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15653903986020285301398067 23480855979030427952097101)
                  ·
                    refine ⟨8805320992136410482036413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23480855979030427952097101 8805320992136410482036413)
                    ·
                      refine ⟨3301995372051153930763655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8805320992136410482036413 3301995372051153930763655)
                      ·
                        rfl

theorem cell23_6430613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_6430613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430613 prefixEnd_6430613 := by exact prefixLift 6430613
  have htrace : WordTrace (prefixWord ++ tailWord_6430613) baseStart_6430613 baseEnd_6430613 := by
    simpa [prefixWord, tailWord_6430613, baseEnd_6430613] using wordTrace_append hprefix tailTrace_6430613
  have hstable : (prefixWord ++ tailWord_6430613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430613).length < 2 ^ (prefixWord ++ tailWord_6430613).sum := by decide
  have hdescent : baseEnd_6430613 < baseStart_6430613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430644 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_6430644 : Nat := 118140960795 + 6430644 * 2 ^ 59
def prefixEnd_6430644 : Nat := 4983230072969 + 3 ^ 40 * 6430644 * 2
def baseEnd_6430644 : Nat := 3302011289951443309476013

theorem tailTrace_6430644 : CollatzResearch.WordTrace tailWord_6430644 prefixEnd_6430644 3302011289951443309476013 := by
  unfold tailWord_6430644
  simp only [CollatzResearch.WordTrace]
  refine ⟨117272427657441264701421493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156363236876588352935228657 117272427657441264701421493)
  ·
    refine ⟨10994290092885118565758265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117272427657441264701421493 10994290092885118565758265)
    ·
      refine ⟨8245717569663838924318699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10994290092885118565758265 8245717569663838924318699)
      ·
        refine ⟨12368576354495758386478049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8245717569663838924318699 12368576354495758386478049)
        ·
          refine ⟨9276432265871818789858537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12368576354495758386478049 9276432265871818789858537)
          ·
            refine ⟨6957324199403864092393903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9276432265871818789858537 6957324199403864092393903)
            ·
              refine ⟨10435986299105796138590855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6957324199403864092393903 10435986299105796138590855)
              ·
                refine ⟨15653979448658694207886283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10435986299105796138590855 15653979448658694207886283)
                ·
                  refine ⟨23480969172988041311829425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15653979448658694207886283 23480969172988041311829425)
                  ·
                    refine ⟨17610726879741030983872069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23480969172988041311829425 17610726879741030983872069)
                    ·
                      refine ⟨3302011289951443309476013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17610726879741030983872069 3302011289951443309476013)
                      ·
                        rfl

theorem cell23_6430644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_6430644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430644 prefixEnd_6430644 := by exact prefixLift 6430644
  have htrace : WordTrace (prefixWord ++ tailWord_6430644) baseStart_6430644 baseEnd_6430644 := by
    simpa [prefixWord, tailWord_6430644, baseEnd_6430644] using wordTrace_append hprefix tailTrace_6430644
  have hstable : (prefixWord ++ tailWord_6430644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430644).length < 2 ^ (prefixWord ++ tailWord_6430644).sum := by decide
  have hdescent : baseEnd_6430644 < baseStart_6430644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430670 : List Nat := [4, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2]
def baseStart_6430670 : Nat := 118140960795 + 6430670 * 2 ^ 59
def prefixEnd_6430670 : Nat := 4983230072969 + 3 ^ 40 * 6430670 * 2
def baseEnd_6430670 : Nat := 3302024640448460207750893

theorem tailTrace_6430670 : CollatzResearch.WordTrace tailWord_6430670 prefixEnd_6430670 3302024640448460207750893 := by
  unfold tailWord_6430670
  simp only [CollatzResearch.WordTrace]
  refine ⟨29318225451598541980411183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156363869075192223895526309 29318225451598541980411183)
  ·
    refine ⟨43977338177397812970616775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29318225451598541980411183 43977338177397812970616775)
    ·
      refine ⟨65966007266096719455925163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43977338177397812970616775 65966007266096719455925163)
      ·
        refine ⟨98949010899145079183887745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65966007266096719455925163 98949010899145079183887745)
        ·
          refine ⟨74211758174358809387915809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98949010899145079183887745 74211758174358809387915809)
          ·
            refine ⟨55658818630769107040936857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74211758174358809387915809 55658818630769107040936857)
            ·
              refine ⟨41744113973076830280702643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55658818630769107040936857 41744113973076830280702643)
              ·
                refine ⟨62616170959615245421053965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41744113973076830280702643 62616170959615245421053965)
                ·
                  refine ⟨23481064109855717032895237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62616170959615245421053965 23481064109855717032895237)
                  ·
                    refine ⟨4402699520597946943667857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23481064109855717032895237 4402699520597946943667857)
                    ·
                      refine ⟨3302024640448460207750893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402699520597946943667857 3302024640448460207750893)
                      ·
                        rfl

theorem cell23_6430670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_6430670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430670 prefixEnd_6430670 := by exact prefixLift 6430670
  have htrace : WordTrace (prefixWord ++ tailWord_6430670) baseStart_6430670 baseEnd_6430670 := by
    simpa [prefixWord, tailWord_6430670, baseEnd_6430670] using wordTrace_append hprefix tailTrace_6430670
  have hstable : (prefixWord ++ tailWord_6430670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430670).length < 2 ^ (prefixWord ++ tailWord_6430670).sum := by decide
  have hdescent : baseEnd_6430670 < baseStart_6430670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430687 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 4, 2, 2]
def baseStart_6430687 : Nat := 118140960795 + 6430687 * 2 ^ 59
def prefixEnd_6430687 : Nat := 4983230072969 + 3 ^ 40 * 6430687 * 2
def baseEnd_6430687 : Nat := 3302033369619586641238315

theorem tailTrace_6430687 : CollatzResearch.WordTrace tailWord_6430687 prefixEnd_6430687 3302033369619586641238315 := by
  unfold tailWord_6430687
  simp only [CollatzResearch.WordTrace]
  refine ⟨234546423653726747746658315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156364282435817831831105543 234546423653726747746658315)
  ·
    refine ⟨351819635480590121619987473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234546423653726747746658315 351819635480590121619987473)
    ·
      refine ⟨263864726610442591214990605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351819635480590121619987473 263864726610442591214990605)
      ·
        refine ⟨98949272478915971705621477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263864726610442591214990605 98949272478915971705621477)
        ·
          refine ⟨18552988589796744694804027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98949272478915971705621477 18552988589796744694804027)
          ·
            refine ⟨27829482884695117042206041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18552988589796744694804027 27829482884695117042206041)
            ·
              refine ⟨20872112163521337781654531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27829482884695117042206041 20872112163521337781654531)
              ·
                refine ⟨31308168245282006672481797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20872112163521337781654531 31308168245282006672481797)
                ·
                  refine ⟨5870281545990376251090337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31308168245282006672481797 5870281545990376251090337)
                  ·
                    refine ⟨4402711159492782188317753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5870281545990376251090337 4402711159492782188317753)
                    ·
                      refine ⟨3302033369619586641238315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402711159492782188317753 3302033369619586641238315)
                      ·
                        rfl

theorem cell23_6430687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_6430687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430687 prefixEnd_6430687 := by exact prefixLift 6430687
  have htrace : WordTrace (prefixWord ++ tailWord_6430687) baseStart_6430687 baseEnd_6430687 := by
    simpa [prefixWord, tailWord_6430687, baseEnd_6430687] using wordTrace_append hprefix tailTrace_6430687
  have hstable : (prefixWord ++ tailWord_6430687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430687).length < 2 ^ (prefixWord ++ tailWord_6430687).sum := by decide
  have hdescent : baseEnd_6430687 < baseStart_6430687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430703 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 3]
def baseStart_6430703 : Nat := 118140960795 + 6430703 * 2 ^ 59
def prefixEnd_6430703 : Nat := 4983230072969 + 3 ^ 40 * 6430703 * 2
def baseEnd_6430703 : Nat := 3302041585310058578638241

theorem tailTrace_6430703 : CollatzResearch.WordTrace tailWord_6430703 prefixEnd_6430703 3302041585310058578638241 := by
  unfold tailWord_6430703
  simp only [CollatzResearch.WordTrace]
  refine ⟨234547007221668782479240763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156364671481112521652827175 234547007221668782479240763)
  ·
    refine ⟨351820510832503173718861145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234547007221668782479240763 351820510832503173718861145)
    ·
      refine ⟨263865383124377380289145859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351820510832503173718861145 263865383124377380289145859)
      ·
        refine ⟨395798074686566070433718789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263865383124377380289145859 395798074686566070433718789)
        ·
          refine ⟨74212139003731138206322273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395798074686566070433718789 74212139003731138206322273)
          ·
            refine ⟨55659104252798353654741705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74212139003731138206322273 55659104252798353654741705)
            ·
              refine ⟨41744328189598765241056279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55659104252798353654741705 41744328189598765241056279)
              ·
                refine ⟨62616492284398147861584419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41744328189598765241056279 62616492284398147861584419)
                ·
                  refine ⟨93924738426597221792376629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62616492284398147861584419 93924738426597221792376629)
                  ·
                    refine ⟨8805444227493489543035309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93924738426597221792376629 8805444227493489543035309)
                    ·
                      refine ⟨3302041585310058578638241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8805444227493489543035309 3302041585310058578638241)
                      ·
                        rfl

theorem cell23_6430703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 3].length) (baseStart_6430703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430703 prefixEnd_6430703 := by exact prefixLift 6430703
  have htrace : WordTrace (prefixWord ++ tailWord_6430703) baseStart_6430703 baseEnd_6430703 := by
    simpa [prefixWord, tailWord_6430703, baseEnd_6430703] using wordTrace_append hprefix tailTrace_6430703
  have hstable : (prefixWord ++ tailWord_6430703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430703).length < 2 ^ (prefixWord ++ tailWord_6430703).sum := by decide
  have hdescent : baseEnd_6430703 < baseStart_6430703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430704 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 2, 2, 2]
def baseStart_6430704 : Nat := 118140960795 + 6430704 * 2 ^ 59
def prefixEnd_6430704 : Nat := 4983230072969 + 3 ^ 40 * 6430704 * 2
def baseEnd_6430704 : Nat := 3302042098790713074725737

theorem tailTrace_6430704 : CollatzResearch.WordTrace tailWord_6430704 prefixEnd_6430704 3302042098790713074725737 := by
  unfold tailWord_6430704
  simp only [CollatzResearch.WordTrace]
  refine ⟨117273521847332579825013583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156364695796443439766684777 117273521847332579825013583)
  ·
    refine ⟨175910282770998869737520375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117273521847332579825013583 175910282770998869737520375)
    ·
      refine ⟨263865424156498304606280563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175910282770998869737520375 263865424156498304606280563)
      ·
        refine ⟨395798136234747456909420845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263865424156498304606280563 395798136234747456909420845)
        ·
          refine ⟨148424301088030296341032817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395798136234747456909420845 148424301088030296341032817)
          ·
            refine ⟨111318225816022722255774613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148424301088030296341032817 111318225816022722255774613)
            ·
              refine ⟨5218041835126065105739435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111318225816022722255774613 5218041835126065105739435)
              ·
                refine ⟨7827062752689097658609153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218041835126065105739435 7827062752689097658609153)
                ·
                  refine ⟨5870297064516823243956865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7827062752689097658609153 5870297064516823243956865)
                  ·
                    refine ⟨4402722798387617432967649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5870297064516823243956865 4402722798387617432967649)
                    ·
                      refine ⟨3302042098790713074725737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402722798387617432967649 3302042098790713074725737)
                      ·
                        rfl

theorem cell23_6430704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 2, 2, 2].length) (baseStart_6430704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430704 prefixEnd_6430704 := by exact prefixLift 6430704
  have htrace : WordTrace (prefixWord ++ tailWord_6430704) baseStart_6430704 baseEnd_6430704 := by
    simpa [prefixWord, tailWord_6430704, baseEnd_6430704] using wordTrace_append hprefix tailTrace_6430704
  have hstable : (prefixWord ++ tailWord_6430704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430704).length < 2 ^ (prefixWord ++ tailWord_6430704).sum := by decide
  have hdescent : baseEnd_6430704 < baseStart_6430704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430770 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_6430770 : Nat := 118140960795 + 6430770 * 2 ^ 59
def prefixEnd_6430770 : Nat := 4983230072969 + 3 ^ 40 * 6430770 * 2
def baseEnd_6430770 : Nat := 1100691996171303272166811

theorem tailTrace_6430770 : CollatzResearch.WordTrace tailWord_6430770 prefixEnd_6430770 1100691996171303272166811 := by
  unfold tailWord_6430770
  simp only [CollatzResearch.WordTrace]
  refine ⟨58637362728106513230482441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156366300608284035281286509 58637362728106513230482441)
  ·
    refine ⟨43978022046079884922861831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58637362728106513230482441 43978022046079884922861831)
    ·
      refine ⟨65967033069119827384292747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43978022046079884922861831 65967033069119827384292747)
      ·
        refine ⟨98950549603679741076439121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65967033069119827384292747 98950549603679741076439121)
        ·
          refine ⟨74212912202759805807329341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98950549603679741076439121 74212912202759805807329341)
          ·
            refine ⟨27829842076034927177748503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74212912202759805807329341 27829842076034927177748503)
            ·
              refine ⟨41744763114052390766622755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27829842076034927177748503 41744763114052390766622755)
              ·
                refine ⟨62617144671078586149934133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41744763114052390766622755 62617144671078586149934133)
                ·
                  refine ⟨5870357312913617451556325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62617144671078586149934133 5870357312913617451556325)
                  ·
                    refine ⟨1100691996171303272166811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5870357312913617451556325 1100691996171303272166811)
                    ·
                      rfl

theorem cell23_6430770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_6430770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430770 prefixEnd_6430770 := by exact prefixLift 6430770
  have htrace : WordTrace (prefixWord ++ tailWord_6430770) baseStart_6430770 baseEnd_6430770 := by
    simpa [prefixWord, tailWord_6430770, baseEnd_6430770] using wordTrace_append hprefix tailTrace_6430770
  have hstable : (prefixWord ++ tailWord_6430770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430770).length < 2 ^ (prefixWord ++ tailWord_6430770).sum := by decide
  have hdescent : baseEnd_6430770 < baseStart_6430770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430780 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_6430780 : Nat := 118140960795 + 6430780 * 2 ^ 59
def prefixEnd_6430780 : Nat := 4983230072969 + 3 ^ 40 * 6430780 * 2
def baseEnd_6430780 : Nat := 3302081123320454777375387

theorem tailTrace_6430780 : CollatzResearch.WordTrace tailWord_6430780 prefixEnd_6430780 3302081123320454777375387 := by
  unfold tailWord_6430780
  simp only [CollatzResearch.WordTrace]
  refine ⟨117274907821194912314896897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156366543761593216419862529 117274907821194912314896897)
  ·
    refine ⟨87956180865896184236172673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117274907821194912314896897 87956180865896184236172673)
    ·
      refine ⟨65967135649422138177129505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87956180865896184236172673 65967135649422138177129505)
      ·
        refine ⟨49475351737066603632847129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65967135649422138177129505 49475351737066603632847129)
        ·
          refine ⟨37106513802799952724635347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49475351737066603632847129 37106513802799952724635347)
          ·
            refine ⟨55659770704199929086953021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37106513802799952724635347 55659770704199929086953021)
            ·
              refine ⟨20872414014074973407607383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55659770704199929086953021 20872414014074973407607383)
              ·
                refine ⟨31308621021112460111411075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20872414014074973407607383 31308621021112460111411075)
                ·
                  refine ⟨46962931531668690167116613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31308621021112460111411075 46962931531668690167116613)
                  ·
                    refine ⟨8805549662187879406334365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46962931531668690167116613 8805549662187879406334365)
                    ·
                      refine ⟨3302081123320454777375387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8805549662187879406334365 3302081123320454777375387)
                      ·
                        rfl

theorem cell23_6430780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_6430780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430780 prefixEnd_6430780 := by exact prefixLift 6430780
  have htrace : WordTrace (prefixWord ++ tailWord_6430780) baseStart_6430780 baseEnd_6430780 := by
    simpa [prefixWord, tailWord_6430780, baseEnd_6430780] using wordTrace_append hprefix tailTrace_6430780
  have hstable : (prefixWord ++ tailWord_6430780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430780).length < 2 ^ (prefixWord ++ tailWord_6430780).sum := by decide
  have hdescent : baseEnd_6430780 < baseStart_6430780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430797 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_6430797 : Nat := 118140960795 + 6430797 * 2 ^ 59
def prefixEnd_6430797 : Nat := 4983230072969 + 3 ^ 40 * 6430797 * 2
def baseEnd_6430797 : Nat := 3302089852491581210862809

theorem tailTrace_6430797 : CollatzResearch.WordTrace tailWord_6430797 prefixEnd_6430797 3302089852491581210862809 := by
  unfold tailWord_6430797
  simp only [CollatzResearch.WordTrace]
  refine ⟨234550435683328236533162645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156366957122218824355441763 234550435683328236533162645)
  ·
    refine ⟨10994551672656011087491999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 234550435683328236533162645 10994551672656011087491999)
    ·
      refine ⟨16491827508984016631237999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10994551672656011087491999 16491827508984016631237999)
      ·
        refine ⟨24737741263476024946856999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16491827508984016631237999 24737741263476024946856999)
        ·
          refine ⟨37106611895214037420285499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24737741263476024946856999 37106611895214037420285499)
          ·
            refine ⟨55659917842821056130428249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37106611895214037420285499 55659917842821056130428249)
            ·
              refine ⟨41744938382115792097821187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55659917842821056130428249 41744938382115792097821187)
              ·
                refine ⟨62617407573173688146731781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41744938382115792097821187 62617407573173688146731781)
                ·
                  refine ⟨11740763919970066527512209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62617407573173688146731781 11740763919970066527512209)
                  ·
                    refine ⟨8805572939977549895634157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11740763919970066527512209 8805572939977549895634157)
                    ·
                      refine ⟨3302089852491581210862809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8805572939977549895634157 3302089852491581210862809)
                      ·
                        rfl

theorem cell23_6430797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_6430797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430797 prefixEnd_6430797 := by exact prefixLift 6430797
  have htrace : WordTrace (prefixWord ++ tailWord_6430797) baseStart_6430797 baseEnd_6430797 := by
    simpa [prefixWord, tailWord_6430797, baseEnd_6430797] using wordTrace_append hprefix tailTrace_6430797
  have hstable : (prefixWord ++ tailWord_6430797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430797).length < 2 ^ (prefixWord ++ tailWord_6430797).sum := by decide
  have hdescent : baseEnd_6430797 < baseStart_6430797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430868 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 6]
def baseStart_6430868 : Nat := 118140960795 + 6430868 * 2 ^ 59
def prefixEnd_6430868 : Nat := 4983230072969 + 3 ^ 40 * 6430868 * 2
def baseEnd_6430868 : Nat := 366902923290894492563887

theorem tailTrace_6430868 : CollatzResearch.WordTrace tailWord_6430868 prefixEnd_6430868 366902923290894492563887 := by
  unfold tailWord_6430868
  simp only [CollatzResearch.WordTrace]
  refine ⟨117276512633035507829498629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156368683510714010439331505 117276512633035507829498629)
  ·
    refine ⟨21989346118694157718030993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117276512633035507829498629 21989346118694157718030993)
    ·
      refine ⟨16492009589020618288523245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21989346118694157718030993 16492009589020618288523245)
      ·
        refine ⟨6184503595882731858196217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16492009589020618288523245 6184503595882731858196217)
        ·
          refine ⟨4638377696912048893647163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6184503595882731858196217 4638377696912048893647163)
          ·
            refine ⟨6957566545368073340470745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4638377696912048893647163 6957566545368073340470745)
            ·
              refine ⟨5218174909026055005353059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6957566545368073340470745 5218174909026055005353059)
              ·
                refine ⟨7827262363539082508029589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218174909026055005353059 7827262363539082508029589)
                ·
                  refine ⟨366902923290894492563887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7827262363539082508029589 366902923290894492563887)
                  ·
                    rfl

theorem cell23_6430868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_6430868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430868 prefixEnd_6430868 := by exact prefixLift 6430868
  have htrace : WordTrace (prefixWord ++ tailWord_6430868) baseStart_6430868 baseEnd_6430868 := by
    simpa [prefixWord, tailWord_6430868, baseEnd_6430868] using wordTrace_append hprefix tailTrace_6430868
  have hstable : (prefixWord ++ tailWord_6430868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430868).length < 2 ^ (prefixWord ++ tailWord_6430868).sum := by decide
  have hdescent : baseEnd_6430868 < baseStart_6430868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430880 : List Nat := [2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 6]
def baseStart_6430880 : Nat := 118140960795 + 6430880 * 2 ^ 59
def prefixEnd_6430880 : Nat := 4983230072969 + 3 ^ 40 * 6430880 * 2
def baseEnd_6430880 : Nat := 3302132471385904386124927

theorem tailTrace_6430880 : CollatzResearch.WordTrace tailWord_6430880 prefixEnd_6430880 3302132471385904386124927 := by
  unfold tailWord_6430880
  simp only [CollatzResearch.WordTrace]
  refine ⟨117276731471013770854217047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156368975294685027805622729 117276731471013770854217047)
  ·
    refine ⟨175915097206520656281325571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117276731471013770854217047 175915097206520656281325571)
    ·
      refine ⟨263872645809780984421988357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175915097206520656281325571 263872645809780984421988357)
      ·
        refine ⟨49476121089333934579122817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263872645809780984421988357 49476121089333934579122817)
        ·
          refine ⟨37107090817000450934342113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49476121089333934579122817 37107090817000450934342113)
          ·
            refine ⟨27830318112750338200756585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37107090817000450934342113 27830318112750338200756585)
            ·
              refine ⟨20872738584562753650567439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27830318112750338200756585 20872738584562753650567439)
              ·
                refine ⟨31309107876844130475851159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20872738584562753650567439 31309107876844130475851159)
                ·
                  refine ⟨46963661815266195713776739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31309107876844130475851159 46963661815266195713776739)
                  ·
                    refine ⟨70445492722899293570665109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46963661815266195713776739 70445492722899293570665109)
                    ·
                      refine ⟨3302132471385904386124927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70445492722899293570665109 3302132471385904386124927)
                      ·
                        rfl

theorem cell23_6430880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_6430880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430880 prefixEnd_6430880 := by exact prefixLift 6430880
  have htrace : WordTrace (prefixWord ++ tailWord_6430880) baseStart_6430880 baseEnd_6430880 := by
    simpa [prefixWord, tailWord_6430880, baseEnd_6430880] using wordTrace_append hprefix tailTrace_6430880
  have hstable : (prefixWord ++ tailWord_6430880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430880).length < 2 ^ (prefixWord ++ tailWord_6430880).sum := by decide
  have hdescent : baseEnd_6430880 < baseStart_6430880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430904 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 1, 2, 3]
def baseStart_6430904 : Nat := 118140960795 + 6430904 * 2 ^ 59
def prefixEnd_6430904 : Nat := 4983230072969 + 3 ^ 40 * 6430904 * 2
def baseEnd_6430904 : Nat := 3302144794921612292224817

theorem tailTrace_6430904 : CollatzResearch.WordTrace tailWord_6430904 prefixEnd_6430904 3302144794921612292224817 := by
  unfold tailWord_6430904
  simp only [CollatzResearch.WordTrace]
  refine ⟨117277169146970296903653883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156369558862627062538205177 117277169146970296903653883)
  ·
    refine ⟨175915753720455445355480825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117277169146970296903653883 175915753720455445355480825)
    ·
      refine ⟨131936815290341584016610619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175915753720455445355480825 131936815290341584016610619)
      ·
        refine ⟨197905222935512376024915929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131936815290341584016610619 197905222935512376024915929)
        ·
          refine ⟨148428917201634282018686947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197905222935512376024915929 148428917201634282018686947)
          ·
            refine ⟨222643375802451423028030421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148428917201634282018686947 222643375802451423028030421)
            ·
              refine ⟨5218204120369955227219463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 222643375802451423028030421 5218204120369955227219463)
              ·
                refine ⟨7827306180554932840829195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218204120369955227219463 7827306180554932840829195)
                ·
                  refine ⟨11740959270832399261243793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7827306180554932840829195 11740959270832399261243793)
                  ·
                    refine ⟨8805719453124299445932845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11740959270832399261243793 8805719453124299445932845)
                    ·
                      refine ⟨3302144794921612292224817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8805719453124299445932845 3302144794921612292224817)
                      ·
                        rfl

theorem cell23_6430904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 2, 3].length) (baseStart_6430904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430904 prefixEnd_6430904 := by exact prefixLift 6430904
  have htrace : WordTrace (prefixWord ++ tailWord_6430904) baseStart_6430904 baseEnd_6430904 := by
    simpa [prefixWord, tailWord_6430904, baseEnd_6430904] using wordTrace_append hprefix tailTrace_6430904
  have hstable : (prefixWord ++ tailWord_6430904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430904).length < 2 ^ (prefixWord ++ tailWord_6430904).sum := by decide
  have hdescent : baseEnd_6430904 < baseStart_6430904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430917 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 4, 1, 3]
def baseStart_6430917 : Nat := 118140960795 + 6430917 * 2 ^ 59
def prefixEnd_6430917 : Nat := 4983230072969 + 3 ^ 40 * 6430917 * 2
def baseEnd_6430917 : Nat := 3302151470170120741362257

theorem tailTrace_6430917 : CollatzResearch.WordTrace tailWord_6430917 prefixEnd_6430917 3302151470170120741362257 := by
  unfold tailWord_6430917
  simp only [CollatzResearch.WordTrace]
  refine ⟨234554812442893497027531005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156369874961928998018354003 234554812442893497027531005)
  ·
    refine ⟨87958054666085061385324127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234554812442893497027531005 87958054666085061385324127)
    ·
      refine ⟨131937081999127592077986191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87958054666085061385324127 131937081999127592077986191)
      ·
        refine ⟨197905622998691388116979287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131937081999127592077986191 197905622998691388116979287)
        ·
          refine ⟨296858434498037082175468931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197905622998691388116979287 296858434498037082175468931)
          ·
            refine ⟨445287651747055623263203397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296858434498037082175468931 445287651747055623263203397)
            ·
              refine ⟨83491434702572929361850637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 445287651747055623263203397 83491434702572929361850637)
              ·
                refine ⟨31309288013464848510693989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83491434702572929361850637 31309288013464848510693989)
                ·
                  refine ⟨5870491502524659095755123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31309288013464848510693989 5870491502524659095755123)
                  ·
                    refine ⟨8805737253786988643632685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5870491502524659095755123 8805737253786988643632685)
                    ·
                      refine ⟨3302151470170120741362257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8805737253786988643632685 3302151470170120741362257)
                      ·
                        rfl

theorem cell23_6430917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_6430917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430917 prefixEnd_6430917 := by exact prefixLift 6430917
  have htrace : WordTrace (prefixWord ++ tailWord_6430917) baseStart_6430917 baseEnd_6430917 := by
    simpa [prefixWord, tailWord_6430917, baseEnd_6430917] using wordTrace_append hprefix tailTrace_6430917
  have hstable : (prefixWord ++ tailWord_6430917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430917).length < 2 ^ (prefixWord ++ tailWord_6430917).sum := by decide
  have hdescent : baseEnd_6430917 < baseStart_6430917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430924 : List Nat := [2, 2, 1, 6, 1, 2, 1, 8]
def baseStart_6430924 : Nat := 118140960795 + 6430924 * 2 ^ 59
def prefixEnd_6430924 : Nat := 4983230072969 + 3 ^ 40 * 6430924 * 2
def baseEnd_6430924 : Nat := 122302039427211193110175

theorem tailTrace_6430924 : CollatzResearch.WordTrace tailWord_6430924 prefixEnd_6430924 122302039427211193110175 := by
  unfold tailWord_6430924
  simp only [CollatzResearch.WordTrace]
  refine ⟨117277533876934068611517913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156370045169245424815357217 117277533876934068611517913)
  ·
    refine ⟨87958150407700551458638435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117277533876934068611517913 87958150407700551458638435)
    ·
      refine ⟨131937225611550827187957653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87958150407700551458638435 131937225611550827187957653)
      ·
        refine ⟨6184557450541445024435515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131937225611550827187957653 6184557450541445024435515)
        ·
          refine ⟨9276836175812167536653273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6184557450541445024435515 9276836175812167536653273)
          ·
            refine ⟨6957627131859125652489955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9276836175812167536653273 6957627131859125652489955)
            ·
              refine ⟨10436440697788688478734933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6957627131859125652489955 10436440697788688478734933)
              ·
                refine ⟨122302039427211193110175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10436440697788688478734933 122302039427211193110175)
                ·
                  rfl

theorem cell23_6430924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 8].length) (baseStart_6430924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430924 prefixEnd_6430924 := by exact prefixLift 6430924
  have htrace : WordTrace (prefixWord ++ tailWord_6430924) baseStart_6430924 baseEnd_6430924 := by
    simpa [prefixWord, tailWord_6430924, baseEnd_6430924] using wordTrace_append hprefix tailTrace_6430924
  have hstable : (prefixWord ++ tailWord_6430924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430924).length < 2 ^ (prefixWord ++ tailWord_6430924).sum := by decide
  have hdescent : baseEnd_6430924 < baseStart_6430924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430927 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 5, 3, 2]
def baseStart_6430927 : Nat := 118140960795 + 6430927 * 2 ^ 59
def prefixEnd_6430927 : Nat := 4983230072969 + 3 ^ 40 * 6430927 * 2
def baseEnd_6430927 : Nat := 3302156604976665702237211

theorem tailTrace_6430927 : CollatzResearch.WordTrace tailWord_6430927 prefixEnd_6430927 3302156604976665702237211 := by
  unfold tailWord_6430927
  simp only [CollatzResearch.WordTrace]
  refine ⟨234555177172857268735395035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156370118115238179156930023 234555177172857268735395035)
  ·
    refine ⟨351832765759285903103092553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234555177172857268735395035 351832765759285903103092553)
    ·
      refine ⟨263874574319464427327319415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351832765759285903103092553 263874574319464427327319415)
      ·
        refine ⟨395811861479196640990979123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263874574319464427327319415 395811861479196640990979123)
        ·
          refine ⟨593717792218794961486468685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395811861479196640990979123 593717792218794961486468685)
          ·
            refine ⟨222644172082048110557425757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 593717792218794961486468685 222644172082048110557425757)
            ·
              refine ⟨83491564530768041459034659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222644172082048110557425757 83491564530768041459034659)
              ·
                refine ⟨125237346796152062188551989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83491564530768041459034659 125237346796152062188551989)
                ·
                  refine ⟨11741001262139255830176749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125237346796152062188551989 11741001262139255830176749)
                  ·
                    refine ⟨4402875473302220936316281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11741001262139255830176749 4402875473302220936316281)
                    ·
                      refine ⟨3302156604976665702237211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402875473302220936316281 3302156604976665702237211)
                      ·
                        rfl

theorem cell23_6430927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 3, 2].length) (baseStart_6430927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430927 prefixEnd_6430927 := by exact prefixLift 6430927
  have htrace : WordTrace (prefixWord ++ tailWord_6430927) baseStart_6430927 baseEnd_6430927 := by
    simpa [prefixWord, tailWord_6430927, baseEnd_6430927] using wordTrace_append hprefix tailTrace_6430927
  have hstable : (prefixWord ++ tailWord_6430927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430927).length < 2 ^ (prefixWord ++ tailWord_6430927).sum := by decide
  have hdescent : baseEnd_6430927 < baseStart_6430927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430944 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 1, 3, 2]
def baseStart_6430944 : Nat := 118140960795 + 6430944 * 2 ^ 59
def prefixEnd_6430944 : Nat := 4983230072969 + 3 ^ 40 * 6430944 * 2
def baseEnd_6430944 : Nat := 3302165334147792135724633

theorem tailTrace_6430944 : CollatzResearch.WordTrace tailWord_6430944 prefixEnd_6430944 3302165334147792135724633 := by
  unfold tailWord_6430944
  simp only [CollatzResearch.WordTrace]
  refine ⟨117277898606897840319381943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156370531475863787092509257 117277898606897840319381943)
  ·
    refine ⟨175916847910346760479072915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117277898606897840319381943 175916847910346760479072915)
    ·
      refine ⟨263875271865520140718609373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175916847910346760479072915 263875271865520140718609373)
      ·
        refine ⟨98953226949570052769478515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263875271865520140718609373 98953226949570052769478515)
        ·
          refine ⟨148429840424355079154217773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98953226949570052769478515 148429840424355079154217773)
          ·
            refine ⟨55661190159133154682831665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148429840424355079154217773 55661190159133154682831665)
            ·
              refine ⟨41745892619349866012123749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55661190159133154682831665 41745892619349866012123749)
              ·
                refine ⟨7827354866128099877273203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41745892619349866012123749 7827354866128099877273203)
                ·
                  refine ⟨11741032299192149815909805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7827354866128099877273203 11741032299192149815909805)
                  ·
                    refine ⟨4402887112197056180966177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11741032299192149815909805 4402887112197056180966177)
                    ·
                      refine ⟨3302165334147792135724633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402887112197056180966177 3302165334147792135724633)
                      ·
                        rfl

theorem cell23_6430944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_6430944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430944 prefixEnd_6430944 := by exact prefixLift 6430944
  have htrace : WordTrace (prefixWord ++ tailWord_6430944) baseStart_6430944 baseEnd_6430944 := by
    simpa [prefixWord, tailWord_6430944, baseEnd_6430944] using wordTrace_append hprefix tailTrace_6430944
  have hstable : (prefixWord ++ tailWord_6430944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430944).length < 2 ^ (prefixWord ++ tailWord_6430944).sum := by decide
  have hdescent : baseEnd_6430944 < baseStart_6430944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430960 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 5]
def baseStart_6430960 : Nat := 118140960795 + 6430960 * 2 ^ 59
def prefixEnd_6430960 : Nat := 4983230072969 + 3 ^ 40 * 6430960 * 2
def baseEnd_6430960 : Nat := 3302173549838264073124559

theorem tailTrace_6430960 : CollatzResearch.WordTrace tailWord_6430960 prefixEnd_6430960 3302173549838264073124559 := by
  unfold tailWord_6430960
  simp only [CollatzResearch.WordTrace]
  refine ⟨117278190390868857685673167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156370920521158476914230889 117278190390868857685673167)
  ·
    refine ⟨175917285586303286528509751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117278190390868857685673167 175917285586303286528509751)
    ·
      refine ⟨263875928379454929792764627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175917285586303286528509751 263875928379454929792764627)
      ·
        refine ⟨395813892569182394689146941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263875928379454929792764627 395813892569182394689146941)
        ·
          refine ⟨148430209713443398008430103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395813892569182394689146941 148430209713443398008430103)
          ·
            refine ⟨222645314570165097012645155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148430209713443398008430103 222645314570165097012645155)
            ·
              refine ⟨333967971855247645518967733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222645314570165097012645155 333967971855247645518967733)
              ·
                refine ⟨31309497361429466767403225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 333967971855247645518967733 31309497361429466767403225)
                ·
                  refine ⟨23482123021072100075552419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31309497361429466767403225 23482123021072100075552419)
                  ·
                    refine ⟨35223184531608150113328629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23482123021072100075552419 35223184531608150113328629)
                    ·
                      refine ⟨3302173549838264073124559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35223184531608150113328629 3302173549838264073124559)
                      ·
                        rfl

theorem cell23_6430960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_6430960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430960 prefixEnd_6430960 := by exact prefixLift 6430960
  have htrace : WordTrace (prefixWord ++ tailWord_6430960) baseStart_6430960 baseEnd_6430960 := by
    simpa [prefixWord, tailWord_6430960, baseEnd_6430960] using wordTrace_append hprefix tailTrace_6430960
  have hstable : (prefixWord ++ tailWord_6430960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430960).length < 2 ^ (prefixWord ++ tailWord_6430960).sum := by decide
  have hdescent : baseEnd_6430960 < baseStart_6430960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6430961 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 1, 3, 2]
def baseStart_6430961 : Nat := 118140960795 + 6430961 * 2 ^ 59
def prefixEnd_6430961 : Nat := 4983230072969 + 3 ^ 40 * 6430961 * 2
def baseEnd_6430961 : Nat := 3302174063318918569212055

theorem tailTrace_6430961 : CollatzResearch.WordTrace tailWord_6430961 prefixEnd_6430961 3302174063318918569212055 := by
  unfold tailWord_6430961
  simp only [CollatzResearch.WordTrace]
  refine ⟨234556417254734092542132737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156370944836489395028088491 234556417254734092542132737)
  ·
    refine ⟨175917312941050569406599553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234556417254734092542132737 175917312941050569406599553)
    ·
      refine ⟨131937984705787927054949665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175917312941050569406599553 131937984705787927054949665)
      ·
        refine ⟨98953488529340945291212249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131937984705787927054949665 98953488529340945291212249)
        ·
          refine ⟨74215116397005708968409187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98953488529340945291212249 74215116397005708968409187)
          ·
            refine ⟨111322674595508563452613781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74215116397005708968409187 111322674595508563452613781)
            ·
              refine ⟨5218250371664463911841271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111322674595508563452613781 5218250371664463911841271)
              ·
                refine ⟨7827375557496695867761907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218250371664463911841271 7827375557496695867761907)
                ·
                  refine ⟨11741063336245043801642861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7827375557496695867761907 11741063336245043801642861)
                  ·
                    refine ⟨4402898751091891425616073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11741063336245043801642861 4402898751091891425616073)
                    ·
                      refine ⟨3302174063318918569212055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4402898751091891425616073 3302174063318918569212055)
                      ·
                        rfl

theorem cell23_6430961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_6430961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6430961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6430961 prefixEnd_6430961 := by exact prefixLift 6430961
  have htrace : WordTrace (prefixWord ++ tailWord_6430961) baseStart_6430961 baseEnd_6430961 := by
    simpa [prefixWord, tailWord_6430961, baseEnd_6430961] using wordTrace_append hprefix tailTrace_6430961
  have hstable : (prefixWord ++ tailWord_6430961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6430961).length < 2 ^ (prefixWord ++ tailWord_6430961).sum := by decide
  have hdescent : baseEnd_6430961 < baseStart_6430961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6430961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431027 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 2, 5]
def baseStart_6431027 : Nat := 118140960795 + 6431027 * 2 ^ 59
def prefixEnd_6431027 : Nat := 4983230072969 + 3 ^ 40 * 6431027 * 2
def baseEnd_6431027 : Nat := 1100735984347371770328917

theorem tailTrace_6431027 : CollatzResearch.WordTrace tailWord_6431027 prefixEnd_6431027 1100735984347371770328917 := by
  unfold tailWord_6431027
  simp only [CollatzResearch.WordTrace]
  refine ⟨234558824472494985814035335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156372549648329990542690223 234558824472494985814035335)
  ·
    refine ⟨351838236708742478721053003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234558824472494985814035335 351838236708742478721053003)
    ·
      refine ⟨527757355063113718081579505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351838236708742478721053003 527757355063113718081579505)
      ·
        refine ⟨395818016297335288561184629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527757355063113718081579505 395818016297335288561184629)
        ·
          refine ⟨37107939027875183302611059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 395818016297335288561184629 37107939027875183302611059)
          ·
            refine ⟨55661908541812774953916589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37107939027875183302611059 55661908541812774953916589)
            ·
              refine ⟨20873215703179790607718721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55661908541812774953916589 20873215703179790607718721)
              ·
                refine ⟨15654911777384842955789041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20873215703179790607718721 15654911777384842955789041)
                ·
                  refine ⟨11741183833038632216841781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15654911777384842955789041 11741183833038632216841781)
                  ·
                    refine ⟨1100735984347371770328917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11741183833038632216841781 1100735984347371770328917)
                    ·
                      rfl

theorem cell23_6431027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 2, 5].length) (baseStart_6431027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431027 prefixEnd_6431027 := by exact prefixLift 6431027
  have htrace : WordTrace (prefixWord ++ tailWord_6431027) baseStart_6431027 baseEnd_6431027 := by
    simpa [prefixWord, tailWord_6431027, baseEnd_6431027] using wordTrace_append hprefix tailTrace_6431027
  have hstable : (prefixWord ++ tailWord_6431027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431027).length < 2 ^ (prefixWord ++ tailWord_6431027).sum := by decide
  have hdescent : baseEnd_6431027 < baseStart_6431027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431040 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 2, 8]
def baseStart_6431040 : Nat := 118140960795 + 6431040 * 2 ^ 59
def prefixEnd_6431040 : Nat := 4983230072969 + 3 ^ 40 * 6431040 * 2
def baseEnd_6431040 : Nat := 1100738209430207920041397

theorem tailTrace_6431040 : CollatzResearch.WordTrace tailWord_6431040 prefixEnd_6431040 1100738209430207920041397 := by
  unfold tailWord_6431040
  simp only [CollatzResearch.WordTrace]
  refine ⟨117279649310723944517129287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156372865747631926022839049 117279649310723944517129287)
  ·
    refine ⟨175919473966085916775693931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117279649310723944517129287 175919473966085916775693931)
    ·
      refine ⟨263879210949128875163540897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175919473966085916775693931 263879210949128875163540897)
      ·
        refine ⟨197909408211846656372655673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263879210949128875163540897 197909408211846656372655673)
        ·
          refine ⟨148432056158884992279491755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197909408211846656372655673 148432056158884992279491755)
          ·
            refine ⟨222648084238327488419237633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148432056158884992279491755 222648084238327488419237633)
            ·
              refine ⟨166986063178745616314428225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222648084238327488419237633 166986063178745616314428225)
              ·
                refine ⟨125239547384059212235821169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166986063178745616314428225 125239547384059212235821169)
                ·
                  refine ⟨93929660538044409176865877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125239547384059212235821169 93929660538044409176865877)
                  ·
                    refine ⟨1100738209430207920041397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93929660538044409176865877 1100738209430207920041397)
                    ·
                      rfl

theorem cell23_6431040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_6431040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431040 prefixEnd_6431040 := by exact prefixLift 6431040
  have htrace : WordTrace (prefixWord ++ tailWord_6431040) baseStart_6431040 baseEnd_6431040 := by
    simpa [prefixWord, tailWord_6431040, baseEnd_6431040] using wordTrace_append hprefix tailTrace_6431040
  have hstable : (prefixWord ++ tailWord_6431040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431040).length < 2 ^ (prefixWord ++ tailWord_6431040).sum := by decide
  have hdescent : baseEnd_6431040 < baseStart_6431040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431047 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_6431047 : Nat := 118140960795 + 6431047 * 2 ^ 59
def prefixEnd_6431047 : Nat := 4983230072969 + 3 ^ 40 * 6431047 * 2
def baseEnd_6431047 : Nat := 3302218222655205232736659

theorem tailTrace_6431047 : CollatzResearch.WordTrace tailWord_6431047 prefixEnd_6431047 3302218222655205232736659 := by
  unfold tailWord_6431047
  simp only [CollatzResearch.WordTrace]
  refine ⟨234559553932422529229763395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156373035954948352819842263 234559553932422529229763395)
  ·
    refine ⟨351839330898633793844645093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234559553932422529229763395 351839330898633793844645093)
    ·
      refine ⟨65969874543493836345870955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351839330898633793844645093 65969874543493836345870955)
      ·
        refine ⟨98954811815240754518806433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65969874543493836345870955 98954811815240754518806433)
        ·
          refine ⟨74216108861430565889104825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98954811815240754518806433 74216108861430565889104825)
          ·
            refine ⟨55662081646072924416828619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74216108861430565889104825 55662081646072924416828619)
            ·
              refine ⟨83493122469109386625242929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55662081646072924416828619 83493122469109386625242929)
              ·
                refine ⟨62619841851832039968932197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83493122469109386625242929 62619841851832039968932197)
                ·
                  refine ⟨11741220347218507494174787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62619841851832039968932197 11741220347218507494174787)
                  ·
                    refine ⟨17611830520827761241262181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11741220347218507494174787 17611830520827761241262181)
                    ·
                      refine ⟨3302218222655205232736659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17611830520827761241262181 3302218222655205232736659)
                      ·
                        rfl

theorem cell23_6431047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_6431047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431047 prefixEnd_6431047 := by exact prefixLift 6431047
  have htrace : WordTrace (prefixWord ++ tailWord_6431047) baseStart_6431047 baseEnd_6431047 := by
    simpa [prefixWord, tailWord_6431047, baseEnd_6431047] using wordTrace_append hprefix tailTrace_6431047
  have hstable : (prefixWord ++ tailWord_6431047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431047).length < 2 ^ (prefixWord ++ tailWord_6431047).sum := by decide
  have hdescent : baseEnd_6431047 < baseStart_6431047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431097 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 2, 5, 3]
def baseStart_6431097 : Nat := 118140960795 + 6431097 * 2 ^ 59
def prefixEnd_6431097 : Nat := 4983230072969 + 3 ^ 40 * 6431097 * 2
def baseEnd_6431097 : Nat := 3302243896687930037111429

theorem tailTrace_6431097 : CollatzResearch.WordTrace tailWord_6431097 prefixEnd_6431097 3302243896687930037111429 := by
  unfold tailWord_6431097
  simp only [CollatzResearch.WordTrace]
  refine ⟨234561377582241387769083545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156374251721494258512722363 234561377582241387769083545)
  ·
    refine ⟨175921033186681040826812659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234561377582241387769083545 175921033186681040826812659)
    ·
      refine ⟨263881549780021561240218989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175921033186681040826812659 263881549780021561240218989)
      ·
        refine ⟨98955581167508085465082121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263881549780021561240218989 98955581167508085465082121)
        ·
          refine ⟨74216685875631064098811591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98955581167508085465082121 74216685875631064098811591)
          ·
            refine ⟨111325028813446596148217387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74216685875631064098811591 111325028813446596148217387)
            ·
              refine ⟨166987543220169894222326081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111325028813446596148217387 166987543220169894222326081)
              ·
                refine ⟨125240657415127420666744561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166987543220169894222326081 125240657415127420666744561)
                ·
                  refine ⟨93930493061345565500058421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125240657415127420666744561 93930493061345565500058421)
                  ·
                    refine ⟨8805983724501146765630477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93930493061345565500058421 8805983724501146765630477)
                    ·
                      refine ⟨3302243896687930037111429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8805983724501146765630477 3302243896687930037111429)
                      ·
                        rfl

theorem cell23_6431097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_6431097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431097 prefixEnd_6431097 := by exact prefixLift 6431097
  have htrace : WordTrace (prefixWord ++ tailWord_6431097) baseStart_6431097 baseEnd_6431097 := by
    simpa [prefixWord, tailWord_6431097, baseEnd_6431097] using wordTrace_append hprefix tailTrace_6431097
  have hstable : (prefixWord ++ tailWord_6431097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431097).length < 2 ^ (prefixWord ++ tailWord_6431097).sum := by decide
  have hdescent : baseEnd_6431097 < baseStart_6431097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431118 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6431118 : Nat := 118140960795 + 6431118 * 2 ^ 59
def prefixEnd_6431118 : Nat := 4983230072969 + 3 ^ 40 * 6431118 * 2
def baseEnd_6431118 : Nat := 3302254679781674454948833

theorem tailTrace_6431118 : CollatzResearch.WordTrace tailWord_6431118 prefixEnd_6431118 3302254679781674454948833 := by
  unfold tailWord_6431118
  simp only [CollatzResearch.WordTrace]
  refine ⟨29320267939395663544449751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156374762343443538903732005 29320267939395663544449751)
  ·
    refine ⟨43980401909093495316674627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29320267939395663544449751 43980401909093495316674627)
    ·
      refine ⟨65970602863640242975011941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43980401909093495316674627 65970602863640242975011941)
      ·
        refine ⟨12369488036932545557814739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65970602863640242975011941 12369488036932545557814739)
        ·
          refine ⟨18554232055398818336722109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12369488036932545557814739 18554232055398818336722109)
          ·
            refine ⟨6957837020774556876270791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18554232055398818336722109 6957837020774556876270791)
            ·
              refine ⟨10436755531161835314406187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6957837020774556876270791 10436755531161835314406187)
              ·
                refine ⟨15655133296742752971609281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10436755531161835314406187 15655133296742752971609281)
                ·
                  refine ⟨11741349972557064728706961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15655133296742752971609281 11741349972557064728706961)
                  ·
                    refine ⟨8806012479417798546530221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11741349972557064728706961 8806012479417798546530221)
                    ·
                      refine ⟨3302254679781674454948833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8806012479417798546530221 3302254679781674454948833)
                      ·
                        rfl

theorem cell23_6431118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6431118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431118 prefixEnd_6431118 := by exact prefixLift 6431118
  have htrace : WordTrace (prefixWord ++ tailWord_6431118) baseStart_6431118 baseEnd_6431118 := by
    simpa [prefixWord, tailWord_6431118, baseEnd_6431118] using wordTrace_append hprefix tailTrace_6431118
  have hstable : (prefixWord ++ tailWord_6431118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431118).length < 2 ^ (prefixWord ++ tailWord_6431118).sum := by decide
  have hdescent : baseEnd_6431118 < baseStart_6431118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431231 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 3, 3, 2]
def baseStart_6431231 : Nat := 118140960795 + 6431231 * 2 ^ 59
def prefixEnd_6431231 : Nat := 4983230072969 + 3 ^ 40 * 6431231 * 2
def baseEnd_6431231 : Nat := 3302312703095632512835813

theorem tailTrace_6431231 : CollatzResearch.WordTrace tailWord_6431231 prefixEnd_6431231 3302312703095632512835813 := by
  unfold tailWord_6431231
  simp only [CollatzResearch.WordTrace]
  refine ⟨234566264963755928654461547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156377509975837285769641031 234566264963755928654461547)
  ·
    refine ⟨351849397445633892981692321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234566264963755928654461547 351849397445633892981692321)
    ·
      refine ⟨263887048084225419736269241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351849397445633892981692321 263887048084225419736269241)
      ·
        refine ⟨197915286063169064802201931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263887048084225419736269241 197915286063169064802201931)
        ·
          refine ⟨296872929094753597203302897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197915286063169064802201931 296872929094753597203302897)
          ·
            refine ⟨222654696821065197902477173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296872929094753597203302897 222654696821065197902477173)
            ·
              refine ⟨20873877826974862303357235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222654696821065197902477173 20873877826974862303357235)
              ·
                refine ⟨31310816740462293455035853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20873877826974862303357235 31310816740462293455035853)
                ·
                  refine ⟨11741556277673360045638445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31310816740462293455035853 11741556277673360045638445)
                  ·
                    refine ⟨4403083604127510017114417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11741556277673360045638445 4403083604127510017114417)
                    ·
                      refine ⟨3302312703095632512835813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403083604127510017114417 3302312703095632512835813)
                      ·
                        rfl

theorem cell23_6431231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 3, 2].length) (baseStart_6431231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431231 prefixEnd_6431231 := by exact prefixLift 6431231
  have htrace : WordTrace (prefixWord ++ tailWord_6431231) baseStart_6431231 baseEnd_6431231 := by
    simpa [prefixWord, tailWord_6431231, baseEnd_6431231] using wordTrace_append hprefix tailTrace_6431231
  have hstable : (prefixWord ++ tailWord_6431231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431231).length < 2 ^ (prefixWord ++ tailWord_6431231).sum := by decide
  have hdescent : baseEnd_6431231 < baseStart_6431231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431301 : List Nat := [1, 3, 1, 1, 1, 5, 1, 5, 5]
def baseStart_6431301 : Nat := 118140960795 + 6431301 * 2 ^ 59
def prefixEnd_6431301 : Nat := 4983230072969 + 3 ^ 40 * 6431301 * 2
def baseEnd_6431301 : Nat := 366927627415716359884499

theorem tailTrace_6431301 : CollatzResearch.WordTrace tailWord_6431301 prefixEnd_6431301 366927627415716359884499 := by
  unfold tailWord_6431301
  simp only [CollatzResearch.WordTrace]
  refine ⟨234568818073502330609509757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156379212049001553739673171 234568818073502330609509757)
  ·
    refine ⟨87963306777563373978566159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234568818073502330609509757 87963306777563373978566159)
    ·
      refine ⟨131944960166345060967849239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87963306777563373978566159 131944960166345060967849239)
      ·
        refine ⟨197917440249517591451773859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131944960166345060967849239 197917440249517591451773859)
        ·
          refine ⟨296876160374276387177660789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197917440249517591451773859 296876160374276387177660789)
          ·
            refine ⟨27832140035088411297905699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296876160374276387177660789 27832140035088411297905699)
            ·
              refine ⟨41748210052632616946858549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27832140035088411297905699 41748210052632616946858549)
              ·
                refine ⟨3913894692434307838767989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41748210052632616946858549 3913894692434307838767989)
                ·
                  refine ⟨366927627415716359884499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3913894692434307838767989 366927627415716359884499)
                  ·
                    rfl

theorem cell23_6431301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 5].length) (baseStart_6431301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431301 prefixEnd_6431301 := by exact prefixLift 6431301
  have htrace : WordTrace (prefixWord ++ tailWord_6431301) baseStart_6431301 baseEnd_6431301 := by
    simpa [prefixWord, tailWord_6431301, baseEnd_6431301] using wordTrace_append hprefix tailTrace_6431301
  have hstable : (prefixWord ++ tailWord_6431301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431301).length < 2 ^ (prefixWord ++ tailWord_6431301).sum := by decide
  have hdescent : baseEnd_6431301 < baseStart_6431301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431351 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 1, 6, 2]
def baseStart_6431351 : Nat := 118140960795 + 6431351 * 2 ^ 59
def prefixEnd_6431351 : Nat := 4983230072969 + 3 ^ 40 * 6431351 * 2
def baseEnd_6431351 : Nat := 3302374320774172043335261

theorem tailTrace_6431351 : CollatzResearch.WordTrace tailWord_6431351 prefixEnd_6431351 3302374320774172043335261 := by
  unfold tailWord_6431351
  simp only [CollatzResearch.WordTrace]
  refine ⟨234570641723321189148829907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156380427815547459432553271 234570641723321189148829907)
  ·
    refine ⟨351855962584981783723244861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234570641723321189148829907 351855962584981783723244861)
    ·
      refine ⟨131945985969368168896216823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351855962584981783723244861 131945985969368168896216823)
      ·
        refine ⟨197918978954052253344325235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131945985969368168896216823 197918978954052253344325235)
        ·
          refine ⟨296878468431078380016487853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197918978954052253344325235 296878468431078380016487853)
          ·
            refine ⟨111329425661654392506182945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296878468431078380016487853 111329425661654392506182945)
            ·
              refine ⟨83497069246240794379637209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111329425661654392506182945 83497069246240794379637209)
              ·
                refine ⟨62622801934680595784727907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83497069246240794379637209 62622801934680595784727907)
                ·
                  refine ⟨93934202902020893677091861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62622801934680595784727907 93934202902020893677091861)
                  ·
                    refine ⟨4403165761032229391113681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93934202902020893677091861 4403165761032229391113681)
                    ·
                      refine ⟨3302374320774172043335261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403165761032229391113681 3302374320774172043335261)
                      ·
                        rfl

theorem cell23_6431351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 6, 2].length) (baseStart_6431351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431351 prefixEnd_6431351 := by exact prefixLift 6431351
  have htrace : WordTrace (prefixWord ++ tailWord_6431351) baseStart_6431351 baseEnd_6431351 := by
    simpa [prefixWord, tailWord_6431351, baseEnd_6431351] using wordTrace_append hprefix tailTrace_6431351
  have hstable : (prefixWord ++ tailWord_6431351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431351).length < 2 ^ (prefixWord ++ tailWord_6431351).sum := by decide
  have hdescent : baseEnd_6431351 < baseStart_6431351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431402 : List Nat := [3, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6431402 : Nat := 118140960795 + 6431402 * 2 ^ 59
def prefixEnd_6431402 : Nat := 4983230072969 + 3 ^ 40 * 6431402 * 2
def baseEnd_6431402 : Nat := 3302400508287551343797527

theorem tailTrace_6431402 : CollatzResearch.WordTrace tailWord_6431402 prefixEnd_6431402 3302400508287551343797527 := by
  unfold tailWord_6431402
  simp only [CollatzResearch.WordTrace]
  refine ⟨58643125461534106214734115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156381667897424283239290973 58643125461534106214734115)
  ·
    refine ⟨87964688192301159322101173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58643125461534106214734115 87964688192301159322101173)
    ·
      refine ⟨8246689518028233686446985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87964688192301159322101173 8246689518028233686446985)
      ·
        refine ⟨6185017138521175264835239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8246689518028233686446985 6185017138521175264835239)
        ·
          refine ⟨9277525707781762897252859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6185017138521175264835239 9277525707781762897252859)
          ·
            refine ⟨13916288561672644345879289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9277525707781762897252859 13916288561672644345879289)
            ·
              refine ⟨10437216421254483259409467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13916288561672644345879289 10437216421254483259409467)
              ·
                refine ⟨15655824631881724889114201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10437216421254483259409467 15655824631881724889114201)
                ·
                  refine ⟨11741868473911293666835651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15655824631881724889114201 11741868473911293666835651)
                  ·
                    refine ⟨17612802710866940500253477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11741868473911293666835651 17612802710866940500253477)
                    ·
                      refine ⟨3302400508287551343797527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17612802710866940500253477 3302400508287551343797527)
                      ·
                        rfl

theorem cell23_6431402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6431402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431402 prefixEnd_6431402 := by exact prefixLift 6431402
  have htrace : WordTrace (prefixWord ++ tailWord_6431402) baseStart_6431402 baseEnd_6431402 := by
    simpa [prefixWord, tailWord_6431402, baseEnd_6431402] using wordTrace_append hprefix tailTrace_6431402
  have hstable : (prefixWord ++ tailWord_6431402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431402).length < 2 ^ (prefixWord ++ tailWord_6431402).sum := by decide
  have hdescent : baseEnd_6431402 < baseStart_6431402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431405 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_6431405 : Nat := 118140960795 + 6431405 * 2 ^ 59
def prefixEnd_6431405 : Nat := 4983230072969 + 3 ^ 40 * 6431405 * 2
def baseEnd_6431405 : Nat := 3302402048729514832060013

theorem tailTrace_6431405 : CollatzResearch.WordTrace tailWord_6431405 prefixEnd_6431405 3302402048729514832060013 := by
  unfold tailWord_6431405
  simp only [CollatzResearch.WordTrace]
  refine ⟨234572611265125556371295669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156381740843417037580863779 234572611265125556371295669)
  ·
    refine ⟨21991182306105520909808969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234572611265125556371295669 21991182306105520909808969)
    ·
      refine ⟨16493386729579140682356727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21991182306105520909808969 16493386729579140682356727)
      ·
        refine ⟨24740080094368711023535091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16493386729579140682356727 24740080094368711023535091)
        ·
          refine ⟨37110120141553066535302637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24740080094368711023535091 37110120141553066535302637)
          ·
            refine ⟨13916295053082399950738489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37110120141553066535302637 13916295053082399950738489)
            ·
              refine ⟨10437221289811799963053867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13916295053082399950738489 10437221289811799963053867)
              ·
                refine ⟨15655831934717699944580801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10437221289811799963053867 15655831934717699944580801)
                ·
                  refine ⟨11741873951038274958435601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15655831934717699944580801 11741873951038274958435601)
                  ·
                    refine ⟨8806405463278706218826701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11741873951038274958435601 8806405463278706218826701)
                    ·
                      refine ⟨3302402048729514832060013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8806405463278706218826701 3302402048729514832060013)
                      ·
                        rfl

theorem cell23_6431405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_6431405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431405 prefixEnd_6431405 := by exact prefixLift 6431405
  have htrace : WordTrace (prefixWord ++ tailWord_6431405) baseStart_6431405 baseEnd_6431405 := by
    simpa [prefixWord, tailWord_6431405, baseEnd_6431405] using wordTrace_append hprefix tailTrace_6431405
  have hstable : (prefixWord ++ tailWord_6431405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431405).length < 2 ^ (prefixWord ++ tailWord_6431405).sum := by decide
  have hdescent : baseEnd_6431405 < baseStart_6431405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431441 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 4]
def baseStart_6431441 : Nat := 118140960795 + 6431441 * 2 ^ 59
def prefixEnd_6431441 : Nat := 4983230072969 + 3 ^ 40 * 6431441 * 2
def baseEnd_6431441 : Nat := 3302420534033076691209847

theorem tailTrace_6431441 : CollatzResearch.WordTrace tailWord_6431441 prefixEnd_6431441 3302420534033076691209847 := by
  unfold tailWord_6431441
  simp only [CollatzResearch.WordTrace]
  refine ⟨234573924292995134519606177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156382616195330089679737451 234573924292995134519606177)
  ·
    refine ⟨175930443219746350889704633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234573924292995134519606177 175930443219746350889704633)
    ·
      refine ⟨131947832414809763167278475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175930443219746350889704633 131947832414809763167278475)
      ·
        refine ⟨197921748622214644750917713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131947832414809763167278475 197921748622214644750917713)
        ·
          refine ⟨148441311466660983563188285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197921748622214644750917713 148441311466660983563188285)
          ·
            refine ⟨55665491799997868836195607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148441311466660983563188285 55665491799997868836195607)
            ·
              refine ⟨83498237699996803254293411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55665491799997868836195607 83498237699996803254293411)
              ·
                refine ⟨125247356549995204881440117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83498237699996803254293411 125247356549995204881440117)
                ·
                  refine ⟨11741939676562050457635011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125247356549995204881440117 11741939676562050457635011)
                  ·
                    refine ⟨17612909514843075686452517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11741939676562050457635011 17612909514843075686452517)
                    ·
                      refine ⟨3302420534033076691209847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17612909514843075686452517 3302420534033076691209847)
                      ·
                        rfl

theorem cell23_6431441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_6431441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431441 prefixEnd_6431441 := by exact prefixLift 6431441
  have htrace : WordTrace (prefixWord ++ tailWord_6431441) baseStart_6431441 baseEnd_6431441 := by
    simpa [prefixWord, tailWord_6431441, baseEnd_6431441] using wordTrace_append hprefix tailTrace_6431441
  have hstable : (prefixWord ++ tailWord_6431441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431441).length < 2 ^ (prefixWord ++ tailWord_6431441).sum := by decide
  have hdescent : baseEnd_6431441 < baseStart_6431441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431452 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_6431452 : Nat := 118140960795 + 6431452 * 2 ^ 59
def prefixEnd_6431452 : Nat := 4983230072969 + 3 ^ 40 * 6431452 * 2
def baseEnd_6431452 : Nat := 3302426182320276148172297

theorem tailTrace_6431452 : CollatzResearch.WordTrace tailWord_6431452 prefixEnd_6431452 3302426182320276148172297 := by
  unfold tailWord_6431452
  simp only [CollatzResearch.WordTrace]
  refine ⟨117287162747977641699128305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156382883663970188932171073 117287162747977641699128305)
  ·
    refine ⟨87965372060983231274346229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117287162747977641699128305 87965372060983231274346229)
    ·
      refine ⟨8246753630717177931969959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87965372060983231274346229 8246753630717177931969959)
      ·
        refine ⟨12370130446075766897954939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8246753630717177931969959 12370130446075766897954939)
        ·
          refine ⟨18555195669113650346932409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12370130446075766897954939 18555195669113650346932409)
          ·
            refine ⟨13916396751835237760199307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18555195669113650346932409 13916396751835237760199307)
            ·
              refine ⟨20874595127752856640298961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13916396751835237760199307 20874595127752856640298961)
              ·
                refine ⟨15655946345814642480224221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20874595127752856640298961 15655946345814642480224221)
                ·
                  refine ⟨5870979879680490930084083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15655946345814642480224221 5870979879680490930084083)
                  ·
                    refine ⟨8806469819520736395126125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5870979879680490930084083 8806469819520736395126125)
                    ·
                      refine ⟨3302426182320276148172297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8806469819520736395126125 3302426182320276148172297)
                      ·
                        rfl

theorem cell23_6431452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_6431452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431452 prefixEnd_6431452 := by exact prefixLift 6431452
  have htrace : WordTrace (prefixWord ++ tailWord_6431452) baseStart_6431452 baseEnd_6431452 := by
    simpa [prefixWord, tailWord_6431452, baseEnd_6431452] using wordTrace_append hprefix tailTrace_6431452
  have hstable : (prefixWord ++ tailWord_6431452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431452).length < 2 ^ (prefixWord ++ tailWord_6431452).sum := by decide
  have hdescent : baseEnd_6431452 < baseStart_6431452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431478 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_6431478 : Nat := 118140960795 + 6431478 * 2 ^ 59
def prefixEnd_6431478 : Nat := 4983230072969 + 3 ^ 40 * 6431478 * 2
def baseEnd_6431478 : Nat := 3302439532817293046447177

theorem tailTrace_6431478 : CollatzResearch.WordTrace tailWord_6431478 prefixEnd_6431478 3302439532817293046447177 := by
  unfold tailWord_6431478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14660954612116318114918943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156383515862574059892468725 14660954612116318114918943)
  ·
    refine ⟨21991431918174477172378415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14660954612116318114918943 21991431918174477172378415)
    ·
      refine ⟨32987147877261715758567623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21991431918174477172378415 32987147877261715758567623)
      ·
        refine ⟨49480721815892573637851435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32987147877261715758567623 49480721815892573637851435)
        ·
          refine ⟨74221082723838860456777153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49480721815892573637851435 74221082723838860456777153)
          ·
            refine ⟨55665812042879145342582865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74221082723838860456777153 55665812042879145342582865)
            ·
              refine ⟨41749359032159359006937149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55665812042879145342582865 41749359032159359006937149)
              ·
                refine ⟨15656009637059759627601431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41749359032159359006937149 15656009637059759627601431)
                ·
                  refine ⟨23484014455589639441402147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15656009637059759627601431 23484014455589639441402147)
                  ·
                    refine ⟨35226021683384459162103221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23484014455589639441402147 35226021683384459162103221)
                    ·
                      refine ⟨3302439532817293046447177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35226021683384459162103221 3302439532817293046447177)
                      ·
                        rfl

theorem cell23_6431478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_6431478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431478 prefixEnd_6431478 := by exact prefixLift 6431478
  have htrace : WordTrace (prefixWord ++ tailWord_6431478) baseStart_6431478 baseEnd_6431478 := by
    simpa [prefixWord, tailWord_6431478, baseEnd_6431478] using wordTrace_append hprefix tailTrace_6431478
  have hstable : (prefixWord ++ tailWord_6431478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431478).length < 2 ^ (prefixWord ++ tailWord_6431478).sum := by decide
  have hdescent : baseEnd_6431478 < baseStart_6431478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431492 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_6431492 : Nat := 118140960795 + 6431492 * 2 ^ 59
def prefixEnd_6431492 : Nat := 4983230072969 + 3 ^ 40 * 6431492 * 2
def baseEnd_6431492 : Nat := 3302446721546455991672113

theorem tailTrace_6431492 : CollatzResearch.WordTrace tailWord_6431492 prefixEnd_6431492 3302446721546455991672113 := by
  unfold tailWord_6431492
  simp only [CollatzResearch.WordTrace]
  refine ⟨117287892207905185114856365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156383856277206913486475153 117287892207905185114856365)
  ·
    refine ⟨43982959577964444418071137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117287892207905185114856365 43982959577964444418071137)
    ·
      refine ⟨32987219683473333313553353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43982959577964444418071137 32987219683473333313553353)
      ·
        refine ⟨24740414762604999985165015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32987219683473333313553353 24740414762604999985165015)
        ·
          refine ⟨37110622143907499977747523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24740414762604999985165015 37110622143907499977747523)
          ·
            refine ⟨55665933215861249966621285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37110622143907499977747523 55665933215861249966621285)
            ·
              refine ⟨10437362477973984368741491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55665933215861249966621285 10437362477973984368741491)
              ·
                refine ⟨15656043716960976553112237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10437362477973984368741491 15656043716960976553112237)
                ·
                  refine ⟨5871016393860366207417089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15656043716960976553112237 5871016393860366207417089)
                  ·
                    refine ⟨4403262295395274655562817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5871016393860366207417089 4403262295395274655562817)
                    ·
                      refine ⟨3302446721546455991672113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403262295395274655562817 3302446721546455991672113)
                      ·
                        rfl

theorem cell23_6431492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_6431492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431492 prefixEnd_6431492 := by exact prefixLift 6431492
  have htrace : WordTrace (prefixWord ++ tailWord_6431492) baseStart_6431492 baseEnd_6431492 := by
    simpa [prefixWord, tailWord_6431492, baseEnd_6431492] using wordTrace_append hprefix tailTrace_6431492
  have hstable : (prefixWord ++ tailWord_6431492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431492).length < 2 ^ (prefixWord ++ tailWord_6431492).sum := by decide
  have hdescent : baseEnd_6431492 < baseStart_6431492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431521 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_6431521 : Nat := 118140960795 + 6431521 * 2 ^ 59
def prefixEnd_6431521 : Nat := 4983230072969 + 3 ^ 40 * 6431521 * 2
def baseEnd_6431521 : Nat := 3302461612485436378209479

theorem tailTrace_6431521 : CollatzResearch.WordTrace tailWord_6431521 prefixEnd_6431521 3302461612485436378209479 := by
  unfold tailWord_6431521
  simp only [CollatzResearch.WordTrace]
  refine ⟨234576842132705308182518417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156384561421803538788345611 234576842132705308182518417)
  ·
    refine ⟨175932631599528981136888813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234576842132705308182518417 175932631599528981136888813)
    ·
      refine ⟨65974736849823367926333305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175932631599528981136888813 65974736849823367926333305)
      ·
        refine ⟨49481052637367525944749979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65974736849823367926333305 49481052637367525944749979)
        ·
          refine ⟨74221578956051288917124969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49481052637367525944749979 74221578956051288917124969)
          ·
            refine ⟨55666184217038466687843727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74221578956051288917124969 55666184217038466687843727)
            ·
              refine ⟨83499276325557700031765591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55666184217038466687843727 83499276325557700031765591)
              ·
                refine ⟨125248914488336550047648387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83499276325557700031765591 125248914488336550047648387)
                ·
                  refine ⟨187873371732504825071472581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125248914488336550047648387 187873371732504825071472581)
                  ·
                    refine ⟨35226257199844654700901109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187873371732504825071472581 35226257199844654700901109)
                    ·
                      refine ⟨3302461612485436378209479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35226257199844654700901109 3302461612485436378209479)
                      ·
                        rfl

theorem cell23_6431521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_6431521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431521 prefixEnd_6431521 := by exact prefixLift 6431521
  have htrace : WordTrace (prefixWord ++ tailWord_6431521) baseStart_6431521 baseEnd_6431521 := by
    simpa [prefixWord, tailWord_6431521, baseEnd_6431521] using wordTrace_append hprefix tailTrace_6431521
  have hstable : (prefixWord ++ tailWord_6431521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431521).length < 2 ^ (prefixWord ++ tailWord_6431521).sum := by decide
  have hdescent : baseEnd_6431521 < baseStart_6431521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431569 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 1, 3, 2]
def baseStart_6431569 : Nat := 118140960795 + 6431569 * 2 ^ 59
def prefixEnd_6431569 : Nat := 4983230072969 + 3 ^ 40 * 6431569 * 2
def baseEnd_6431569 : Nat := 3302486259556852190409259

theorem tailTrace_6431569 : CollatzResearch.WordTrace tailWord_6431569 prefixEnd_6431569 3302486259556852190409259 := by
  unfold tailWord_6431569
  simp only [CollatzResearch.WordTrace]
  refine ⟨234578592836531412380265761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156385728557687608253510507 234578592836531412380265761)
  ·
    refine ⟨175933944627398559285199321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234578592836531412380265761 175933944627398559285199321)
    ·
      refine ⟨131950458470548919463899491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175933944627398559285199321 131950458470548919463899491)
      ·
        refine ⟨197925687705823379195849237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131950458470548919463899491 197925687705823379195849237)
        ·
          refine ⟨9277766611210470899805433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 197925687705823379195849237 9277766611210470899805433)
          ·
            refine ⟨6958324958407853174854075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9277766611210470899805433 6958324958407853174854075)
            ·
              refine ⟨10437487437611779762281113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6958324958407853174854075 10437487437611779762281113)
              ·
                refine ⟨7828115578208834821710835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10437487437611779762281113 7828115578208834821710835)
                ·
                  refine ⟨11742173367313252232566253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7828115578208834821710835 11742173367313252232566253)
                  ·
                    refine ⟨4403315012742469587212345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11742173367313252232566253 4403315012742469587212345)
                    ·
                      refine ⟨3302486259556852190409259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403315012742469587212345 3302486259556852190409259)
                      ·
                        rfl

theorem cell23_6431569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 3, 2].length) (baseStart_6431569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431569 prefixEnd_6431569 := by exact prefixLift 6431569
  have htrace : WordTrace (prefixWord ++ tailWord_6431569) baseStart_6431569 baseEnd_6431569 := by
    simpa [prefixWord, tailWord_6431569, baseEnd_6431569] using wordTrace_append hprefix tailTrace_6431569
  have hstable : (prefixWord ++ tailWord_6431569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431569).length < 2 ^ (prefixWord ++ tailWord_6431569).sum := by decide
  have hdescent : baseEnd_6431569 < baseStart_6431569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431571 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 7]
def baseStart_6431571 : Nat := 118140960795 + 6431571 * 2 ^ 59
def prefixEnd_6431571 : Nat := 4983230072969 + 3 ^ 40 * 6431571 * 2
def baseEnd_6431571 : Nat := 366943031835351242509361

theorem tailTrace_6431571 : CollatzResearch.WordTrace tailWord_6431571 prefixEnd_6431571 366943031835351242509361 := by
  unfold tailWord_6431571
  simp only [CollatzResearch.WordTrace]
  refine ⟨234578665782524166721838567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156385777188349444481225711 234578665782524166721838567)
  ·
    refine ⟨351867998673786250082757851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234578665782524166721838567 351867998673786250082757851)
    ·
      refine ⟨527801998010679375124136777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351867998673786250082757851 527801998010679375124136777)
      ·
        refine ⟨395851498508009531343102583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527801998010679375124136777 395851498508009531343102583)
        ·
          refine ⟨593777247762014297014653875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395851498508009531343102583 593777247762014297014653875)
          ·
            refine ⟨890665871643021445521980813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593777247762014297014653875 890665871643021445521980813)
            ·
              refine ⟨333999701866133042070742805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 890665871643021445521980813 333999701866133042070742805)
              ·
                refine ⟨15656236024974986347066069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 333999701866133042070742805 15656236024974986347066069)
                ·
                  refine ⟨366943031835351242509361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15656236024974986347066069 366943031835351242509361)
                  ·
                    rfl

theorem cell23_6431571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 7].length) (baseStart_6431571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431571 prefixEnd_6431571 := by exact prefixLift 6431571
  have htrace : WordTrace (prefixWord ++ tailWord_6431571) baseStart_6431571 baseEnd_6431571 := by
    simpa [prefixWord, tailWord_6431571, baseEnd_6431571] using wordTrace_append hprefix tailTrace_6431571
  have hstable : (prefixWord ++ tailWord_6431571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431571).length < 2 ^ (prefixWord ++ tailWord_6431571).sum := by decide
  have hdescent : baseEnd_6431571 < baseStart_6431571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431586 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_6431586 : Nat := 118140960795 + 6431586 * 2 ^ 59
def prefixEnd_6431586 : Nat := 4983230072969 + 3 ^ 40 * 6431586 * 2
def baseEnd_6431586 : Nat := 3302494988727978623896681

theorem tailTrace_6431586 : CollatzResearch.WordTrace tailWord_6431586 prefixEnd_6431586 3302494988727978623896681 := by
  unfold tailWord_6431586
  simp only [CollatzResearch.WordTrace]
  refine ⟨58644803219367456070908653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156386141918313216189089741 58644803219367456070908653)
  ·
    refine ⟨21991801207262796026590745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58644803219367456070908653 21991801207262796026590745)
    ·
      refine ⟨16493850905447097019943059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21991801207262796026590745 16493850905447097019943059)
      ·
        refine ⟨24740776358170645529914589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16493850905447097019943059 24740776358170645529914589)
        ·
          refine ⟨9277791134313992073717971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24740776358170645529914589 9277791134313992073717971)
          ·
            refine ⟨13916686701470988110576957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9277791134313992073717971 13916686701470988110576957)
            ·
              refine ⟨5218757513051620541466359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13916686701470988110576957 5218757513051620541466359)
              ·
                refine ⟨7828136269577430812199539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5218757513051620541466359 7828136269577430812199539)
                ·
                  refine ⟨11742204404366146218299309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7828136269577430812199539 11742204404366146218299309)
                  ·
                    refine ⟨4403326651637304831862241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11742204404366146218299309 4403326651637304831862241)
                    ·
                      refine ⟨3302494988727978623896681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403326651637304831862241 3302494988727978623896681)
                      ·
                        rfl

theorem cell23_6431586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_6431586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431586 prefixEnd_6431586 := by exact prefixLift 6431586
  have htrace : WordTrace (prefixWord ++ tailWord_6431586) baseStart_6431586 baseEnd_6431586 := by
    simpa [prefixWord, tailWord_6431586, baseEnd_6431586] using wordTrace_append hprefix tailTrace_6431586
  have hstable : (prefixWord ++ tailWord_6431586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431586).length < 2 ^ (prefixWord ++ tailWord_6431586).sum := by decide
  have hdescent : baseEnd_6431586 < baseStart_6431586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431728 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 4]
def baseStart_6431728 : Nat := 118140960795 + 6431728 * 2 ^ 59
def prefixEnd_6431728 : Nat := 4983230072969 + 3 ^ 40 * 6431728 * 2
def baseEnd_6431728 : Nat := 3302567902980917068321027

theorem tailTrace_6431728 : CollatzResearch.WordTrace tailWord_6431728 prefixEnd_6431728 3302567902980917068321027 := by
  unfold tailWord_6431728
  simp only [CollatzResearch.WordTrace]
  refine ⟨117292196021477691267651919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156389594695303588356869225 117292196021477691267651919)
  ·
    refine ⟨175938294032216536901477879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117292196021477691267651919 175938294032216536901477879)
    ·
      refine ⟨263907441048324805352216819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175938294032216536901477879 263907441048324805352216819)
      ·
        refine ⟨395861161572487208028325229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263907441048324805352216819 395861161572487208028325229)
        ·
          refine ⟨148447935589682703010621961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395861161572487208028325229 148447935589682703010621961)
          ·
            refine ⟨111335951692262027257966471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148447935589682703010621961 111335951692262027257966471)
            ·
              refine ⟨167003927538393040886949707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111335951692262027257966471 167003927538393040886949707)
              ·
                refine ⟨250505891307589561330424561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167003927538393040886949707 250505891307589561330424561)
                ·
                  refine ⟨187879418480692170997818421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250505891307589561330424561 187879418480692170997818421)
                  ·
                    refine ⟨17613695482564891031045477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 187879418480692170997818421 17613695482564891031045477)
                    ·
                      refine ⟨3302567902980917068321027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17613695482564891031045477 3302567902980917068321027)
                      ·
                        rfl

theorem cell23_6431728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_6431728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431728 prefixEnd_6431728 := by exact prefixLift 6431728
  have htrace : WordTrace (prefixWord ++ tailWord_6431728) baseStart_6431728 baseEnd_6431728 := by
    simpa [prefixWord, tailWord_6431728, baseEnd_6431728] using wordTrace_append hprefix tailTrace_6431728
  have hstable : (prefixWord ++ tailWord_6431728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431728).length < 2 ^ (prefixWord ++ tailWord_6431728).sum := by decide
  have hdescent : baseEnd_6431728 < baseStart_6431728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431738 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_6431738 : Nat := 118140960795 + 6431738 * 2 ^ 59
def prefixEnd_6431738 : Nat := 4983230072969 + 3 ^ 40 * 6431738 * 2
def baseEnd_6431738 : Nat := 1100857679262487343065327

theorem tailTrace_6431738 : CollatzResearch.WordTrace tailWord_6431738 prefixEnd_6431738 1100857679262487343065327 := by
  unfold tailWord_6431738
  simp only [CollatzResearch.WordTrace]
  refine ⟨58646189193229788560791967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156389837848612769495445245 58646189193229788560791967)
  ·
    refine ⟨87969283789844682841187951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58646189193229788560791967 87969283789844682841187951)
    ·
      refine ⟨131953925684767024261781927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87969283789844682841187951 131953925684767024261781927)
      ·
        refine ⟨197930888527150536392672891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131953925684767024261781927 197930888527150536392672891)
        ·
          refine ⟨296896332790725804589009337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197930888527150536392672891 296896332790725804589009337)
          ·
            refine ⟨222672249593044353441757003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296896332790725804589009337 222672249593044353441757003)
            ·
              refine ⟨334008374389566530162635505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222672249593044353441757003 334008374389566530162635505)
              ·
                refine ⟨250506280792174897621976629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334008374389566530162635505 250506280792174897621976629)
                ·
                  refine ⟨23484963824266396652060309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250506280792174897621976629 23484963824266396652060309)
                  ·
                    refine ⟨1100857679262487343065327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23484963824266396652060309 1100857679262487343065327)
                    ·
                      rfl

theorem cell23_6431738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_6431738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431738 prefixEnd_6431738 := by exact prefixLift 6431738
  have htrace : WordTrace (prefixWord ++ tailWord_6431738) baseStart_6431738 baseEnd_6431738 := by
    simpa [prefixWord, tailWord_6431738, baseEnd_6431738] using wordTrace_append hprefix tailTrace_6431738
  have hstable : (prefixWord ++ tailWord_6431738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431738).length < 2 ^ (prefixWord ++ tailWord_6431738).sum := by decide
  have hdescent : baseEnd_6431738 < baseStart_6431738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431755 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 1, 6]
def baseStart_6431755 : Nat := 118140960795 + 6431755 * 2 ^ 59
def prefixEnd_6431755 : Nat := 4983230072969 + 3 ^ 40 * 6431755 * 2
def baseEnd_6431755 : Nat := 1100860588986196154227801

theorem tailTrace_6431755 : CollatzResearch.WordTrace tailWord_6431755 prefixEnd_6431755 1100860588986196154227801 := by
  unfold tailWord_6431755
  simp only [CollatzResearch.WordTrace]
  refine ⟨234585376813857566146536719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156390251209238377431024479 234585376813857566146536719)
  ·
    refine ⟨351878065220786349219805079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234585376813857566146536719 351878065220786349219805079)
    ·
      refine ⟨527817097831179523829707619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351878065220786349219805079 527817097831179523829707619)
      ·
        refine ⟨791725646746769285744561429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527817097831179523829707619 791725646746769285744561429)
        ·
          refine ⟨37112139691254810269276317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 791725646746769285744561429 37112139691254810269276317)
          ·
            refine ⟨13917052384220553850978619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37112139691254810269276317 13917052384220553850978619)
            ·
              refine ⟨20875578576330830776467929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13917052384220553850978619 20875578576330830776467929)
              ·
                refine ⟨15656683932248123082350947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20875578576330830776467929 15656683932248123082350947)
                ·
                  refine ⟨23485025898372184623526421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15656683932248123082350947 23485025898372184623526421)
                  ·
                    refine ⟨1100860588986196154227801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23485025898372184623526421 1100860588986196154227801)
                    ·
                      rfl

theorem cell23_6431755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 6].length) (baseStart_6431755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431755 prefixEnd_6431755 := by exact prefixLift 6431755
  have htrace : WordTrace (prefixWord ++ tailWord_6431755) baseStart_6431755 baseEnd_6431755 := by
    simpa [prefixWord, tailWord_6431755, baseEnd_6431755] using wordTrace_append hprefix tailTrace_6431755
  have hstable : (prefixWord ++ tailWord_6431755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431755).length < 2 ^ (prefixWord ++ tailWord_6431755).sum := by decide
  have hdescent : baseEnd_6431755 < baseStart_6431755 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431768 : List Nat := [2, 1, 2, 3, 2, 13]
def baseStart_6431768 : Nat := 118140960795 + 6431768 * 2 ^ 59
def prefixEnd_6431768 : Nat := 4983230072969 + 3 ^ 40 * 6431768 * 2
def baseEnd_6431768 : Nat := 13590898939123855604201

theorem tailTrace_6431768 : CollatzResearch.WordTrace tailWord_6431768 prefixEnd_6431768 13590898939123855604201 := by
  unfold tailWord_6431768
  simp only [CollatzResearch.WordTrace]
  refine ⟨117292925481405234683379979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156390567308540312911173305 117292925481405234683379979)
  ·
    refine ⟨175939388222107852025069969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117292925481405234683379979 175939388222107852025069969)
    ·
      refine ⟨131954541166580889018802477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175939388222107852025069969 131954541166580889018802477)
      ·
        refine ⟨49482952937467833382050929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131954541166580889018802477 49482952937467833382050929)
        ·
          refine ⟨37112214703100875036538197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49482952937467833382050929 37112214703100875036538197)
          ·
            refine ⟨13590898939123855604201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 37112214703100875036538197 13590898939123855604201)
            ·
              rfl

theorem cell23_6431768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 13].length) (baseStart_6431768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431768 prefixEnd_6431768 := by exact prefixLift 6431768
  have htrace : WordTrace (prefixWord ++ tailWord_6431768) baseStart_6431768 baseEnd_6431768 := by
    simpa [prefixWord, tailWord_6431768, baseEnd_6431768] using wordTrace_append hprefix tailTrace_6431768
  have hstable : (prefixWord ++ tailWord_6431768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431768).length < 2 ^ (prefixWord ++ tailWord_6431768).sum := by decide
  have hdescent : baseEnd_6431768 < baseStart_6431768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431796 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_6431796 : Nat := 118140960795 + 6431796 * 2 ^ 59
def prefixEnd_6431796 : Nat := 4983230072969 + 3 ^ 40 * 6431796 * 2
def baseEnd_6431796 : Nat := 3302602819665422802270715

theorem tailTrace_6431796 : CollatzResearch.WordTrace tailWord_6431796 prefixEnd_6431796 3302602819665422802270715 := by
  unfold tailWord_6431796
  simp only [CollatzResearch.WordTrace]
  refine ⟨117293436103354515074389621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156391248137806020099186161 117293436103354515074389621)
  ·
    refine ⟨10996259634689485788224027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117293436103354515074389621 10996259634689485788224027)
    ·
      refine ⟨16494389452034228682336041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10996259634689485788224027 16494389452034228682336041)
      ·
        refine ⟨12370792089025671511752031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16494389452034228682336041 12370792089025671511752031)
        ·
          refine ⟨18556188133538507267628047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12370792089025671511752031 18556188133538507267628047)
          ·
            refine ⟨27834282200307760901442071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18556188133538507267628047 27834282200307760901442071)
            ·
              refine ⟨41751423300461641352163107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27834282200307760901442071 41751423300461641352163107)
              ·
                refine ⟨62627134950692462028244661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41751423300461641352163107 62627134950692462028244661)
                ·
                  refine ⟨5871293901627418315147937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62627134950692462028244661 5871293901627418315147937)
                  ·
                    refine ⟨4403470426220563736360953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5871293901627418315147937 4403470426220563736360953)
                    ·
                      refine ⟨3302602819665422802270715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403470426220563736360953 3302602819665422802270715)
                      ·
                        rfl

theorem cell23_6431796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_6431796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431796 prefixEnd_6431796 := by exact prefixLift 6431796
  have htrace : WordTrace (prefixWord ++ tailWord_6431796) baseStart_6431796 baseEnd_6431796 := by
    simpa [prefixWord, tailWord_6431796, baseEnd_6431796] using wordTrace_append hprefix tailTrace_6431796
  have hstable : (prefixWord ++ tailWord_6431796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431796).length < 2 ^ (prefixWord ++ tailWord_6431796).sum := by decide
  have hdescent : baseEnd_6431796 < baseStart_6431796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431830 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_6431830 : Nat := 118140960795 + 6431830 * 2 ^ 59
def prefixEnd_6431830 : Nat := 4983230072969 + 3 ^ 40 * 6431830 * 2
def baseEnd_6431830 : Nat := 3302620278007675669245559

theorem tailTrace_6431830 : CollatzResearch.WordTrace tailWord_6431830 prefixEnd_6431830 3302620278007675669245559 := by
  unfold tailWord_6431830
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661757018036615872219809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156392074859057235970344629 14661757018036615872219809)
  ·
    refine ⟨10996317763527461904164857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14661757018036615872219809 10996317763527461904164857)
    ·
      refine ⟨8247238322645596428123643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10996317763527461904164857 8247238322645596428123643)
      ·
        refine ⟨12370857483968394642185465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8247238322645596428123643 12370857483968394642185465)
        ·
          refine ⟨9278143112976295981639099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12370857483968394642185465 9278143112976295981639099)
          ·
            refine ⟨13917214669464443972458649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9278143112976295981639099 13917214669464443972458649)
            ·
              refine ⟨10437911002098332979343987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13917214669464443972458649 10437911002098332979343987)
              ·
                refine ⟨15656866503147499469015981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10437911002098332979343987 15656866503147499469015981)
                ·
                  refine ⟨5871324938680312300880993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15656866503147499469015981 5871324938680312300880993)
                  ·
                    refine ⟨4403493704010234225660745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5871324938680312300880993 4403493704010234225660745)
                    ·
                      refine ⟨3302620278007675669245559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403493704010234225660745 3302620278007675669245559)
                      ·
                        rfl

theorem cell23_6431830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_6431830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431830 prefixEnd_6431830 := by exact prefixLift 6431830
  have htrace : WordTrace (prefixWord ++ tailWord_6431830) baseStart_6431830 baseEnd_6431830 := by
    simpa [prefixWord, tailWord_6431830, baseEnd_6431830] using wordTrace_append hprefix tailTrace_6431830
  have hstable : (prefixWord ++ tailWord_6431830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431830).length < 2 ^ (prefixWord ++ tailWord_6431830).sum := by decide
  have hdescent : baseEnd_6431830 < baseStart_6431830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431845 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 2, 6]
def baseStart_6431845 : Nat := 118140960795 + 6431845 * 2 ^ 59
def prefixEnd_6431845 : Nat := 4983230072969 + 3 ^ 40 * 6431845 * 2
def baseEnd_6431845 : Nat := 1100875993405831036852663

theorem tailTrace_6431845 : CollatzResearch.WordTrace tailWord_6431845 prefixEnd_6431845 1100875993405831036852663 := by
  unfold tailWord_6431845
  simp only [CollatzResearch.WordTrace]
  refine ⟨234588659383531511517312989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156392439589021007678208659 234588659383531511517312989)
  ·
    refine ⟨87970747268824316818992371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234588659383531511517312989 87970747268824316818992371)
    ·
      refine ⟨131956120903236475228488557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87970747268824316818992371 131956120903236475228488557)
      ·
        refine ⟨49483545338713678210683209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131956120903236475228488557 49483545338713678210683209)
        ·
          refine ⟨37112659004035258658012407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49483545338713678210683209 37112659004035258658012407)
          ·
            refine ⟨55668988506052887987018611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37112659004035258658012407 55668988506052887987018611)
            ·
              refine ⟨83503482759079331980527917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55668988506052887987018611 83503482759079331980527917)
              ·
                refine ⟨31313806034654749492697969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83503482759079331980527917 31313806034654749492697969)
                ·
                  refine ⟨23485354525991062119523477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31313806034654749492697969 23485354525991062119523477)
                  ·
                    refine ⟨1100875993405831036852663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23485354525991062119523477 1100875993405831036852663)
                    ·
                      rfl

theorem cell23_6431845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_6431845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431845 prefixEnd_6431845 := by exact prefixLift 6431845
  have htrace : WordTrace (prefixWord ++ tailWord_6431845) baseStart_6431845 baseEnd_6431845 := by
    simpa [prefixWord, tailWord_6431845, baseEnd_6431845] using wordTrace_append hprefix tailTrace_6431845
  have hstable : (prefixWord ++ tailWord_6431845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431845).length < 2 ^ (prefixWord ++ tailWord_6431845).sum := by decide
  have hdescent : baseEnd_6431845 < baseStart_6431845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431855 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 5]
def baseStart_6431855 : Nat := 118140960795 + 6431855 * 2 ^ 59
def prefixEnd_6431855 : Nat := 4983230072969 + 3 ^ 40 * 6431855 * 2
def baseEnd_6431855 : Nat := 3302633115024038071432943

theorem tailTrace_6431855 : CollatzResearch.WordTrace tailWord_6431855 prefixEnd_6431855 3302633115024038071432943 := by
  unfold tailWord_6431855
  simp only [CollatzResearch.WordTrace]
  refine ⟨234589024113495283225177019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156392682742330188816784679 234589024113495283225177019)
  ·
    refine ⟨351883536170242924837765529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234589024113495283225177019 351883536170242924837765529)
    ·
      refine ⟨263912652127682193628324147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351883536170242924837765529 263912652127682193628324147)
      ·
        refine ⟨395868978191523290442486221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263912652127682193628324147 395868978191523290442486221)
        ·
          refine ⟨148450866821821233915932333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395868978191523290442486221 148450866821821233915932333)
          ·
            refine ⟨55669075058182962718474625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148450866821821233915932333 55669075058182962718474625)
            ·
              refine ⟨41751806293637222038855969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55669075058182962718474625 41751806293637222038855969)
              ·
                refine ⟨31313854720227916529141977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41751806293637222038855969 31313854720227916529141977)
                ·
                  refine ⟨23485391040170937396856483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31313854720227916529141977 23485391040170937396856483)
                  ·
                    refine ⟨35228086560256406095284725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23485391040170937396856483 35228086560256406095284725)
                    ·
                      refine ⟨3302633115024038071432943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35228086560256406095284725 3302633115024038071432943)
                      ·
                        rfl

theorem cell23_6431855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_6431855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431855 prefixEnd_6431855 := by exact prefixLift 6431855
  have htrace : WordTrace (prefixWord ++ tailWord_6431855) baseStart_6431855 baseEnd_6431855 := by
    simpa [prefixWord, tailWord_6431855, baseEnd_6431855] using wordTrace_append hprefix tailTrace_6431855
  have hstable : (prefixWord ++ tailWord_6431855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431855).length < 2 ^ (prefixWord ++ tailWord_6431855).sum := by decide
  have hdescent : baseEnd_6431855 < baseStart_6431855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431869 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 6, 2, 2]
def baseStart_6431869 : Nat := 118140960795 + 6431869 * 2 ^ 59
def prefixEnd_6431869 : Nat := 4983230072969 + 3 ^ 40 * 6431869 * 2
def baseEnd_6431869 : Nat := 3302640303753201016657879

theorem tailTrace_6431869 : CollatzResearch.WordTrace tailWord_6431869 prefixEnd_6431869 3302640303753201016657879 := by
  unfold tailWord_6431869
  simp only [CollatzResearch.WordTrace]
  refine ⟨234589534735444563616186661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156393023156963042410791107 234589534735444563616186661)
  ·
    refine ⟨43985537762895855678034999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234589534735444563616186661 43985537762895855678034999)
    ·
      refine ⟨65978306644343783517052499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43985537762895855678034999 65978306644343783517052499)
      ·
        refine ⟨98967459966515675275578749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65978306644343783517052499 98967459966515675275578749)
        ·
          refine ⟨37112797487443378228342031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98967459966515675275578749 37112797487443378228342031)
          ·
            refine ⟨55669196231165067342513047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37112797487443378228342031 55669196231165067342513047)
            ·
              refine ⟨83503794346747601013769571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55669196231165067342513047 83503794346747601013769571)
              ·
                refine ⟨125255691520121401520654357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83503794346747601013769571 125255691520121401520654357)
                ·
                  refine ⟨5871360540005690696280673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125255691520121401520654357 5871360540005690696280673)
                  ·
                    refine ⟨4403520405004268022210505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5871360540005690696280673 4403520405004268022210505)
                    ·
                      refine ⟨3302640303753201016657879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403520405004268022210505 3302640303753201016657879)
                      ·
                        rfl

theorem cell23_6431869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_6431869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431869 prefixEnd_6431869 := by exact prefixLift 6431869
  have htrace : WordTrace (prefixWord ++ tailWord_6431869) baseStart_6431869 baseEnd_6431869 := by
    simpa [prefixWord, tailWord_6431869, baseEnd_6431869] using wordTrace_append hprefix tailTrace_6431869
  have hstable : (prefixWord ++ tailWord_6431869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431869).length < 2 ^ (prefixWord ++ tailWord_6431869).sum := by decide
  have hdescent : baseEnd_6431869 < baseStart_6431869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431886 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2]
def baseStart_6431886 : Nat := 118140960795 + 6431886 * 2 ^ 59
def prefixEnd_6431886 : Nat := 4983230072969 + 3 ^ 40 * 6431886 * 2
def baseEnd_6431886 : Nat := 3302649032924327450145301

theorem tailTrace_6431886 : CollatzResearch.WordTrace tailWord_6431886 prefixEnd_6431886 3302649032924327450145301 := by
  unfold tailWord_6431886
  simp only [CollatzResearch.WordTrace]
  refine ⟨29323769347047871939944439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156393436517588650346370341 29323769347047871939944439)
  ·
    refine ⟨43985654020571807909916659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29323769347047871939944439 43985654020571807909916659)
    ·
      refine ⟨65978481030857711864874989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43985654020571807909916659 65978481030857711864874989)
      ·
        refine ⟨24741930386571641949328121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65978481030857711864874989 24741930386571641949328121)
        ·
          refine ⟨18556447789928731461996091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24741930386571641949328121 18556447789928731461996091)
          ·
            refine ⟨27834671684893097192994137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18556447789928731461996091 27834671684893097192994137)
            ·
              refine ⟨20876003763669822894745603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27834671684893097192994137 20876003763669822894745603)
              ·
                refine ⟨31314005645504734342118405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20876003763669822894745603 31314005645504734342118405)
                ·
                  refine ⟨5871376058532137689147201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31314005645504734342118405 5871376058532137689147201)
                  ·
                    refine ⟨4403532043899103266860401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5871376058532137689147201 4403532043899103266860401)
                    ·
                      refine ⟨3302649032924327450145301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403532043899103266860401 3302649032924327450145301)
                      ·
                        rfl

theorem cell23_6431886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_6431886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431886 prefixEnd_6431886 := by exact prefixLift 6431886
  have htrace : WordTrace (prefixWord ++ tailWord_6431886) baseStart_6431886 baseEnd_6431886 := by
    simpa [prefixWord, tailWord_6431886, baseEnd_6431886] using wordTrace_append hprefix tailTrace_6431886
  have hstable : (prefixWord ++ tailWord_6431886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431886).length < 2 ^ (prefixWord ++ tailWord_6431886).sum := by decide
  have hdescent : baseEnd_6431886 < baseStart_6431886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431903 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6431903 : Nat := 118140960795 + 6431903 * 2 ^ 59
def prefixEnd_6431903 : Nat := 4983230072969 + 3 ^ 40 * 6431903 * 2
def baseEnd_6431903 : Nat := 3302657762095453883632723

theorem tailTrace_6431903 : CollatzResearch.WordTrace tailWord_6431903 prefixEnd_6431903 3302657762095453883632723 := by
  unfold tailWord_6431903
  simp only [CollatzResearch.WordTrace]
  refine ⟨234590774817321387422924363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156393849878214258281949575 234590774817321387422924363)
  ·
    refine ⟨351886162225982081134386545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234590774817321387422924363 351886162225982081134386545)
    ·
      refine ⟨263914621669486560850789909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351886162225982081134386545 263914621669486560850789909)
      ·
        refine ⟨12370997890757182539880777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 263914621669486560850789909 12370997890757182539880777)
        ·
          refine ⟨9278248418067886904910583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12370997890757182539880777 9278248418067886904910583)
          ·
            refine ⟨13917372627101830357365875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9278248418067886904910583 13917372627101830357365875)
            ·
              refine ⟨20876058940652745536048813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13917372627101830357365875 20876058940652745536048813)
              ·
                refine ⟨7828522102744779576018305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20876058940652745536048813 7828522102744779576018305)
                ·
                  refine ⟨5871391577058584682013729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7828522102744779576018305 5871391577058584682013729)
                  ·
                    refine ⟨4403543682793938511510297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5871391577058584682013729 4403543682793938511510297)
                    ·
                      refine ⟨3302657762095453883632723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403543682793938511510297 3302657762095453883632723)
                      ·
                        rfl

theorem cell23_6431903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6431903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431903 prefixEnd_6431903 := by exact prefixLift 6431903
  have htrace : WordTrace (prefixWord ++ tailWord_6431903) baseStart_6431903 baseEnd_6431903 := by
    simpa [prefixWord, tailWord_6431903, baseEnd_6431903] using wordTrace_append hprefix tailTrace_6431903
  have hstable : (prefixWord ++ tailWord_6431903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431903).length < 2 ^ (prefixWord ++ tailWord_6431903).sum := by decide
  have hdescent : baseEnd_6431903 < baseStart_6431903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431922 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_6431922 : Nat := 118140960795 + 6431922 * 2 ^ 59
def prefixEnd_6431922 : Nat := 4983230072969 + 3 ^ 40 * 6431922 * 2
def baseEnd_6431922 : Nat := 1100889172742629769765045

theorem tailTrace_6431922 : CollatzResearch.WordTrace tailWord_6431922 prefixEnd_6431922 1100889172742629769765045 := by
  unfold tailWord_6431922
  simp only [CollatzResearch.WordTrace]
  refine ⟨58647866951063138416966505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156394311869501702445244013 58647866951063138416966505)
  ·
    refine ⟨43985900213297353812724879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58647866951063138416966505 43985900213297353812724879)
    ·
      refine ⟨65978850319946030719087319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43985900213297353812724879 65978850319946030719087319)
      ·
        refine ⟨98968275479919046078630979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65978850319946030719087319 98968275479919046078630979)
        ·
          refine ⟨148452413219878569117946469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98968275479919046078630979 148452413219878569117946469)
          ·
            refine ⟨27834827478727231709614963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148452413219878569117946469 27834827478727231709614963)
            ·
              refine ⟨41752241218090847564422445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27834827478727231709614963 41752241218090847564422445)
              ·
                refine ⟨15657090456784067836658417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41752241218090847564422445 15657090456784067836658417)
                ·
                  refine ⟨11742817842588050877493813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15657090456784067836658417 11742817842588050877493813)
                  ·
                    refine ⟨1100889172742629769765045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11742817842588050877493813 1100889172742629769765045)
                    ·
                      rfl

theorem cell23_6431922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_6431922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431922 prefixEnd_6431922 := by exact prefixLift 6431922
  have htrace : WordTrace (prefixWord ++ tailWord_6431922) baseStart_6431922 baseEnd_6431922 := by
    simpa [prefixWord, tailWord_6431922, baseEnd_6431922] using wordTrace_append hprefix tailTrace_6431922
  have hstable : (prefixWord ++ tailWord_6431922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431922).length < 2 ^ (prefixWord ++ tailWord_6431922).sum := by decide
  have hdescent : baseEnd_6431922 < baseStart_6431922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431932 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_6431932 : Nat := 118140960795 + 6431932 * 2 ^ 59
def prefixEnd_6431932 : Nat := 4983230072969 + 3 ^ 40 * 6431932 * 2
def baseEnd_6431932 : Nat := 3302672653034434270170089

theorem tailTrace_6431932 : CollatzResearch.WordTrace tailWord_6431932 prefixEnd_6431932 3302672653034434270170089 := by
  unfold tailWord_6431932
  simp only [CollatzResearch.WordTrace]
  refine ⟨117295916267108162687865025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156394555022810883583820033 117295916267108162687865025)
  ·
    refine ⟨87971937200331122015898769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117295916267108162687865025 87971937200331122015898769)
    ·
      refine ⟨65978952900248341511924077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87971937200331122015898769 65978952900248341511924077)
      ·
        refine ⟨24742107337593128066971529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65978952900248341511924077 24742107337593128066971529)
        ·
          refine ⟨18556580503194846050228647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24742107337593128066971529 18556580503194846050228647)
          ·
            refine ⟨27834870754792269075342971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18556580503194846050228647 27834870754792269075342971)
            ·
              refine ⟨41752306132188403613014457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27834870754792269075342971 41752306132188403613014457)
              ·
                refine ⟨31314229599141302709760843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41752306132188403613014457 31314229599141302709760843)
                ·
                  refine ⟨46971344398711954064641265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31314229599141302709760843 46971344398711954064641265)
                  ·
                    refine ⟨35228508299033965548480949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46971344398711954064641265 35228508299033965548480949)
                    ·
                      refine ⟨3302672653034434270170089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35228508299033965548480949 3302672653034434270170089)
                      ·
                        rfl

theorem cell23_6431932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_6431932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431932 prefixEnd_6431932 := by exact prefixLift 6431932
  have htrace : WordTrace (prefixWord ++ tailWord_6431932) baseStart_6431932 baseEnd_6431932 := by
    simpa [prefixWord, tailWord_6431932, baseEnd_6431932] using wordTrace_append hprefix tailTrace_6431932
  have hstable : (prefixWord ++ tailWord_6431932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431932).length < 2 ^ (prefixWord ++ tailWord_6431932).sum := by decide
  have hdescent : baseEnd_6431932 < baseStart_6431932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431955 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 6]
def baseStart_6431955 : Nat := 118140960795 + 6431955 * 2 ^ 59
def prefixEnd_6431955 : Nat := 4983230072969 + 3 ^ 40 * 6431955 * 2
def baseEnd_6431955 : Nat := 3302684463089487680182483

theorem tailTrace_6431955 : CollatzResearch.WordTrace tailWord_6431955 prefixEnd_6431955 3302684463089487680182483 := by
  unfold tailWord_6431955
  simp only [CollatzResearch.WordTrace]
  refine ⟨234592671413133000303817319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156395114275422000202544879 234592671413133000303817319)
  ·
    refine ⟨351889007119699500455725979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234592671413133000303817319 351889007119699500455725979)
    ·
      refine ⟨527833510679549250683588969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351889007119699500455725979 527833510679549250683588969)
      ·
        refine ⟨395875133009661938012691727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527833510679549250683588969 395875133009661938012691727)
        ·
          refine ⟨593812699514492907019037591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395875133009661938012691727 593812699514492907019037591)
          ·
            refine ⟨890719049271739360528556387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593812699514492907019037591 890719049271739360528556387)
            ·
              refine ⟨1336078573907609040792834581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890719049271739360528556387 1336078573907609040792834581)
              ·
                refine ⟨62628683151919173787164121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1336078573907609040792834581 62628683151919173787164121)
                ·
                  refine ⟨46971512363939380340373091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62628683151919173787164121 46971512363939380340373091)
                  ·
                    refine ⟨70457268545909070510559637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46971512363939380340373091 70457268545909070510559637)
                    ·
                      refine ⟨3302684463089487680182483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70457268545909070510559637 3302684463089487680182483)
                      ·
                        rfl

theorem cell23_6431955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_6431955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431955 prefixEnd_6431955 := by exact prefixLift 6431955
  have htrace : WordTrace (prefixWord ++ tailWord_6431955) baseStart_6431955 baseEnd_6431955 := by
    simpa [prefixWord, tailWord_6431955, baseEnd_6431955] using wordTrace_append hprefix tailTrace_6431955
  have hstable : (prefixWord ++ tailWord_6431955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431955).length < 2 ^ (prefixWord ++ tailWord_6431955).sum := by decide
  have hdescent : baseEnd_6431955 < baseStart_6431955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431962 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3]
def baseStart_6431962 : Nat := 118140960795 + 6431962 * 2 ^ 59
def prefixEnd_6431962 : Nat := 4983230072969 + 3 ^ 40 * 6431962 * 2
def baseEnd_6431962 : Nat := 3302688057454069152794951

theorem tailTrace_6431962 : CollatzResearch.WordTrace tailWord_6431962 prefixEnd_6431962 3302688057454069152794951 := by
  unfold tailWord_6431962
  simp only [CollatzResearch.WordTrace]
  refine ⟨58648231681026910124830535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156395284482738426999548093 58648231681026910124830535)
  ·
    refine ⟨87972347521540365187245803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58648231681026910124830535 87972347521540365187245803)
    ·
      refine ⟨131958521282310547780868705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87972347521540365187245803 131958521282310547780868705)
      ·
        refine ⟨98968890961732910835651529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131958521282310547780868705 98968890961732910835651529)
        ·
          refine ⟨74226668221299683126738647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98968890961732910835651529 74226668221299683126738647)
          ·
            refine ⟨111340002331949524690107971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74226668221299683126738647 111340002331949524690107971)
            ·
              refine ⟨167010003497924287035161957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111340002331949524690107971 167010003497924287035161957)
              ·
                refine ⟨31314375655860803819092867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167010003497924287035161957 31314375655860803819092867)
                ·
                  refine ⟨46971563483791205728639301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31314375655860803819092867 46971563483791205728639301)
                  ·
                    refine ⟨8807168153210851074119869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46971563483791205728639301 8807168153210851074119869)
                    ·
                      refine ⟨3302688057454069152794951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8807168153210851074119869 3302688057454069152794951)
                      ·
                        rfl

theorem cell23_6431962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_6431962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431962 prefixEnd_6431962 := by exact prefixLift 6431962
  have htrace : WordTrace (prefixWord ++ tailWord_6431962) baseStart_6431962 baseEnd_6431962 := by
    simpa [prefixWord, tailWord_6431962, baseEnd_6431962] using wordTrace_append hprefix tailTrace_6431962
  have hstable : (prefixWord ++ tailWord_6431962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431962).length < 2 ^ (prefixWord ++ tailWord_6431962).sum := by decide
  have hdescent : baseEnd_6431962 < baseStart_6431962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431969 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 3, 4]
def baseStart_6431969 : Nat := 118140960795 + 6431969 * 2 ^ 59
def prefixEnd_6431969 : Nat := 4983230072969 + 3 ^ 40 * 6431969 * 2
def baseEnd_6431969 : Nat := 1100897217272883541802473

theorem tailTrace_6431969 : CollatzResearch.WordTrace tailWord_6431969 prefixEnd_6431969 1100897217272883541802473 := by
  unfold tailWord_6431969
  simp only [CollatzResearch.WordTrace]
  refine ⟨234593182035082280694826961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156395454690054853796551307 234593182035082280694826961)
  ·
    refine ⟨175944886526311710521120221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234593182035082280694826961 175944886526311710521120221)
    ·
      refine ⟨65979332447366891445420083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175944886526311710521120221 65979332447366891445420083)
      ·
        refine ⟨98968998671050337168130125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65979332447366891445420083 98968998671050337168130125)
        ·
          refine ⟨37113374501643876438048797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98968998671050337168130125 37113374501643876438048797)
          ·
            refine ⟨13917515438116453664268299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37113374501643876438048797 13917515438116453664268299)
            ·
              refine ⟨20876273157174680496402449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13917515438116453664268299 20876273157174680496402449)
              ·
                refine ⟨15657204867881010372301837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20876273157174680496402449 15657204867881010372301837)
                ·
                  refine ⟨5871451825455378889613189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15657204867881010372301837 5871451825455378889613189)
                  ·
                    refine ⟨1100897217272883541802473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5871451825455378889613189 1100897217272883541802473)
                    ·
                      rfl

theorem cell23_6431969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_6431969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431969 prefixEnd_6431969 := by exact prefixLift 6431969
  have htrace : WordTrace (prefixWord ++ tailWord_6431969) baseStart_6431969 baseEnd_6431969 := by
    simpa [prefixWord, tailWord_6431969, baseEnd_6431969] using wordTrace_append hprefix tailTrace_6431969
  have hstable : (prefixWord ++ tailWord_6431969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431969).length < 2 ^ (prefixWord ++ tailWord_6431969).sum := by decide
  have hdescent : baseEnd_6431969 < baseStart_6431969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431979 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 3]
def baseStart_6431979 : Nat := 118140960795 + 6431979 * 2 ^ 59
def prefixEnd_6431979 : Nat := 4983230072969 + 3 ^ 40 * 6431979 * 2
def baseEnd_6431979 : Nat := 3302696786625195586282373

theorem tailTrace_6431979 : CollatzResearch.WordTrace tailWord_6431979 prefixEnd_6431979 3302696786625195586282373 := by
  unfold tailWord_6431979
  simp only [CollatzResearch.WordTrace]
  refine ⟨234593546765046052402690991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156395697843364034935127327 234593546765046052402690991)
  ·
    refine ⟨351890320147569078604036487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234593546765046052402690991 351890320147569078604036487)
    ·
      refine ⟨527835480221353617906054731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351890320147569078604036487 527835480221353617906054731)
      ·
        refine ⟨791753220332030426859082097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527835480221353617906054731 791753220332030426859082097)
        ·
          refine ⟨593814915249022820144311573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 791753220332030426859082097 593814915249022820144311573)
          ·
            refine ⟨27835074152297944694264605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 593814915249022820144311573 27835074152297944694264605)
            ·
              refine ⟨10438152807111729260349227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27835074152297944694264605 10438152807111729260349227)
              ·
                refine ⟨15657229210667593890523841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10438152807111729260349227 15657229210667593890523841)
                ·
                  refine ⟨11742921908000695417892881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15657229210667593890523841 11742921908000695417892881)
                  ·
                    refine ⟨8807191431000521563419661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11742921908000695417892881 8807191431000521563419661)
                    ·
                      refine ⟨3302696786625195586282373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8807191431000521563419661 3302696786625195586282373)
                      ·
                        rfl

theorem cell23_6431979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 3].length) (baseStart_6431979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431979 prefixEnd_6431979 := by exact prefixLift 6431979
  have htrace : WordTrace (prefixWord ++ tailWord_6431979) baseStart_6431979 baseEnd_6431979 := by
    simpa [prefixWord, tailWord_6431979, baseEnd_6431979] using wordTrace_append hprefix tailTrace_6431979
  have hstable : (prefixWord ++ tailWord_6431979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431979).length < 2 ^ (prefixWord ++ tailWord_6431979).sum := by decide
  have hdescent : baseEnd_6431979 < baseStart_6431979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6431999 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 6]
def baseStart_6431999 : Nat := 118140960795 + 6431999 * 2 ^ 59
def prefixEnd_6431999 : Nat := 4983230072969 + 3 ^ 40 * 6431999 * 2
def baseEnd_6431999 : Nat := 366967450693142834225809

theorem tailTrace_6431999 : CollatzResearch.WordTrace tailWord_6431999 prefixEnd_6431999 366967450693142834225809 := by
  unfold tailWord_6431999
  simp only [CollatzResearch.WordTrace]
  refine ⟨234594276224973595818419051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156396184149982397212279367 234594276224973595818419051)
  ·
    refine ⟨351891414337460393727628577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234594276224973595818419051 351891414337460393727628577)
    ·
      refine ⟨263918560753095295295721433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351891414337460393727628577 263918560753095295295721433)
      ·
        refine ⟨197938920564821471471791075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263918560753095295295721433 197938920564821471471791075)
        ·
          refine ⟨296908380847232207207686613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197938920564821471471791075 296908380847232207207686613)
          ·
            refine ⟨6958790176107004856430155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 296908380847232207207686613 6958790176107004856430155)
            ·
              refine ⟨10438185264160507284645233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6958790176107004856430155 10438185264160507284645233)
              ·
                refine ⟨7828638948120380463483925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10438185264160507284645233 7828638948120380463483925)
                ·
                  refine ⟨366967450693142834225809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7828638948120380463483925 366967450693142834225809)
                  ·
                    rfl

theorem cell23_6431999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 6].length) (baseStart_6431999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6431999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6431999 prefixEnd_6431999 := by exact prefixLift 6431999
  have htrace : WordTrace (prefixWord ++ tailWord_6431999) baseStart_6431999 baseEnd_6431999 := by
    simpa [prefixWord, tailWord_6431999, baseEnd_6431999] using wordTrace_append hprefix tailTrace_6431999
  have hstable : (prefixWord ++ tailWord_6431999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6431999).length < 2 ^ (prefixWord ++ tailWord_6431999).sum := by decide
  have hdescent : baseEnd_6431999 < baseStart_6431999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6431999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432026 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3]
def baseStart_6432026 : Nat := 118140960795 + 6432026 * 2 ^ 59
def prefixEnd_6432026 : Nat := 4983230072969 + 3 ^ 40 * 6432026 * 2
def baseEnd_6432026 : Nat := 3302720920215956902394657

theorem tailTrace_6432026 : CollatzResearch.WordTrace tailWord_6432026 prefixEnd_6432026 3302720920215956902394657 := by
  unfold tailWord_6432026
  simp only [CollatzResearch.WordTrace]
  refine ⟨58648815248968944857412983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156396840663917186286434621 58648815248968944857412983)
  ·
    refine ⟨87973222873453417286119475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58648815248968944857412983 87973222873453417286119475)
    ·
      refine ⟨131959834310180125929179213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87973222873453417286119475 131959834310180125929179213)
      ·
        refine ⟨49484937866317547223442205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131959834310180125929179213 49484937866317547223442205)
        ·
          refine ⟨18556851699869080208790827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49484937866317547223442205 18556851699869080208790827)
          ·
            refine ⟨27835277549803620313186241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18556851699869080208790827 27835277549803620313186241)
            ·
              refine ⟨20876458162352715234889681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27835277549803620313186241 20876458162352715234889681)
              ·
                refine ⟨15657343621764536426167261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20876458162352715234889681 15657343621764536426167261)
                ·
                  refine ⟨5871503858161701159812723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15657343621764536426167261 5871503858161701159812723)
                  ·
                    refine ⟨8807255787242551739719085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5871503858161701159812723 8807255787242551739719085)
                    ·
                      refine ⟨3302720920215956902394657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8807255787242551739719085 3302720920215956902394657)
                      ·
                        rfl

theorem cell23_6432026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_6432026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432026 prefixEnd_6432026 := by exact prefixLift 6432026
  have htrace : WordTrace (prefixWord ++ tailWord_6432026) baseStart_6432026 baseEnd_6432026 := by
    simpa [prefixWord, tailWord_6432026, baseEnd_6432026] using wordTrace_append hprefix tailTrace_6432026
  have hstable : (prefixWord ++ tailWord_6432026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432026).length < 2 ^ (prefixWord ++ tailWord_6432026).sum := by decide
  have hdescent : baseEnd_6432026 < baseStart_6432026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432036 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 2, 3, 2]
def baseStart_6432036 : Nat := 118140960795 + 6432036 * 2 ^ 59
def prefixEnd_6432036 : Nat := 4983230072969 + 3 ^ 40 * 6432036 * 2
def baseEnd_6432036 : Nat := 3302726055022501863269611

theorem tailTrace_6432036 : CollatzResearch.WordTrace tailWord_6432036 prefixEnd_6432036 3302726055022501863269611 := by
  unfold tailWord_6432036
  simp only [CollatzResearch.WordTrace]
  refine ⟨117297812862919775568757981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156397083817226367425010641 117297812862919775568757981)
  ·
    refine ⟨43986679823594915838284243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117297812862919775568757981 43986679823594915838284243)
    ·
      refine ⟨65980019735392373757426365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43986679823594915838284243 65980019735392373757426365)
      ·
        refine ⟨24742507400772140159034887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65980019735392373757426365 24742507400772140159034887)
        ·
          refine ⟨37113761101158210238552331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24742507400772140159034887 37113761101158210238552331)
          ·
            refine ⟨55670641651737315357828497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37113761101158210238552331 55670641651737315357828497)
            ·
              refine ⟨41752981238802986518371373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55670641651737315357828497 41752981238802986518371373)
              ·
                refine ⟨15657367964551119944389265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41752981238802986518371373 15657367964551119944389265)
                ·
                  refine ⟨11743025973413339958291949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15657367964551119944389265 11743025973413339958291949)
                  ·
                    refine ⟨4403634740030002484359481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11743025973413339958291949 4403634740030002484359481)
                    ·
                      refine ⟨3302726055022501863269611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403634740030002484359481 3302726055022501863269611)
                      ·
                        rfl

theorem cell23_6432036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_6432036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432036 prefixEnd_6432036 := by exact prefixLift 6432036
  have htrace : WordTrace (prefixWord ++ tailWord_6432036) baseStart_6432036 baseEnd_6432036 := by
    simpa [prefixWord, tailWord_6432036, baseEnd_6432036] using wordTrace_append hprefix tailTrace_6432036
  have hstable : (prefixWord ++ tailWord_6432036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432036).length < 2 ^ (prefixWord ++ tailWord_6432036).sum := by decide
  have hdescent : baseEnd_6432036 < baseStart_6432036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432060 : List Nat := [2, 2, 2, 2, 1, 4, 3, 2, 1, 1, 3]
def baseStart_6432060 : Nat := 118140960795 + 6432060 * 2 ^ 59
def prefixEnd_6432060 : Nat := 4983230072969 + 3 ^ 40 * 6432060 * 2
def baseEnd_6432060 : Nat := 3302738378558209769369501

theorem tailTrace_6432060 : CollatzResearch.WordTrace tailWord_6432060 prefixEnd_6432060 3302738378558209769369501 := by
  unfold tailWord_6432060
  simp only [CollatzResearch.WordTrace]
  refine ⟨117298250538876301618194817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156397667385168402157593089 117298250538876301618194817)
  ·
    refine ⟨87973687904157226213646113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117298250538876301618194817 87973687904157226213646113)
    ·
      refine ⟨65980265928117919660234585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87973687904157226213646113 65980265928117919660234585)
      ·
        refine ⟨49485199446088439745175939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65980265928117919660234585 49485199446088439745175939)
        ·
          refine ⟨74227799169132659617763909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49485199446088439745175939 74227799169132659617763909)
          ·
            refine ⟨13917712344212373678330733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74227799169132659617763909 13917712344212373678330733)
            ·
              refine ⟨5219142129079640129374025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13917712344212373678330733 5219142129079640129374025)
              ·
                refine ⟨3914356596809730097030519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5219142129079640129374025 3914356596809730097030519)
                ·
                  refine ⟨5871534895214595145545779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3914356596809730097030519 5871534895214595145545779)
                  ·
                    refine ⟨8807302342821892718318669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5871534895214595145545779 8807302342821892718318669)
                    ·
                      refine ⟨3302738378558209769369501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8807302342821892718318669 3302738378558209769369501)
                      ·
                        rfl

theorem cell23_6432060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_6432060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432060 prefixEnd_6432060 := by exact prefixLift 6432060
  have htrace : WordTrace (prefixWord ++ tailWord_6432060) baseStart_6432060 baseEnd_6432060 := by
    simpa [prefixWord, tailWord_6432060, baseEnd_6432060] using wordTrace_append hprefix tailTrace_6432060
  have hstable : (prefixWord ++ tailWord_6432060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432060).length < 2 ^ (prefixWord ++ tailWord_6432060).sum := by decide
  have hdescent : baseEnd_6432060 < baseStart_6432060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432076 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 2, 4]
def baseStart_6432076 : Nat := 118140960795 + 6432076 * 2 ^ 59
def prefixEnd_6432076 : Nat := 4983230072969 + 3 ^ 40 * 6432076 * 2
def baseEnd_6432076 : Nat := 1100915531416227235589809

theorem tailTrace_6432076 : CollatzResearch.WordTrace tailWord_6432076 prefixEnd_6432076 1100915531416227235589809 := by
  unfold tailWord_6432076
  simp only [CollatzResearch.WordTrace]
  refine ⟨117298542322847318984486041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156398056430463091979314721 117298542322847318984486041)
  ·
    refine ⟨87973906742135489238364531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117298542322847318984486041 87973906742135489238364531)
    ·
      refine ⟨131960860113203233857546797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87973906742135489238364531 131960860113203233857546797)
      ·
        refine ⟨49485322542451212696580049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131960860113203233857546797 49485322542451212696580049)
        ·
          refine ⟨37113991906838409522435037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49485322542451212696580049 37113991906838409522435037)
          ·
            refine ⟨13917746965064403570913139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37113991906838409522435037 13917746965064403570913139)
            ·
              refine ⟨20876620447596605356369709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13917746965064403570913139 20876620447596605356369709)
              ·
                refine ⟨7828732667848727008638641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20876620447596605356369709 7828732667848727008638641)
                ·
                  refine ⟨5871549500886545256478981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7828732667848727008638641 5871549500886545256478981)
                  ·
                    refine ⟨1100915531416227235589809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5871549500886545256478981 1100915531416227235589809)
                    ·
                      rfl

theorem cell23_6432076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_6432076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432076 prefixEnd_6432076 := by exact prefixLift 6432076
  have htrace : WordTrace (prefixWord ++ tailWord_6432076) baseStart_6432076 baseEnd_6432076 := by
    simpa [prefixWord, tailWord_6432076, baseEnd_6432076] using wordTrace_append hprefix tailTrace_6432076
  have hstable : (prefixWord ++ tailWord_6432076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432076).length < 2 ^ (prefixWord ++ tailWord_6432076).sum := by decide
  have hdescent : baseEnd_6432076 < baseStart_6432076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432099 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 3]
def baseStart_6432099 : Nat := 118140960795 + 6432099 * 2 ^ 59
def prefixEnd_6432099 : Nat := 4983230072969 + 3 ^ 40 * 6432099 * 2
def baseEnd_6432099 : Nat := 3302758404303735116781821

theorem tailTrace_6432099 : CollatzResearch.WordTrace tailWord_6432099 prefixEnd_6432099 3302758404303735116781821 := by
  unfold tailWord_6432099
  simp only [CollatzResearch.WordTrace]
  refine ⟨234597923524611312897059351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156398615683074208598039567 234597923524611312897059351)
  ·
    refine ⟨351896885286916969345589027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234597923524611312897059351 351896885286916969345589027)
    ·
      refine ⟨527845327930375454018383541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351896885286916969345589027 527845327930375454018383541)
      ·
        refine ⟨49485499493472698814223457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 527845327930375454018383541 49485499493472698814223457)
        ·
          refine ⟨37114124620104524110667593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49485499493472698814223457 37114124620104524110667593)
          ·
            refine ⟨27835593465078393083000695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37114124620104524110667593 27835593465078393083000695)
            ·
              refine ⟨41753390197617589624501043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27835593465078393083000695 41753390197617589624501043)
              ·
                refine ⟨62630085296426384436751565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41753390197617589624501043 62630085296426384436751565)
                ·
                  refine ⟨23486281986159894163781837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62630085296426384436751565 23486281986159894163781837)
                  ·
                    refine ⟨8807355744809960311418189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23486281986159894163781837 8807355744809960311418189)
                    ·
                      refine ⟨3302758404303735116781821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8807355744809960311418189 3302758404303735116781821)
                      ·
                        rfl

theorem cell23_6432099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_6432099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432099 prefixEnd_6432099 := by exact prefixLift 6432099
  have htrace : WordTrace (prefixWord ++ tailWord_6432099) baseStart_6432099 baseEnd_6432099 := by
    simpa [prefixWord, tailWord_6432099, baseEnd_6432099] using wordTrace_append hprefix tailTrace_6432099
  have hstable : (prefixWord ++ tailWord_6432099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432099).length < 2 ^ (prefixWord ++ tailWord_6432099).sum := by decide
  have hdescent : baseEnd_6432099 < baseStart_6432099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432103 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_6432103 : Nat := 118140960795 + 6432103 * 2 ^ 59
def prefixEnd_6432103 : Nat := 4983230072969 + 3 ^ 40 * 6432103 * 2
def baseEnd_6432103 : Nat := 3302760458226353101131803

theorem tailTrace_6432103 : CollatzResearch.WordTrace tailWord_6432103 prefixEnd_6432103 3302760458226353101131803 := by
  unfold tailWord_6432103
  simp only [CollatzResearch.WordTrace]
  refine ⟨234598069416596821580204963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156398712944397881053469975 234598069416596821580204963)
  ·
    refine ⟨351897104124895232370307445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234598069416596821580204963 351897104124895232370307445)
    ·
      refine ⟨32990353511708928034716323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 351897104124895232370307445 32990353511708928034716323)
      ·
        refine ⟨49485530267563392052074485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32990353511708928034716323 49485530267563392052074485)
        ·
          refine ⟨4639268462584068004881983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49485530267563392052074485 4639268462584068004881983)
          ·
            refine ⟨6958902693876102007322975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639268462584068004881983 6958902693876102007322975)
            ·
              refine ⟨10438354040814153010984463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6958902693876102007322975 10438354040814153010984463)
              ·
                refine ⟨15657531061221229516476695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10438354040814153010984463 15657531061221229516476695)
                ·
                  refine ⟨23486296591831844274715043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15657531061221229516476695 23486296591831844274715043)
                  ·
                    refine ⟨35229444887747766412072565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23486296591831844274715043 35229444887747766412072565)
                    ·
                      refine ⟨3302760458226353101131803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35229444887747766412072565 3302760458226353101131803)
                      ·
                        rfl

theorem cell23_6432103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_6432103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432103 prefixEnd_6432103 := by exact prefixLift 6432103
  have htrace : WordTrace (prefixWord ++ tailWord_6432103) baseStart_6432103 baseEnd_6432103 := by
    simpa [prefixWord, tailWord_6432103, baseEnd_6432103] using wordTrace_append hprefix tailTrace_6432103
  have hstable : (prefixWord ++ tailWord_6432103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432103).length < 2 ^ (prefixWord ++ tailWord_6432103).sum := by decide
  have hdescent : baseEnd_6432103 < baseStart_6432103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432110 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_6432110 : Nat := 118140960795 + 6432110 * 2 ^ 59
def prefixEnd_6432110 : Nat := 4983230072969 + 3 ^ 40 * 6432110 * 2
def baseEnd_6432110 : Nat := 1100921350863644857914757

theorem tailTrace_6432110 : CollatzResearch.WordTrace tailWord_6432110 prefixEnd_6432110 1100921350863644857914757 := by
  unfold tailWord_6432110
  simp only [CollatzResearch.WordTrace]
  refine ⟨29324790590946432721963723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156398883151714307850473189 29324790590946432721963723)
  ·
    refine ⟨43987185886419649082945585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29324790590946432721963723 43987185886419649082945585)
    ·
      refine ⟨32990389414814736812209189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43987185886419649082945585 32990389414814736812209189)
      ·
        refine ⟨6185698015277763152289223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32990389414814736812209189 6185698015277763152289223)
        ·
          refine ⟨9278547022916644728433835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6185698015277763152289223 9278547022916644728433835)
          ·
            refine ⟨13917820534374967092650753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9278547022916644728433835 13917820534374967092650753)
            ·
              refine ⟨10438365400781225319488065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13917820534374967092650753 10438365400781225319488065)
              ·
                refine ⟨7828774050585918989616049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10438365400781225319488065 7828774050585918989616049)
                ·
                  refine ⟨5871580537939439242212037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7828774050585918989616049 5871580537939439242212037)
                  ·
                    refine ⟨1100921350863644857914757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5871580537939439242212037 1100921350863644857914757)
                    ·
                      rfl

theorem cell23_6432110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_6432110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432110 prefixEnd_6432110 := by exact prefixLift 6432110
  have htrace : WordTrace (prefixWord ++ tailWord_6432110) baseStart_6432110 baseEnd_6432110 := by
    simpa [prefixWord, tailWord_6432110, baseEnd_6432110] using wordTrace_append hprefix tailTrace_6432110
  have hstable : (prefixWord ++ tailWord_6432110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432110).length < 2 ^ (prefixWord ++ tailWord_6432110).sum := by decide
  have hdescent : baseEnd_6432110 < baseStart_6432110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432117 : List Nat := [1, 3, 4, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_6432117 : Nat := 118140960795 + 6432117 * 2 ^ 59
def prefixEnd_6432117 : Nat := 4983230072969 + 3 ^ 40 * 6432117 * 2
def baseEnd_6432117 : Nat := 3302767646955516046356739

theorem tailTrace_6432117 : CollatzResearch.WordTrace tailWord_6432117 prefixEnd_6432117 3302767646955516046356739 := by
  unfold tailWord_6432117
  simp only [CollatzResearch.WordTrace]
  refine ⟨234598580038546101971214605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156399053359030734647476403 234598580038546101971214605)
  ·
    refine ⟨87974467514454788239205477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234598580038546101971214605 87974467514454788239205477)
    ·
      refine ⟨16495212658960272794851027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87974467514454788239205477 16495212658960272794851027)
      ·
        refine ⟨24742818988440409192276541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16495212658960272794851027 24742818988440409192276541)
        ·
          refine ⟨9278557120665153447103703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24742818988440409192276541 9278557120665153447103703)
          ·
            refine ⟨13917835680997730170655555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9278557120665153447103703 13917835680997730170655555)
            ·
              refine ⟨20876753521496595255983333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13917835680997730170655555 20876753521496595255983333)
              ·
                refine ⟨3914391285280611610496875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20876753521496595255983333 3914391285280611610496875)
                ·
                  refine ⟨5871586927920917415745313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3914391285280611610496875 5871586927920917415745313)
                  ·
                    refine ⟨4403690195940688061808985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5871586927920917415745313 4403690195940688061808985)
                    ·
                      refine ⟨3302767646955516046356739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403690195940688061808985 3302767646955516046356739)
                      ·
                        rfl

theorem cell23_6432117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_6432117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432117 prefixEnd_6432117 := by exact prefixLift 6432117
  have htrace : WordTrace (prefixWord ++ tailWord_6432117) baseStart_6432117 baseEnd_6432117 := by
    simpa [prefixWord, tailWord_6432117, baseEnd_6432117] using wordTrace_append hprefix tailTrace_6432117
  have hstable : (prefixWord ++ tailWord_6432117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432117).length < 2 ^ (prefixWord ++ tailWord_6432117).sum := by decide
  have hdescent : baseEnd_6432117 < baseStart_6432117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432196 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 7]
def baseStart_6432196 : Nat := 118140960795 + 6432196 * 2 ^ 59
def prefixEnd_6432196 : Nat := 4983230072969 + 3 ^ 40 * 6432196 * 2
def baseEnd_6432196 : Nat := 366978690214135693029875

theorem tailTrace_6432196 : CollatzResearch.WordTrace tailWord_6432196 prefixEnd_6432196 366978690214135693029875 := by
  unfold tailWord_6432196
  simp only [CollatzResearch.WordTrace]
  refine ⟨117300730702629949231670221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156400974270173265642226961 117300730702629949231670221)
  ·
    refine ⟨43987774013486230961876333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117300730702629949231670221 43987774013486230961876333)
    ·
      refine ⟨16495415255057336610703625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43987774013486230961876333 16495415255057336610703625)
      ·
        refine ⟨12371561441293002458027719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16495415255057336610703625 12371561441293002458027719)
        ·
          refine ⟨18557342161939503687041579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12371561441293002458027719 18557342161939503687041579)
          ·
            refine ⟨27836013242909255530562369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18557342161939503687041579 27836013242909255530562369)
            ·
              refine ⟨20877009932181941647921777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27836013242909255530562369 20877009932181941647921777)
              ·
                refine ⟨15657757449136456235941333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20877009932181941647921777 15657757449136456235941333)
                ·
                  refine ⟨366978690214135693029875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15657757449136456235941333 366978690214135693029875)
                  ·
                    rfl

theorem cell23_6432196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_6432196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432196 prefixEnd_6432196 := by exact prefixLift 6432196
  have htrace : WordTrace (prefixWord ++ tailWord_6432196) baseStart_6432196 baseEnd_6432196 := by
    simpa [prefixWord, tailWord_6432196, baseEnd_6432196] using wordTrace_append hprefix tailTrace_6432196
  have hstable : (prefixWord ++ tailWord_6432196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432196).length < 2 ^ (prefixWord ++ tailWord_6432196).sum := by decide
  have hdescent : baseEnd_6432196 < baseStart_6432196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432263 : List Nat := [1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_6432263 : Nat := 118140960795 + 6432263 * 2 ^ 59
def prefixEnd_6432263 : Nat := 4983230072969 + 3 ^ 40 * 6432263 * 2
def baseEnd_6432263 : Nat := 3302842615131072475131067

theorem tailTrace_6432263 : CollatzResearch.WordTrace tailWord_6432263 prefixEnd_6432263 3302842615131072475131067 := by
  unfold tailWord_6432263
  simp only [CollatzResearch.WordTrace]
  refine ⟨234603905096017168906029443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156402603397344779270686295 234603905096017168906029443)
  ·
    refine ⟨351905857644025753359044165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234603905096017168906029443 351905857644025753359044165)
    ·
      refine ⟨65982348308254828754820781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351905857644025753359044165 65982348308254828754820781)
      ·
        refine ⟨24743380615595560783057793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65982348308254828754820781 24743380615595560783057793)
        ·
          refine ⟨18557535461696670587293345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24743380615595560783057793 18557535461696670587293345)
          ·
            refine ⟨13918151596272502940470009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18557535461696670587293345 13918151596272502940470009)
            ·
              refine ⟨10438613697204377205352507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13918151596272502940470009 10438613697204377205352507)
              ·
                refine ⟨15657920545806565808028761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10438613697204377205352507 15657920545806565808028761)
                ·
                  refine ⟨11743440409354924356021571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15657920545806565808028761 11743440409354924356021571)
                  ·
                    refine ⟨17615160614032386534032357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11743440409354924356021571 17615160614032386534032357)
                    ·
                      refine ⟨3302842615131072475131067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17615160614032386534032357 3302842615131072475131067)
                      ·
                        rfl

theorem cell23_6432263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_6432263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432263 prefixEnd_6432263 := by exact prefixLift 6432263
  have htrace : WordTrace (prefixWord ++ tailWord_6432263) baseStart_6432263 baseEnd_6432263 := by
    simpa [prefixWord, tailWord_6432263, baseEnd_6432263] using wordTrace_append hprefix tailTrace_6432263
  have hstable : (prefixWord ++ tailWord_6432263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432263).length < 2 ^ (prefixWord ++ tailWord_6432263).sum := by decide
  have hdescent : baseEnd_6432263 < baseStart_6432263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432273 : List Nat := [1, 2, 2, 1, 1, 2, 4, 5, 1, 4]
def baseStart_6432273 : Nat := 118140960795 + 6432273 * 2 ^ 59
def prefixEnd_6432273 : Nat := 4983230072969 + 3 ^ 40 * 6432273 * 2
def baseEnd_6432273 : Nat := 1100949249979205812002007

theorem tailTrace_6432273 : CollatzResearch.WordTrace tailWord_6432273 prefixEnd_6432273 1100949249979205812002007 := by
  unfold tailWord_6432273
  simp only [CollatzResearch.WordTrace]
  refine ⟨234604269825980940613893473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156402846550653960409262315 234604269825980940613893473)
  ·
    refine ⟨175953202369485705460420105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234604269825980940613893473 175953202369485705460420105)
    ·
      refine ⟨131964901777114279095315079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175953202369485705460420105 131964901777114279095315079)
      ·
        refine ⟨197947352665671418642972619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131964901777114279095315079 197947352665671418642972619)
        ·
          refine ⟨296921028998507127964458929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197947352665671418642972619 296921028998507127964458929)
          ·
            refine ⟨222690771748880345973344197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296921028998507127964458929 222690771748880345973344197)
            ·
              refine ⟨41754519702915064870002037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222690771748880345973344197 41754519702915064870002037)
              ·
                refine ⟨3914486222148287331562691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41754519702915064870002037 3914486222148287331562691)
                ·
                  refine ⟨5871729333222430997344037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3914486222148287331562691 5871729333222430997344037)
                  ·
                    refine ⟨1100949249979205812002007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5871729333222430997344037 1100949249979205812002007)
                    ·
                      rfl

theorem cell23_6432273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 1, 4].length) (baseStart_6432273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432273 prefixEnd_6432273 := by exact prefixLift 6432273
  have htrace : WordTrace (prefixWord ++ tailWord_6432273) baseStart_6432273 baseEnd_6432273 := by
    simpa [prefixWord, tailWord_6432273, baseEnd_6432273] using wordTrace_append hprefix tailTrace_6432273
  have hstable : (prefixWord ++ tailWord_6432273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432273).length < 2 ^ (prefixWord ++ tailWord_6432273).sum := by decide
  have hdescent : baseEnd_6432273 < baseStart_6432273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432313 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 5, 1, 3]
def baseStart_6432313 : Nat := 118140960795 + 6432313 * 2 ^ 59
def prefixEnd_6432313 : Nat := 4983230072969 + 3 ^ 40 * 6432313 * 2
def baseEnd_6432313 : Nat := 3302868289163797279505837

theorem tailTrace_6432313 : CollatzResearch.WordTrace tailWord_6432313 prefixEnd_6432313 3302868289163797279505837 := by
  unfold tailWord_6432313
  simp only [CollatzResearch.WordTrace]
  refine ⟨234605728745836027445349593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156403819163890684963566395 234605728745836027445349593)
  ·
    refine ⟨175954296559377020584012195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234605728745836027445349593 175954296559377020584012195)
    ·
      refine ⟨263931444839065530876018293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175954296559377020584012195 263931444839065530876018293)
      ·
        refine ⟨24743572953662393519626715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 263931444839065530876018293 24743572953662393519626715)
        ·
          refine ⟨37115359430493590279440073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24743572953662393519626715 37115359430493590279440073)
          ·
            refine ⟨27836519572870192709580055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37115359430493590279440073 27836519572870192709580055)
            ·
              refine ⟨41754779359305289064370083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27836519572870192709580055 41754779359305289064370083)
              ·
                refine ⟨62632169038957933596555125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41754779359305289064370083 62632169038957933596555125)
                ·
                  refine ⟨5871765847402306274677043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62632169038957933596555125 5871765847402306274677043)
                  ·
                    refine ⟨8807648771103459412015565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5871765847402306274677043 8807648771103459412015565)
                    ·
                      refine ⟨3302868289163797279505837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8807648771103459412015565 3302868289163797279505837)
                      ·
                        rfl

theorem cell23_6432313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_6432313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432313 prefixEnd_6432313 := by exact prefixLift 6432313
  have htrace : WordTrace (prefixWord ++ tailWord_6432313) baseStart_6432313 baseEnd_6432313 := by
    simpa [prefixWord, tailWord_6432313, baseEnd_6432313] using wordTrace_append hprefix tailTrace_6432313
  have hstable : (prefixWord ++ tailWord_6432313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432313).length < 2 ^ (prefixWord ++ tailWord_6432313).sum := by decide
  have hdescent : baseEnd_6432313 < baseStart_6432313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432317 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 2, 2, 3]
def baseStart_6432317 : Nat := 118140960795 + 6432317 * 2 ^ 59
def prefixEnd_6432317 : Nat := 4983230072969 + 3 ^ 40 * 6432317 * 2
def baseEnd_6432317 : Nat := 3302870343086415263855819

theorem tailTrace_6432317 : CollatzResearch.WordTrace tailWord_6432317 prefixEnd_6432317 3302870343086415263855819 := by
  unfold tailWord_6432317
  simp only [CollatzResearch.WordTrace]
  refine ⟨234605874637821536128495205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156403916425214357418996803 234605874637821536128495205)
  ·
    refine ⟨43988601494591538024092851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234605874637821536128495205 43988601494591538024092851)
    ·
      refine ⟨65982902241887307036139277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43988601494591538024092851 65982902241887307036139277)
      ·
        refine ⟨24743588340707740138552229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65982902241887307036139277 24743588340707740138552229)
        ·
          refine ⟨4639422813882701275978543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24743588340707740138552229 4639422813882701275978543)
          ·
            refine ⟨6959134220824051913967815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639422813882701275978543 6959134220824051913967815)
            ·
              refine ⟨10438701331236077870951723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6959134220824051913967815 10438701331236077870951723)
              ·
                refine ⟨15658051996854116806427585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10438701331236077870951723 15658051996854116806427585)
                ·
                  refine ⟨11743538997640587604820689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15658051996854116806427585 11743538997640587604820689)
                  ·
                    refine ⟨8807654248230440703615517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11743538997640587604820689 8807654248230440703615517)
                    ·
                      refine ⟨3302870343086415263855819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8807654248230440703615517 3302870343086415263855819)
                      ·
                        rfl

theorem cell23_6432317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_6432317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432317 prefixEnd_6432317 := by exact prefixLift 6432317
  have htrace : WordTrace (prefixWord ++ tailWord_6432317) baseStart_6432317 baseEnd_6432317 := by
    simpa [prefixWord, tailWord_6432317, baseEnd_6432317] using wordTrace_append hprefix tailTrace_6432317
  have hstable : (prefixWord ++ tailWord_6432317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432317).length < 2 ^ (prefixWord ++ tailWord_6432317).sum := by decide
  have hdescent : baseEnd_6432317 < baseStart_6432317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432356 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_6432356 : Nat := 118140960795 + 6432356 * 2 ^ 59
def prefixEnd_6432356 : Nat := 4983230072969 + 3 ^ 40 * 6432356 * 2
def baseEnd_6432356 : Nat := 3302890368831940611268139

theorem tailTrace_6432356 : CollatzResearch.WordTrace tailWord_6432356 prefixEnd_6432356 3302890368831940611268139 := by
  unfold tailWord_6432356
  simp only [CollatzResearch.WordTrace]
  refine ⟨117303648542340122894582461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156404864723120163859443281 117303648542340122894582461)
  ·
    refine ⟨43988868203377546085468423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117303648542340122894582461 43988868203377546085468423)
    ·
      refine ⟨65983302305066319128202635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43988868203377546085468423 65983302305066319128202635)
      ·
        refine ⟨98974953457599478692303953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65983302305066319128202635 98974953457599478692303953)
        ·
          refine ⟨74231215093199609019227965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98974953457599478692303953 74231215093199609019227965)
          ·
            refine ⟨27836705659949853382210487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74231215093199609019227965 27836705659949853382210487)
            ·
              refine ⟨41755058489924780073315731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27836705659949853382210487 41755058489924780073315731)
              ·
                refine ⟨62632587734887170109973597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41755058489924780073315731 62632587734887170109973597)
                ·
                  refine ⟨23487220400582688791240099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62632587734887170109973597 23487220400582688791240099)
                  ·
                    refine ⟨35230830600874033186860149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23487220400582688791240099 35230830600874033186860149)
                    ·
                      refine ⟨3302890368831940611268139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35230830600874033186860149 3302890368831940611268139)
                      ·
                        rfl

theorem cell23_6432356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_6432356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432356 prefixEnd_6432356 := by exact prefixLift 6432356
  have htrace : WordTrace (prefixWord ++ tailWord_6432356) baseStart_6432356 baseEnd_6432356 := by
    simpa [prefixWord, tailWord_6432356, baseEnd_6432356] using wordTrace_append hprefix tailTrace_6432356
  have hstable : (prefixWord ++ tailWord_6432356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432356).length < 2 ^ (prefixWord ++ tailWord_6432356).sum := by decide
  have hdescent : baseEnd_6432356 < baseStart_6432356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432370 : List Nat := [3, 2, 1, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_6432370 : Nat := 118140960795 + 6432370 * 2 ^ 59
def prefixEnd_6432370 : Nat := 4983230072969 + 3 ^ 40 * 6432370 * 2
def baseEnd_6432370 : Nat := 3302897557561103556493075

theorem tailTrace_6432370 : CollatzResearch.WordTrace tailWord_6432370 prefixEnd_6432370 3302897557561103556493075 := by
  unfold tailWord_6432370
  simp only [CollatzResearch.WordTrace]
  refine ⟨58651951926657381545043641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156405205137753017453449709 58651951926657381545043641)
  ·
    refine ⟨43988963944993036158782731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58651951926657381545043641 43988963944993036158782731)
    ·
      refine ⟨65983445917489554238174097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43988963944993036158782731 65983445917489554238174097)
      ·
        refine ⟨49487584438117165678630573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65983445917489554238174097 49487584438117165678630573)
        ·
          refine ⟨18557844164293937129486465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49487584438117165678630573 18557844164293937129486465)
          ·
            refine ⟨13918383123220452847114849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18557844164293937129486465 13918383123220452847114849)
            ·
              refine ⟨10438787342415339635336137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13918383123220452847114849 10438787342415339635336137)
              ·
                refine ⟨7829090506811504726502103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10438787342415339635336137 7829090506811504726502103)
                ·
                  refine ⟨11743635760217257089753155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7829090506811504726502103 11743635760217257089753155)
                  ·
                    refine ⟨17615453640325885634629733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11743635760217257089753155 17615453640325885634629733)
                    ·
                      refine ⟨3302897557561103556493075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17615453640325885634629733 3302897557561103556493075)
                      ·
                        rfl

theorem cell23_6432370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_6432370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432370 prefixEnd_6432370 := by exact prefixLift 6432370
  have htrace : WordTrace (prefixWord ++ tailWord_6432370) baseStart_6432370 baseEnd_6432370 := by
    simpa [prefixWord, tailWord_6432370, baseEnd_6432370] using wordTrace_append hprefix tailTrace_6432370
  have hstable : (prefixWord ++ tailWord_6432370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432370).length < 2 ^ (prefixWord ++ tailWord_6432370).sum := by decide
  have hdescent : baseEnd_6432370 < baseStart_6432370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432413 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_6432413 : Nat := 118140960795 + 6432413 * 2 ^ 59
def prefixEnd_6432413 : Nat := 4983230072969 + 3 ^ 40 * 6432413 * 2
def baseEnd_6432413 : Nat := 3302919637229246888255377

theorem tailTrace_6432413 : CollatzResearch.WordTrace tailWord_6432413 prefixEnd_6432413 3302919637229246888255377 := by
  unfold tailWord_6432413
  simp only [CollatzResearch.WordTrace]
  refine ⟨234609376045473744523989893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156406250696982496349326595 234609376045473744523989893)
  ·
    refine ⟨43989258008526327098248105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234609376045473744523989893 43989258008526327098248105)
    ·
      refine ⟨32991943506394745323686079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43989258008526327098248105 32991943506394745323686079)
      ·
        refine ⟨49487915259592117985529119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32991943506394745323686079 49487915259592117985529119)
        ·
          refine ⟨74231872889388176978293679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49487915259592117985529119 74231872889388176978293679)
          ·
            refine ⟨111347809334082265467440519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74231872889388176978293679 111347809334082265467440519)
            ·
              refine ⟨167021714001123398201160779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111347809334082265467440519 167021714001123398201160779)
              ·
                refine ⟨250532571001685097301741169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167021714001123398201160779 250532571001685097301741169)
                ·
                  refine ⟨187899428251263822976305877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250532571001685097301741169 187899428251263822976305877)
                  ·
                    refine ⟨4403892849638995851007169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 187899428251263822976305877 4403892849638995851007169)
                    ·
                      refine ⟨3302919637229246888255377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403892849638995851007169 3302919637229246888255377)
                      ·
                        rfl

theorem cell23_6432413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_6432413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432413 prefixEnd_6432413 := by exact prefixLift 6432413
  have htrace : WordTrace (prefixWord ++ tailWord_6432413) baseStart_6432413 baseEnd_6432413 := by
    simpa [prefixWord, tailWord_6432413, baseEnd_6432413] using wordTrace_append hprefix tailTrace_6432413
  have hstable : (prefixWord ++ tailWord_6432413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432413).length < 2 ^ (prefixWord ++ tailWord_6432413).sum := by decide
  have hdescent : baseEnd_6432413 < baseStart_6432413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432414 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_6432414 : Nat := 118140960795 + 6432414 * 2 ^ 59
def prefixEnd_6432414 : Nat := 4983230072969 + 3 ^ 40 * 6432414 * 2
def baseEnd_6432414 : Nat := 1100973383569967128114291

theorem tailTrace_6432414 : CollatzResearch.WordTrace tailWord_6432414 prefixEnd_6432414 1100973383569967128114291 := by
  unfold tailWord_6432414
  simp only [CollatzResearch.WordTrace]
  refine ⟨29326176564808765211847037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156406275012313414463184197 29326176564808765211847037)
  ·
    refine ⟨10997316211803286954442639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29326176564808765211847037 10997316211803286954442639)
    ·
      refine ⟨16495974317704930431663959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10997316211803286954442639 16495974317704930431663959)
      ·
        refine ⟨24743961476557395647495939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16495974317704930431663959 24743961476557395647495939)
        ·
          refine ⟨37115942214836093471243909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24743961476557395647495939 37115942214836093471243909)
          ·
            refine ⟨6959239165281767525858233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37115942214836093471243909 6959239165281767525858233)
            ·
              refine ⟨5219429373961325644393675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6959239165281767525858233 5219429373961325644393675)
              ·
                refine ⟨7829144060941988466590513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219429373961325644393675 7829144060941988466590513)
                ·
                  refine ⟨5871858045706491349942885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7829144060941988466590513 5871858045706491349942885)
                  ·
                    refine ⟨1100973383569967128114291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5871858045706491349942885 1100973383569967128114291)
                    ·
                      rfl

theorem cell23_6432414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_6432414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432414 prefixEnd_6432414 := by exact prefixLift 6432414
  have htrace : WordTrace (prefixWord ++ tailWord_6432414) baseStart_6432414 baseEnd_6432414 := by
    simpa [prefixWord, tailWord_6432414, baseEnd_6432414] using wordTrace_append hprefix tailTrace_6432414
  have hstable : (prefixWord ++ tailWord_6432414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432414).length < 2 ^ (prefixWord ++ tailWord_6432414).sum := by decide
  have hdescent : baseEnd_6432414 < baseStart_6432414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432424 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6432424 : Nat := 118140960795 + 6432424 * 2 ^ 59
def prefixEnd_6432424 : Nat := 4983230072969 + 3 ^ 40 * 6432424 * 2
def baseEnd_6432424 : Nat := 3302925285516446345217827

theorem tailTrace_6432424 : CollatzResearch.WordTrace tailWord_6432424 prefixEnd_6432424 3302925285516446345217827 := by
  unfold tailWord_6432424
  simp only [CollatzResearch.WordTrace]
  refine ⟨117304888624216946701320163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156406518165622595601760217 117304888624216946701320163)
  ·
    refine ⟨175957332936325420051980245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117304888624216946701320163 175957332936325420051980245)
    ·
      refine ⟨4123999990695127032468287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 175957332936325420051980245 4123999990695127032468287)
      ·
        refine ⟨6185999986042690548702431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4123999990695127032468287 6185999986042690548702431)
        ·
          refine ⟨9278999979064035823053647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6185999986042690548702431 9278999979064035823053647)
          ·
            refine ⟨13918499968596053734580471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9278999979064035823053647 13918499968596053734580471)
            ·
              refine ⟨20877749952894080601870707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13918499968596053734580471 20877749952894080601870707)
              ·
                refine ⟨31316624929341120902806061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20877749952894080601870707 31316624929341120902806061)
                ·
                  refine ⟨11743734348502920338552273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31316624929341120902806061 11743734348502920338552273)
                  ·
                    refine ⟨8807800761377190253914205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11743734348502920338552273 8807800761377190253914205)
                    ·
                      refine ⟨3302925285516446345217827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8807800761377190253914205 3302925285516446345217827)
                      ·
                        rfl

theorem cell23_6432424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6432424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432424 prefixEnd_6432424 := by exact prefixLift 6432424
  have htrace : WordTrace (prefixWord ++ tailWord_6432424) baseStart_6432424 baseEnd_6432424 := by
    simpa [prefixWord, tailWord_6432424, baseEnd_6432424] using wordTrace_append hprefix tailTrace_6432424
  have hstable : (prefixWord ++ tailWord_6432424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432424).length < 2 ^ (prefixWord ++ tailWord_6432424).sum := by decide
  have hdescent : baseEnd_6432424 < baseStart_6432424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432447 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 1, 3, 2]
def baseStart_6432447 : Nat := 118140960795 + 6432447 * 2 ^ 59
def prefixEnd_6432447 : Nat := 4983230072969 + 3 ^ 40 * 6432447 * 2
def baseEnd_6432447 : Nat := 3302937095571499755230221

theorem tailTrace_6432447 : CollatzResearch.WordTrace tailWord_6432447 prefixEnd_6432447 3302937095571499755230221 := by
  unfold tailWord_6432447
  simp only [CollatzResearch.WordTrace]
  refine ⟨234610616127350568330727595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156407077418233712220485063 234610616127350568330727595)
  ·
    refine ⟨351915924191025852496091393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234610616127350568330727595 351915924191025852496091393)
    ·
      refine ⟨263936943143269389372068545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351915924191025852496091393 263936943143269389372068545)
      ·
        refine ⟨197952707357452042029051409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263936943143269389372068545 197952707357452042029051409)
        ·
          refine ⟨148464530518089031521788557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197952707357452042029051409 148464530518089031521788557)
          ·
            refine ⟨55674198944283386820670709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148464530518089031521788557 55674198944283386820670709)
            ·
              refine ⟨5219456151026567514437879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55674198944283386820670709 5219456151026567514437879)
              ·
                refine ⟨7829184226539851271656819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219456151026567514437879 7829184226539851271656819)
                ·
                  refine ⟨11743776339809776907485229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7829184226539851271656819 11743776339809776907485229)
                  ·
                    refine ⟨4403916127428666340306961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11743776339809776907485229 4403916127428666340306961)
                    ·
                      refine ⟨3302937095571499755230221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4403916127428666340306961 3302937095571499755230221)
                      ·
                        rfl

theorem cell23_6432447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 1, 3, 2].length) (baseStart_6432447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432447 prefixEnd_6432447 := by exact prefixLift 6432447
  have htrace : WordTrace (prefixWord ++ tailWord_6432447) baseStart_6432447 baseEnd_6432447 := by
    simpa [prefixWord, tailWord_6432447, baseEnd_6432447] using wordTrace_append hprefix tailTrace_6432447
  have hstable : (prefixWord ++ tailWord_6432447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432447).length < 2 ^ (prefixWord ++ tailWord_6432447).sum := by decide
  have hdescent : baseEnd_6432447 < baseStart_6432447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432473 : List Nat := [1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 4]
def baseStart_6432473 : Nat := 118140960795 + 6432473 * 2 ^ 59
def prefixEnd_6432473 : Nat := 4983230072969 + 3 ^ 40 * 6432473 * 2
def baseEnd_6432473 : Nat := 3302950446068516653505101

theorem tailTrace_6432473 : CollatzResearch.WordTrace tailWord_6432473 prefixEnd_6432473 3302950446068516653505101 := by
  unfold tailWord_6432473
  simp only [CollatzResearch.WordTrace]
  refine ⟨234611564425256374771174073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156407709616837583180782715 234611564425256374771174073)
  ·
    refine ⟨175958673318942281078380555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234611564425256374771174073 175958673318942281078380555)
    ·
      refine ⟨263938009978413421617570833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175958673318942281078380555 263938009978413421617570833)
      ·
        refine ⟨197953507483810066213178125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263938009978413421617570833 197953507483810066213178125)
        ·
          refine ⟨74232565306428774829941797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197953507483810066213178125 74232565306428774829941797)
          ·
            refine ⟨13918605994955395280614087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74232565306428774829941797 13918605994955395280614087)
            ·
              refine ⟨20877908992433092920921131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13918605994955395280614087 20877908992433092920921131)
              ·
                refine ⟨31316863488649639381381697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20877908992433092920921131 31316863488649639381381697)
                ·
                  refine ⟨23487647616487229536036273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31316863488649639381381697 23487647616487229536036273)
                  ·
                    refine ⟨17615735712365422152027205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23487647616487229536036273 17615735712365422152027205)
                    ·
                      refine ⟨3302950446068516653505101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17615735712365422152027205 3302950446068516653505101)
                      ·
                        rfl

theorem cell23_6432473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_6432473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432473 prefixEnd_6432473 := by exact prefixLift 6432473
  have htrace : WordTrace (prefixWord ++ tailWord_6432473) baseStart_6432473 baseEnd_6432473 := by
    simpa [prefixWord, tailWord_6432473, baseEnd_6432473] using wordTrace_append hprefix tailTrace_6432473
  have hstable : (prefixWord ++ tailWord_6432473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432473).length < 2 ^ (prefixWord ++ tailWord_6432473).sum := by decide
  have hdescent : baseEnd_6432473 < baseStart_6432473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432513 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 2, 5]
def baseStart_6432513 : Nat := 118140960795 + 6432513 * 2 ^ 59
def prefixEnd_6432513 : Nat := 4983230072969 + 3 ^ 40 * 6432513 * 2
def baseEnd_6432513 : Nat := 1100990328431565499001639

theorem tailTrace_6432513 : CollatzResearch.WordTrace tailWord_6432513 prefixEnd_6432513 1100990328431565499001639 := by
  unfold tailWord_6432513
  simp only [CollatzResearch.WordTrace]
  refine ⟨234613023345111461602630193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156408682230074307735086795 234613023345111461602630193)
  ·
    refine ⟨175959767508833596201972645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234613023345111461602630193 175959767508833596201972645)
    ·
      refine ⟨32992456407906299287869871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175959767508833596201972645 32992456407906299287869871)
      ·
        refine ⟨49488684611859448931804807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32992456407906299287869871 49488684611859448931804807)
        ·
          refine ⟨74233026917789173397707211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49488684611859448931804807 74233026917789173397707211)
          ·
            refine ⟨111349540376683760096560817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74233026917789173397707211 111349540376683760096560817)
            ·
              refine ⟨83512155282512820072420613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111349540376683760096560817 83512155282512820072420613)
              ·
                refine ⟨15658529115471153763578865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83512155282512820072420613 15658529115471153763578865)
                ·
                  refine ⟨11743896836603365322684149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15658529115471153763578865 11743896836603365322684149)
                  ·
                    refine ⟨1100990328431565499001639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11743896836603365322684149 1100990328431565499001639)
                    ·
                      rfl

theorem cell23_6432513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_6432513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432513 prefixEnd_6432513 := by exact prefixLift 6432513
  have htrace : WordTrace (prefixWord ++ tailWord_6432513) baseStart_6432513 baseEnd_6432513 := by
    simpa [prefixWord, tailWord_6432513, baseEnd_6432513] using wordTrace_append hprefix tailTrace_6432513
  have hstable : (prefixWord ++ tailWord_6432513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432513).length < 2 ^ (prefixWord ++ tailWord_6432513).sum := by decide
  have hdescent : baseEnd_6432513 < baseStart_6432513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432530 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_6432530 : Nat := 118140960795 + 6432530 * 2 ^ 59
def prefixEnd_6432530 : Nat := 4983230072969 + 3 ^ 40 * 6432530 * 2
def baseEnd_6432530 : Nat := 1100993238155274310164113

theorem tailTrace_6432530 : CollatzResearch.WordTrace tailWord_6432530 prefixEnd_6432530 1100993238155274310164113 := by
  unfold tailWord_6432530
  simp only [CollatzResearch.WordTrace]
  refine ⟨58653410846512468376499761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156409095590699915670666029 58653410846512468376499761)
  ·
    refine ⟨43990058134884351282374821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58653410846512468376499761 43990058134884351282374821)
    ·
      refine ⟨8248135900290815865445279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43990058134884351282374821 8248135900290815865445279)
      ·
        refine ⟨12372203850436223798167919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8248135900290815865445279 12372203850436223798167919)
        ·
          refine ⟨18558305775654335697251879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12372203850436223798167919 18558305775654335697251879)
          ·
            refine ⟨27837458663481503545877819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18558305775654335697251879 27837458663481503545877819)
            ·
              refine ⟨41756187995222255318816729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27837458663481503545877819 41756187995222255318816729)
              ·
                refine ⟨31317140996416691489112547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41756187995222255318816729 31317140996416691489112547)
                ·
                  refine ⟨46975711494625037233668821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31317140996416691489112547 46975711494625037233668821)
                  ·
                    refine ⟨1100993238155274310164113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46975711494625037233668821 1100993238155274310164113)
                    ·
                      rfl

theorem cell23_6432530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_6432530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432530 prefixEnd_6432530 := by exact prefixLift 6432530
  have htrace : WordTrace (prefixWord ++ tailWord_6432530) baseStart_6432530 baseEnd_6432530 := by
    simpa [prefixWord, tailWord_6432530, baseEnd_6432530] using wordTrace_append hprefix tailTrace_6432530
  have hstable : (prefixWord ++ tailWord_6432530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432530).length < 2 ^ (prefixWord ++ tailWord_6432530).sum := by decide
  have hdescent : baseEnd_6432530 < baseStart_6432530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432533 : List Nat := [1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_6432533 : Nat := 118140960795 + 6432533 * 2 ^ 59
def prefixEnd_6432533 : Nat := 4983230072969 + 3 ^ 40 * 6432533 * 2
def baseEnd_6432533 : Nat := 3302981254907786418754825

theorem tailTrace_6432533 : CollatzResearch.WordTrace tailWord_6432533 prefixEnd_6432533 3302981254907786418754825 := by
  unfold tailWord_6432533
  simp only [CollatzResearch.WordTrace]
  refine ⟨234613752805039005018358253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156409168536692670012238835 234613752805039005018358253)
  ·
    refine ⟨87980157301889626881884345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234613752805039005018358253 87980157301889626881884345)
    ·
      refine ⟨65985117976417220161413259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87980157301889626881884345 65985117976417220161413259)
      ·
        refine ⟨98977676964625830242119889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65985117976417220161413259 98977676964625830242119889)
        ·
          refine ⟨74233257723469372681589917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98977676964625830242119889 74233257723469372681589917)
          ·
            refine ⟨27837471646301014755596219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74233257723469372681589917 27837471646301014755596219)
            ·
              refine ⟨41756207469451522133394329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27837471646301014755596219 41756207469451522133394329)
              ·
                refine ⟨31317155602088641600045747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41756207469451522133394329 31317155602088641600045747)
                ·
                  refine ⟨46975733403132962400068621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31317155602088641600045747 46975733403132962400068621)
                  ·
                    refine ⟨17615900026174860900025733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46975733403132962400068621 17615900026174860900025733)
                    ·
                      refine ⟨3302981254907786418754825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17615900026174860900025733 3302981254907786418754825)
                      ·
                        rfl

theorem cell23_6432533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_6432533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432533 prefixEnd_6432533 := by exact prefixLift 6432533
  have htrace : WordTrace (prefixWord ++ tailWord_6432533) baseStart_6432533 baseEnd_6432533 := by
    simpa [prefixWord, tailWord_6432533, baseEnd_6432533] using wordTrace_append hprefix tailTrace_6432533
  have hstable : (prefixWord ++ tailWord_6432533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432533).length < 2 ^ (prefixWord ++ tailWord_6432533).sum := by decide
  have hdescent : baseEnd_6432533 < baseStart_6432533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432570 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3]
def baseStart_6432570 : Nat := 118140960795 + 6432570 * 2 ^ 59
def prefixEnd_6432570 : Nat := 4983230072969 + 3 ^ 40 * 6432570 * 2
def baseEnd_6432570 : Nat := 3303000253692002773992155

theorem tailTrace_6432570 : CollatzResearch.WordTrace tailWord_6432570 prefixEnd_6432570 3303000253692002773992155 := by
  unfold tailWord_6432570
  simp only [CollatzResearch.WordTrace]
  refine ⟨58653775576476240084363791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156410068203936640224970109 58653775576476240084363791)
  ·
    refine ⟨87980663364714360126545687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58653775576476240084363791 87980663364714360126545687)
    ·
      refine ⟨131970995047071540189818531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87980663364714360126545687 131970995047071540189818531)
      ·
        refine ⟨197956492570607310284727797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131970995047071540189818531 197956492570607310284727797)
        ·
          refine ⟨18558421178494435339193231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197956492570607310284727797 18558421178494435339193231)
          ·
            refine ⟨27837631767741653008789847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18558421178494435339193231 27837631767741653008789847)
            ·
              refine ⟨41756447651612479513184771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27837631767741653008789847 41756447651612479513184771)
              ·
                refine ⟨62634671477418719269777157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41756447651612479513184771 62634671477418719269777157)
                ·
                  refine ⟨11744000902016009863083217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62634671477418719269777157 11744000902016009863083217)
                  ·
                    refine ⟨8808000676512007397312413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11744000902016009863083217 8808000676512007397312413)
                    ·
                      refine ⟨3303000253692002773992155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8808000676512007397312413 3303000253692002773992155)
                      ·
                        rfl

theorem cell23_6432570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_6432570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432570 prefixEnd_6432570 := by exact prefixLift 6432570
  have htrace : WordTrace (prefixWord ++ tailWord_6432570) baseStart_6432570 baseEnd_6432570 := by
    simpa [prefixWord, tailWord_6432570, baseEnd_6432570] using wordTrace_append hprefix tailTrace_6432570
  have hstable : (prefixWord ++ tailWord_6432570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432570).length < 2 ^ (prefixWord ++ tailWord_6432570).sum := by decide
  have hdescent : baseEnd_6432570 < baseStart_6432570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432604 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_6432604 : Nat := 118140960795 + 6432604 * 2 ^ 59
def prefixEnd_6432604 : Nat := 4983230072969 + 3 ^ 40 * 6432604 * 2
def baseEnd_6432604 : Nat := 3303017712034255640966999

theorem tailTrace_6432604 : CollatzResearch.WordTrace tailWord_6432604 prefixEnd_6432604 3303017712034255640966999 := by
  unfold tailWord_6432604
  simp only [CollatzResearch.WordTrace]
  refine ⟨117308171193890892072096433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156410894925187856096128577 117308171193890892072096433)
  ·
    refine ⟨87981128395418169054072325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117308171193890892072096433 87981128395418169054072325)
    ·
      refine ⟨16496461574140906697638561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87981128395418169054072325 16496461574140906697638561)
      ·
        refine ⟨12372346180605680023228921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16496461574140906697638561 12372346180605680023228921)
        ·
          refine ⟨9279259635454260017421691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12372346180605680023228921 9279259635454260017421691)
          ·
            refine ⟨13918889453181390026132537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279259635454260017421691 13918889453181390026132537)
            ·
              refine ⟨10439167089886042519599403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13918889453181390026132537 10439167089886042519599403)
              ·
                refine ⟨15658750634829063779399105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10439167089886042519599403 15658750634829063779399105)
                ·
                  refine ⟨11744062976121797834549329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15658750634829063779399105 11744062976121797834549329)
                  ·
                    refine ⟨8808047232091348375911997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11744062976121797834549329 8808047232091348375911997)
                    ·
                      refine ⟨3303017712034255640966999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8808047232091348375911997 3303017712034255640966999)
                      ·
                        rfl

theorem cell23_6432604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_6432604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432604 prefixEnd_6432604 := by exact prefixLift 6432604
  have htrace : WordTrace (prefixWord ++ tailWord_6432604) baseStart_6432604 baseEnd_6432604 := by
    simpa [prefixWord, tailWord_6432604, baseEnd_6432604] using wordTrace_append hprefix tailTrace_6432604
  have hstable : (prefixWord ++ tailWord_6432604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432604).length < 2 ^ (prefixWord ++ tailWord_6432604).sum := by decide
  have hdescent : baseEnd_6432604 < baseStart_6432604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432633 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 3, 6]
def baseStart_6432633 : Nat := 118140960795 + 6432633 * 2 ^ 59
def prefixEnd_6432633 : Nat := 4983230072969 + 3 ^ 40 * 6432633 * 2
def baseEnd_6432633 : Nat := 1101010867657745342501455

theorem tailTrace_6432633 : CollatzResearch.WordTrace tailWord_6432633 prefixEnd_6432633 1101010867657745342501455 := by
  unfold tailWord_6432633
  simp only [CollatzResearch.WordTrace]
  refine ⟨234617400104676722096998553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156411600069784481397999035 234617400104676722096998553)
  ·
    refine ⟨175963050078507541572748915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234617400104676722096998553 175963050078507541572748915)
    ·
      refine ⟨263944575117761312359123373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175963050078507541572748915 263944575117761312359123373)
      ·
        refine ⟨98979215669160492134671265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263944575117761312359123373 98979215669160492134671265)
        ·
          refine ⟨74234411751870369101003449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98979215669160492134671265 74234411751870369101003449)
          ·
            refine ⟨55675808813902776825752587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74234411751870369101003449 55675808813902776825752587)
            ·
              refine ⟨83513713220854165238628881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55675808813902776825752587 83513713220854165238628881)
              ·
                refine ⟨62635284915640623928971661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83513713220854165238628881 62635284915640623928971661)
                ·
                  refine ⟨23488231843365233973364373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62635284915640623928971661 23488231843365233973364373)
                  ·
                    refine ⟨1101010867657745342501455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23488231843365233973364373 1101010867657745342501455)
                    ·
                      rfl

theorem cell23_6432633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_6432633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432633 prefixEnd_6432633 := by exact prefixLift 6432633
  have htrace : WordTrace (prefixWord ++ tailWord_6432633) baseStart_6432633 baseEnd_6432633 := by
    simpa [prefixWord, tailWord_6432633, baseEnd_6432633] using wordTrace_append hprefix tailTrace_6432633
  have hstable : (prefixWord ++ tailWord_6432633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432633).length < 2 ^ (prefixWord ++ tailWord_6432633).sum := by decide
  have hdescent : baseEnd_6432633 < baseStart_6432633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432657 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 5, 2, 2]
def baseStart_6432657 : Nat := 118140960795 + 6432657 * 2 ^ 59
def prefixEnd_6432657 : Nat := 4983230072969 + 3 ^ 40 * 6432657 * 2
def baseEnd_6432657 : Nat := 3303044926508943933604255

theorem tailTrace_6432657 : CollatzResearch.WordTrace tailWord_6432657 prefixEnd_6432657 3303044926508943933604255 := by
  unfold tailWord_6432657
  simp only [CollatzResearch.WordTrace]
  refine ⟨234618275456589774195872225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156412183637726516130581483 234618275456589774195872225)
  ·
    refine ⟨175963706592442330646904169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234618275456589774195872225 175963706592442330646904169)
    ·
      refine ⟨131972779944331747985178127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175963706592442330646904169 131972779944331747985178127)
      ·
        refine ⟨197959169916497621977767191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131972779944331747985178127 197959169916497621977767191)
        ·
          refine ⟨296938754874746432966650787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197959169916497621977767191 296938754874746432966650787)
          ·
            refine ⟨445408132312119649449976181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296938754874746432966650787 445408132312119649449976181)
            ·
              refine ⟨41757012404261217135935267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 445408132312119649449976181 41757012404261217135935267)
              ·
                refine ⟨62635518606391825703902901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41757012404261217135935267 62635518606391825703902901)
                ·
                  refine ⟨5872079869349233659740897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62635518606391825703902901 5872079869349233659740897)
                  ·
                    refine ⟨4404059902011925244805673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5872079869349233659740897 4404059902011925244805673)
                    ·
                      refine ⟨3303044926508943933604255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404059902011925244805673 3303044926508943933604255)
                      ·
                        rfl

theorem cell23_6432657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 2, 2].length) (baseStart_6432657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432657 prefixEnd_6432657 := by exact prefixLift 6432657
  have htrace : WordTrace (prefixWord ++ tailWord_6432657) baseStart_6432657 baseEnd_6432657 := by
    simpa [prefixWord, tailWord_6432657, baseEnd_6432657] using wordTrace_append hprefix tailTrace_6432657
  have hstable : (prefixWord ++ tailWord_6432657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432657).length < 2 ^ (prefixWord ++ tailWord_6432657).sum := by decide
  have hdescent : baseEnd_6432657 < baseStart_6432657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432671 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 1, 5]
def baseStart_6432671 : Nat := 118140960795 + 6432671 * 2 ^ 59
def prefixEnd_6432671 : Nat := 4983230072969 + 3 ^ 40 * 6432671 * 2
def baseEnd_6432671 : Nat := 1101017371746035626276397

theorem tailTrace_6432671 : CollatzResearch.WordTrace tailWord_6432671 prefixEnd_6432671 1101017371746035626276397 := by
  unfold tailWord_6432671
  simp only [CollatzResearch.WordTrace]
  refine ⟨234618786078539054586881867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156412524052359369724587911 234618786078539054586881867)
  ·
    refine ⟨351928179117808581880322801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234618786078539054586881867 351928179117808581880322801)
    ·
      refine ⟨263946134338356436410242101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351928179117808581880322801 263946134338356436410242101)
      ·
        refine ⟨24744950094220915913460197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 263946134338356436410242101 24744950094220915913460197)
        ·
          refine ⟨4639678142666421733773787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24744950094220915913460197 4639678142666421733773787)
          ·
            refine ⟨6959517213999632600660681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639678142666421733773787 6959517213999632600660681)
            ·
              refine ⟨5219637910499724450495511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6959517213999632600660681 5219637910499724450495511)
              ·
                refine ⟨7829456865749586675743267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219637910499724450495511 7829456865749586675743267)
                ·
                  refine ⟨11744185298624380013614901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7829456865749586675743267 11744185298624380013614901)
                  ·
                    refine ⟨1101017371746035626276397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11744185298624380013614901 1101017371746035626276397)
                    ·
                      rfl

theorem cell23_6432671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 5].length) (baseStart_6432671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432671 prefixEnd_6432671 := by exact prefixLift 6432671
  have htrace : WordTrace (prefixWord ++ tailWord_6432671) baseStart_6432671 baseEnd_6432671 := by
    simpa [prefixWord, tailWord_6432671, baseEnd_6432671] using wordTrace_append hprefix tailTrace_6432671
  have hstable : (prefixWord ++ tailWord_6432671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432671).length < 2 ^ (prefixWord ++ tailWord_6432671).sum := by decide
  have hdescent : baseEnd_6432671 < baseStart_6432671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432674 : List Nat := [3, 3, 1, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_6432674 : Nat := 118140960795 + 6432674 * 2 ^ 59
def prefixEnd_6432674 : Nat := 4983230072969 + 3 ^ 40 * 6432674 * 2
def baseEnd_6432674 : Nat := 3303053655680070367091677

theorem tailTrace_6432674 : CollatzResearch.WordTrace tailWord_6432674 prefixEnd_6432674 3303053655680070367091677 := by
  unfold tailWord_6432674
  simp only [CollatzResearch.WordTrace]
  refine ⟨58654723874382046524810269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156412596998352124066160717 58654723874382046524810269)
  ·
    refine ⟨21995521452893267446803851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58654723874382046524810269 21995521452893267446803851)
    ·
      refine ⟨32993282179339901170205777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21995521452893267446803851 32993282179339901170205777)
      ·
        refine ⟨24744961634504925877654333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32993282179339901170205777 24744961634504925877654333)
        ·
          refine ⟨9279360612939347204120375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24744961634504925877654333 9279360612939347204120375)
          ·
            refine ⟨13919040919409020806180563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279360612939347204120375 13919040919409020806180563)
            ·
              refine ⟨20878561379113531209270845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13919040919409020806180563 20878561379113531209270845)
              ·
                refine ⟨7829460517167574203476567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20878561379113531209270845 7829460517167574203476567)
                ·
                  refine ⟨11744190775751361305214851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7829460517167574203476567 11744190775751361305214851)
                  ·
                    refine ⟨17616286163627041957822277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11744190775751361305214851 17616286163627041957822277)
                    ·
                      refine ⟨3303053655680070367091677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17616286163627041957822277 3303053655680070367091677)
                      ·
                        rfl

theorem cell23_6432674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_6432674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432674 prefixEnd_6432674 := by exact prefixLift 6432674
  have htrace : WordTrace (prefixWord ++ tailWord_6432674) baseStart_6432674 baseEnd_6432674 := by
    simpa [prefixWord, tailWord_6432674, baseEnd_6432674] using wordTrace_append hprefix tailTrace_6432674
  have hstable : (prefixWord ++ tailWord_6432674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432674).length < 2 ^ (prefixWord ++ tailWord_6432674).sum := by decide
  have hdescent : baseEnd_6432674 < baseStart_6432674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432690 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_6432690 : Nat := 118140960795 + 6432690 * 2 ^ 59
def prefixEnd_6432690 : Nat := 4983230072969 + 3 ^ 40 * 6432690 * 2
def baseEnd_6432690 : Nat := 3303061871370542304491603

theorem tailTrace_6432690 : CollatzResearch.WordTrace tailWord_6432690 prefixEnd_6432690 3303061871370542304491603 := by
  unfold tailWord_6432690
  simp only [CollatzResearch.WordTrace]
  refine ⟨58654869766367555207955881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156412986043646813887882349 58654869766367555207955881)
  ·
    refine ⟨43991152324775666405966911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58654869766367555207955881 43991152324775666405966911)
    ·
      refine ⟨65986728487163499608950367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43991152324775666405966911 65986728487163499608950367)
      ·
        refine ⟨98980092730745249413425551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65986728487163499608950367 98980092730745249413425551)
        ·
          refine ⟨148470139096117874120138327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98980092730745249413425551 148470139096117874120138327)
          ·
            refine ⟨222705208644176811180207491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148470139096117874120138327 222705208644176811180207491)
            ·
              refine ⟨334057812966265216770311237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222705208644176811180207491 334057812966265216770311237)
              ·
                refine ⟨62635839931174728144433357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334057812966265216770311237 62635839931174728144433357)
                ·
                  refine ⟨23488439974190523054162509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62635839931174728144433357 23488439974190523054162509)
                  ·
                    refine ⟨8808164990321446145310941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23488439974190523054162509 8808164990321446145310941)
                    ·
                      refine ⟨3303061871370542304491603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8808164990321446145310941 3303061871370542304491603)
                      ·
                        rfl

theorem cell23_6432690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_6432690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432690 prefixEnd_6432690 := by exact prefixLift 6432690
  have htrace : WordTrace (prefixWord ++ tailWord_6432690) baseStart_6432690 baseEnd_6432690 := by
    simpa [prefixWord, tailWord_6432690, baseEnd_6432690] using wordTrace_append hprefix tailTrace_6432690
  have hstable : (prefixWord ++ tailWord_6432690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432690).length < 2 ^ (prefixWord ++ tailWord_6432690).sum := by decide
  have hdescent : baseEnd_6432690 < baseStart_6432690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432760 : List Nat := [2, 1, 2, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_6432760 : Nat := 118140960795 + 6432760 * 2 ^ 59
def prefixEnd_6432760 : Nat := 4983230072969 + 3 ^ 40 * 6432760 * 2
def baseEnd_6432760 : Nat := 3303097815016357030616281

theorem tailTrace_6432760 : CollatzResearch.WordTrace tailWord_6432760 prefixEnd_6432760 3303097815016357030616281 := by
  unfold tailWord_6432760
  simp only [CollatzResearch.WordTrace]
  refine ⟨117311016087608311393435867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156414688116811081857914489 117311016087608311393435867)
  ·
    refine ⟨175966524131412467090153801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117311016087608311393435867 175966524131412467090153801)
    ·
      refine ⟨131974893098559350317615351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175966524131412467090153801 131974893098559350317615351)
      ·
        refine ⟨197962339647839025476423027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131974893098559350317615351 197962339647839025476423027)
        ·
          refine ⟨296943509471758538214634541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197962339647839025476423027 296943509471758538214634541)
          ·
            refine ⟨111353816051909451830487953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296943509471758538214634541 111353816051909451830487953)
            ·
              refine ⟨83515362038932088872865965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111353816051909451830487953 83515362038932088872865965)
              ·
                refine ⟨31318260764599533327324737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83515362038932088872865965 31318260764599533327324737)
                ·
                  refine ⟨23488695573449649995493553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31318260764599533327324737 23488695573449649995493553)
                  ·
                    refine ⟨17616521680087237496620165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23488695573449649995493553 17616521680087237496620165)
                    ·
                      refine ⟨3303097815016357030616281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17616521680087237496620165 3303097815016357030616281)
                      ·
                        rfl

theorem cell23_6432760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_6432760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432760 prefixEnd_6432760 := by exact prefixLift 6432760
  have htrace : WordTrace (prefixWord ++ tailWord_6432760) baseStart_6432760 baseEnd_6432760 := by
    simpa [prefixWord, tailWord_6432760, baseEnd_6432760] using wordTrace_append hprefix tailTrace_6432760
  have hstable : (prefixWord ++ tailWord_6432760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432760).length < 2 ^ (prefixWord ++ tailWord_6432760).sum := by decide
  have hdescent : baseEnd_6432760 < baseStart_6432760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432814 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_6432814 : Nat := 118140960795 + 6432814 * 2 ^ 59
def prefixEnd_6432814 : Nat := 4983230072969 + 3 ^ 40 * 6432814 * 2
def baseEnd_6432814 : Nat := 3303125542971699819341033

theorem tailTrace_6432814 : CollatzResearch.WordTrace tailWord_6432814 prefixEnd_6432814 3303125542971699819341033 := by
  unfold tailWord_6432814
  simp only [CollatzResearch.WordTrace]
  refine ⟨29328000214627623751167187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156416001144680660006224997 29328000214627623751167187)
  ·
    refine ⟨43992000321941435626750781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29328000214627623751167187 43992000321941435626750781)
    ·
      refine ⟨16497000120728038360031543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43992000321941435626750781 16497000120728038360031543)
      ·
        refine ⟨24745500181092057540047315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16497000120728038360031543 24745500181092057540047315)
        ·
          refine ⟨37118250271638086310070973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24745500181092057540047315 37118250271638086310070973)
          ·
            refine ⟨13919343851864282366276615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37118250271638086310070973 13919343851864282366276615)
            ·
              refine ⟨20879015777796423549414923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13919343851864282366276615 20879015777796423549414923)
              ·
                refine ⟨31318523666694635324122385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20879015777796423549414923 31318523666694635324122385)
                ·
                  refine ⟨23488892750020976493091789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31318523666694635324122385 23488892750020976493091789)
                  ·
                    refine ⟨8808334781257866184909421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23488892750020976493091789 8808334781257866184909421)
                    ·
                      refine ⟨3303125542971699819341033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8808334781257866184909421 3303125542971699819341033)
                      ·
                        rfl

theorem cell23_6432814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_6432814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432814 prefixEnd_6432814 := by exact prefixLift 6432814
  have htrace : WordTrace (prefixWord ++ tailWord_6432814) baseStart_6432814 baseEnd_6432814 := by
    simpa [prefixWord, tailWord_6432814, baseEnd_6432814] using wordTrace_append hprefix tailTrace_6432814
  have hstable : (prefixWord ++ tailWord_6432814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432814).length < 2 ^ (prefixWord ++ tailWord_6432814).sum := by decide
  have hdescent : baseEnd_6432814 < baseStart_6432814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432837 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 3, 6, 2]
def baseStart_6432837 : Nat := 118140960795 + 6432837 * 2 ^ 59
def prefixEnd_6432837 : Nat := 4983230072969 + 3 ^ 40 * 6432837 * 2
def baseEnd_6432837 : Nat := 3303137353026753229353427

theorem tailTrace_6432837 : CollatzResearch.WordTrace tailWord_6432837 prefixEnd_6432837 3303137353026753229353427 := by
  unfold tailWord_6432837
  simp only [CollatzResearch.WordTrace]
  refine ⟨234624840595937664937424765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156416560397291776624949843 234624840595937664937424765)
  ·
    refine ⟨87984315223476624351534287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234624840595937664937424765 87984315223476624351534287)
    ·
      refine ⟨131976472835214936527301431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87984315223476624351534287 131976472835214936527301431)
      ·
        refine ⟨197964709252822404790952147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131976472835214936527301431 197964709252822404790952147)
        ·
          refine ⟨296947063879233607186428221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197964709252822404790952147 296947063879233607186428221)
          ·
            refine ⟨111355148954712602694910583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296947063879233607186428221 111355148954712602694910583)
            ·
              refine ⟨167032723432068904042365875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111355148954712602694910583 167032723432068904042365875)
              ·
                refine ⟨250549085148103356063548813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167032723432068904042365875 250549085148103356063548813)
                ·
                  refine ⟨93955906930538758523830805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250549085148103356063548813 93955906930538758523830805)
                  ·
                    refine ⟨4404183137369004305804569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93955906930538758523830805 4404183137369004305804569)
                    ·
                      refine ⟨3303137353026753229353427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404183137369004305804569 3303137353026753229353427)
                      ·
                        rfl

theorem cell23_6432837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 6, 2].length) (baseStart_6432837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432837 prefixEnd_6432837 := by exact prefixLift 6432837
  have htrace : WordTrace (prefixWord ++ tailWord_6432837) baseStart_6432837 baseEnd_6432837 := by
    simpa [prefixWord, tailWord_6432837, baseEnd_6432837] using wordTrace_append hprefix tailTrace_6432837
  have hstable : (prefixWord ++ tailWord_6432837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432837).length < 2 ^ (prefixWord ++ tailWord_6432837).sum := by decide
  have hdescent : baseEnd_6432837 < baseStart_6432837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432840 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_6432840 : Nat := 118140960795 + 6432840 * 2 ^ 59
def prefixEnd_6432840 : Nat := 4983230072969 + 3 ^ 40 * 6432840 * 2
def baseEnd_6432840 : Nat := 3303138893468716717615913

theorem tailTrace_6432840 : CollatzResearch.WordTrace tailWord_6432840 prefixEnd_6432840 3303138893468716717615913 := by
  unfold tailWord_6432840
  simp only [CollatzResearch.WordTrace]
  refine ⟨117312475007463398224891987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156416633343284530966522649 117312475007463398224891987)
  ·
    refine ⟨175968712511195097337337981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117312475007463398224891987 175968712511195097337337981)
    ·
      refine ⟨65988267191698161501501743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175968712511195097337337981 65988267191698161501501743)
      ·
        refine ⟨98982400787547242252252615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65988267191698161501501743 98982400787547242252252615)
        ·
          refine ⟨148473601181320863378378923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98982400787547242252252615 148473601181320863378378923)
          ·
            refine ⟨222710401771981295067568385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148473601181320863378378923 222710401771981295067568385)
            ·
              refine ⟨167032801328985971300676289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222710401771981295067568385 167032801328985971300676289)
              ·
                refine ⟨125274600996739478475507217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167032801328985971300676289 125274600996739478475507217)
                ·
                  refine ⟨93955950747554608856630413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125274600996739478475507217 93955950747554608856630413)
                  ·
                    refine ⟨35233481530332978321236405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93955950747554608856630413 35233481530332978321236405)
                    ·
                      refine ⟨3303138893468716717615913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35233481530332978321236405 3303138893468716717615913)
                      ·
                        rfl

theorem cell23_6432840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_6432840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432840 prefixEnd_6432840 := by exact prefixLift 6432840
  have htrace : WordTrace (prefixWord ++ tailWord_6432840) baseStart_6432840 baseEnd_6432840 := by
    simpa [prefixWord, tailWord_6432840, baseEnd_6432840] using wordTrace_append hprefix tailTrace_6432840
  have hstable : (prefixWord ++ tailWord_6432840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432840).length < 2 ^ (prefixWord ++ tailWord_6432840).sum := by decide
  have hdescent : baseEnd_6432840 < baseStart_6432840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432857 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 4, 2, 3]
def baseStart_6432857 : Nat := 118140960795 + 6432857 * 2 ^ 59
def prefixEnd_6432857 : Nat := 4983230072969 + 3 ^ 40 * 6432857 * 2
def baseEnd_6432857 : Nat := 3303147622639843151103335

theorem tailTrace_6432857 : CollatzResearch.WordTrace tailWord_6432857 prefixEnd_6432857 3303147622639843151103335 := by
  unfold tailWord_6432857
  simp only [CollatzResearch.WordTrace]
  refine ⟨234625570055865208353152825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156417046703910138902101883 234625570055865208353152825)
  ·
    refine ⟨175969177541898906264864619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234625570055865208353152825 175969177541898906264864619)
    ·
      refine ⟨263953766312848359397296929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175969177541898906264864619 263953766312848359397296929)
      ·
        refine ⟨197965324734636269547972697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263953766312848359397296929 197965324734636269547972697)
        ·
          refine ⟨148473993550977202160979523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197965324734636269547972697 148473993550977202160979523)
          ·
            refine ⟨222710990326465803241469285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148473993550977202160979523 222710990326465803241469285)
            ·
              refine ⟨41758310686212338107775491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222710990326465803241469285 41758310686212338107775491)
              ·
                refine ⟨62637466029318507161663237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41758310686212338107775491 62637466029318507161663237)
                ·
                  refine ⟨11744524880497220092811857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62637466029318507161663237 11744524880497220092811857)
                  ·
                    refine ⟨8808393660372915069608893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11744524880497220092811857 8808393660372915069608893)
                    ·
                      refine ⟨3303147622639843151103335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8808393660372915069608893 3303147622639843151103335)
                      ·
                        rfl

theorem cell23_6432857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_6432857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432857 prefixEnd_6432857 := by exact prefixLift 6432857
  have htrace : WordTrace (prefixWord ++ tailWord_6432857) baseStart_6432857 baseEnd_6432857 := by
    simpa [prefixWord, tailWord_6432857, baseEnd_6432857] using wordTrace_append hprefix tailTrace_6432857
  have hstable : (prefixWord ++ tailWord_6432857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432857).length < 2 ^ (prefixWord ++ tailWord_6432857).sum := by decide
  have hdescent : baseEnd_6432857 < baseStart_6432857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432864 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 3, 4]
def baseStart_6432864 : Nat := 118140960795 + 6432864 * 2 ^ 59
def prefixEnd_6432864 : Nat := 4983230072969 + 3 ^ 40 * 6432864 * 2
def baseEnd_6432864 : Nat := 1101050405668141541238601

theorem tailTrace_6432864 : CollatzResearch.WordTrace tailWord_6432864 prefixEnd_6432864 1101050405668141541238601 := by
  unfold tailWord_6432864
  simp only [CollatzResearch.WordTrace]
  refine ⟨117312912683419924274328823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156417216911226565699105097 117312912683419924274328823)
  ·
    refine ⟨175969369025129886411493235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117312912683419924274328823 175969369025129886411493235)
    ·
      refine ⟨263954053537694829617239853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175969369025129886411493235 263954053537694829617239853)
      ·
        refine ⟨98982770076635561106464945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263954053537694829617239853 98982770076635561106464945)
        ·
          refine ⟨74237077557476670829848709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98982770076635561106464945 74237077557476670829848709)
          ·
            refine ⟨13919452042026875780596633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74237077557476670829848709 13919452042026875780596633)
            ·
              refine ⟨10439589031520156835447475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13919452042026875780596633 10439589031520156835447475)
              ·
                refine ⟨15659383547280235253171213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10439589031520156835447475 15659383547280235253171213)
                ·
                  refine ⟨5872268830230088219939205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15659383547280235253171213 5872268830230088219939205)
                  ·
                    refine ⟨1101050405668141541238601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5872268830230088219939205 1101050405668141541238601)
                    ·
                      rfl

theorem cell23_6432864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 3, 4].length) (baseStart_6432864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432864 prefixEnd_6432864 := by exact prefixLift 6432864
  have htrace : WordTrace (prefixWord ++ tailWord_6432864) baseStart_6432864 baseEnd_6432864 := by
    simpa [prefixWord, tailWord_6432864, baseEnd_6432864] using wordTrace_append hprefix tailTrace_6432864
  have hstable : (prefixWord ++ tailWord_6432864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432864).length < 2 ^ (prefixWord ++ tailWord_6432864).sum := by decide
  have hdescent : baseEnd_6432864 < baseStart_6432864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432890 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_6432890 : Nat := 118140960795 + 6432890 * 2 ^ 59
def prefixEnd_6432890 : Nat := 4983230072969 + 3 ^ 40 * 6432890 * 2
def baseEnd_6432890 : Nat := 1101054855833813840663561

theorem tailTrace_6432890 : CollatzResearch.WordTrace tailWord_6432890 prefixEnd_6432890 1101054855833813840663561 := by
  unfold tailWord_6432890
  simp only [CollatzResearch.WordTrace]
  refine ⟨58656693416186413747276031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156417849109830436659402749 58656693416186413747276031)
  ·
    refine ⟨87985040124279620620914047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58656693416186413747276031 87985040124279620620914047)
    ·
      refine ⟨131977560186419430931371071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87985040124279620620914047 131977560186419430931371071)
      ·
        refine ⟨197966340279629146397056607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131977560186419430931371071 197966340279629146397056607)
        ·
          refine ⟨296949510419443719595584911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197966340279629146397056607 296949510419443719595584911)
          ·
            refine ⟨445424265629165579393377367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296949510419443719595584911 445424265629165579393377367)
            ·
              refine ⟨668136398443748369090066051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445424265629165579393377367 668136398443748369090066051)
              ·
                refine ⟨1002204597665622553635099077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668136398443748369090066051 1002204597665622553635099077)
                ·
                  refine ⟨187913362062304228806581077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1002204597665622553635099077 187913362062304228806581077)
                  ·
                    refine ⟨1101054855833813840663561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 187913362062304228806581077 1101054855833813840663561)
                    ·
                      rfl

theorem cell23_6432890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_6432890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432890 prefixEnd_6432890 := by exact prefixLift 6432890
  have htrace : WordTrace (prefixWord ++ tailWord_6432890) baseStart_6432890 baseEnd_6432890 := by
    simpa [prefixWord, tailWord_6432890, baseEnd_6432890] using wordTrace_append hprefix tailTrace_6432890
  have hstable : (prefixWord ++ tailWord_6432890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432890).length < 2 ^ (prefixWord ++ tailWord_6432890).sum := by decide
  have hdescent : baseEnd_6432890 < baseStart_6432890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432921 : List Nat := [1, 2, 1, 2, 1, 2, 1, 8, 1, 1, 3]
def baseStart_6432921 : Nat := 118140960795 + 6432921 * 2 ^ 59
def prefixEnd_6432921 : Nat := 4983230072969 + 3 ^ 40 * 6432921 * 2
def baseEnd_6432921 : Nat := 3303180485401730900703041

theorem tailTrace_6432921 : CollatzResearch.WordTrace tailWord_6432921 prefixEnd_6432921 3303180485401730900703041 := by
  unfold tailWord_6432921
  simp only [CollatzResearch.WordTrace]
  refine ⟨234627904327633347283482617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156418602885088898188988411 234627904327633347283482617)
  ·
    refine ⟨175970928245725010462611963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234627904327633347283482617 175970928245725010462611963)
    ·
      refine ⟨263956392368587515693917945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175970928245725010462611963 263956392368587515693917945)
      ·
        refine ⟨197967294276440636770438459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263956392368587515693917945 197967294276440636770438459)
        ·
          refine ⟨296950941414660955155657689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197967294276440636770438459 296950941414660955155657689)
          ·
            refine ⟨222713206060995716366743267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296950941414660955155657689 222713206060995716366743267)
            ·
              refine ⟨334069809091493574550114901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222713206060995716366743267 334069809091493574550114901)
              ·
                refine ⟨3914880575290940326759159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 334069809091493574550114901 3914880575290940326759159)
                ·
                  refine ⟨5872320862936410490138739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3914880575290940326759159 5872320862936410490138739)
                  ·
                    refine ⟨8808481294404615735208109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5872320862936410490138739 8808481294404615735208109)
                    ·
                      refine ⟨3303180485401730900703041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8808481294404615735208109 3303180485401730900703041)
                      ·
                        rfl

theorem cell23_6432921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 1, 1, 3].length) (baseStart_6432921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432921 prefixEnd_6432921 := by exact prefixLift 6432921
  have htrace : WordTrace (prefixWord ++ tailWord_6432921) baseStart_6432921 baseEnd_6432921 := by
    simpa [prefixWord, tailWord_6432921, baseEnd_6432921] using wordTrace_append hprefix tailTrace_6432921
  have hstable : (prefixWord ++ tailWord_6432921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432921).length < 2 ^ (prefixWord ++ tailWord_6432921).sum := by decide
  have hdescent : baseEnd_6432921 < baseStart_6432921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432941 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_6432941 : Nat := 118140960795 + 6432941 * 2 ^ 59
def prefixEnd_6432941 : Nat := 4983230072969 + 3 ^ 40 * 6432941 * 2
def baseEnd_6432941 : Nat := 1101063585004940274150983

theorem tailTrace_6432941 : CollatzResearch.WordTrace tailWord_6432941 prefixEnd_6432941 1101063585004940274150983 := by
  unfold tailWord_6432941
  simp only [CollatzResearch.WordTrace]
  refine ⟨234628633787560890699210677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156419089191707260466140451 234628633787560890699210677)
  ·
    refine ⟨21996434417583833503051001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234628633787560890699210677 21996434417583833503051001)
    ·
      refine ⟨16497325813187875127288251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21996434417583833503051001 16497325813187875127288251)
      ·
        refine ⟨24745988719781812690932377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16497325813187875127288251 24745988719781812690932377)
        ·
          refine ⟨18559491539836359518199283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24745988719781812690932377 18559491539836359518199283)
          ·
            refine ⟨27839237309754539277298925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18559491539836359518199283 27839237309754539277298925)
            ·
              refine ⟨10439713991157952228987097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27839237309754539277298925 10439713991157952228987097)
              ·
                refine ⟨7829785493368464171740323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10439713991157952228987097 7829785493368464171740323)
                ·
                  refine ⟨11744678240052696257610485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7829785493368464171740323 11744678240052696257610485)
                  ·
                    refine ⟨1101063585004940274150983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11744678240052696257610485 1101063585004940274150983)
                    ·
                      rfl

theorem cell23_6432941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_6432941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432941 prefixEnd_6432941 := by exact prefixLift 6432941
  have htrace : WordTrace (prefixWord ++ tailWord_6432941) baseStart_6432941 baseEnd_6432941 := by
    simpa [prefixWord, tailWord_6432941, baseEnd_6432941] using wordTrace_append hprefix tailTrace_6432941
  have hstable : (prefixWord ++ tailWord_6432941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432941).length < 2 ^ (prefixWord ++ tailWord_6432941).sum := by decide
  have hdescent : baseEnd_6432941 < baseStart_6432941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432958 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_6432958 : Nat := 118140960795 + 6432958 * 2 ^ 59
def prefixEnd_6432958 : Nat := 4983230072969 + 3 ^ 40 * 6432958 * 2
def baseEnd_6432958 : Nat := 1101066494728649085313457

theorem tailTrace_6432958 : CollatzResearch.WordTrace tailWord_6432958 prefixEnd_6432958 1101066494728649085313457 := by
  unfold tailWord_6432958
  simp only [CollatzResearch.WordTrace]
  refine ⟨29328656728562412825322441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156419502552332868401719685 29328656728562412825322441)
  ·
    refine ⟨21996492546421809618991831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29328656728562412825322441 21996492546421809618991831)
    ·
      refine ⟨32994738819632714428487747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21996492546421809618991831 32994738819632714428487747)
      ·
        refine ⟨49492108229449071642731621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32994738819632714428487747 49492108229449071642731621)
        ·
          refine ⟨9279770293021700933012179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49492108229449071642731621 9279770293021700933012179)
          ·
            refine ⟨13919655439532551399518269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279770293021700933012179 13919655439532551399518269)
            ·
              refine ⟨5219870789824706774819351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13919655439532551399518269 5219870789824706774819351)
              ·
                refine ⟨7829806184737060162229027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5219870789824706774819351 7829806184737060162229027)
                ·
                  refine ⟨11744709277105590243343541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7829806184737060162229027 11744709277105590243343541)
                  ·
                    refine ⟨1101066494728649085313457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11744709277105590243343541 1101066494728649085313457)
                    ·
                      rfl

theorem cell23_6432958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_6432958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432958 prefixEnd_6432958 := by exact prefixLift 6432958
  have htrace : WordTrace (prefixWord ++ tailWord_6432958) baseStart_6432958 baseEnd_6432958 := by
    simpa [prefixWord, tailWord_6432958, baseEnd_6432958] using wordTrace_append hprefix tailTrace_6432958
  have hstable : (prefixWord ++ tailWord_6432958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432958).length < 2 ^ (prefixWord ++ tailWord_6432958).sum := by decide
  have hdescent : baseEnd_6432958 < baseStart_6432958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432984 : List Nat := [2, 1, 2, 2, 4, 3, 1, 8]
def baseStart_6432984 : Nat := 118140960795 + 6432984 * 2 ^ 59
def prefixEnd_6432984 : Nat := 4983230072969 + 3 ^ 40 * 6432984 * 2
def baseEnd_6432984 : Nat := 122341216099369042748713

theorem tailTrace_6432984 : CollatzResearch.WordTrace tailWord_6432984 prefixEnd_6432984 122341216099369042748713 := by
  unfold tailWord_6432984
  simp only [CollatzResearch.WordTrace]
  refine ⟨117315101063202554521513003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156420134750936739362017337 117315101063202554521513003)
  ·
    refine ⟨175972651594803831782269505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117315101063202554521513003 175972651594803831782269505)
    ·
      refine ⟨131979488696102873836702129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175972651594803831782269505 131979488696102873836702129)
      ·
        refine ⟨98984616522077155377526597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131979488696102873836702129 98984616522077155377526597)
        ·
          refine ⟨18559615597889466633286237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98984616522077155377526597 18559615597889466633286237)
          ·
            refine ⟨6959855849208549987482339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18559615597889466633286237 6959855849208549987482339)
            ·
              refine ⟨10439783773812824981223509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6959855849208549987482339 10439783773812824981223509)
              ·
                refine ⟨122341216099369042748713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10439783773812824981223509 122341216099369042748713)
                ·
                  rfl

theorem cell23_6432984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 8].length) (baseStart_6432984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432984 prefixEnd_6432984 := by exact prefixLift 6432984
  have htrace : WordTrace (prefixWord ++ tailWord_6432984) baseStart_6432984 baseEnd_6432984 := by
    simpa [prefixWord, tailWord_6432984, baseEnd_6432984] using wordTrace_append hprefix tailTrace_6432984
  have hstable : (prefixWord ++ tailWord_6432984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432984).length < 2 ^ (prefixWord ++ tailWord_6432984).sum := by decide
  have hdescent : baseEnd_6432984 < baseStart_6432984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432988 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 1, 6]
def baseStart_6432988 : Nat := 118140960795 + 6432988 * 2 ^ 59
def prefixEnd_6432988 : Nat := 4983230072969 + 3 ^ 40 * 6432988 * 2
def baseEnd_6432988 : Nat := 1101071629535194046188411

theorem tailTrace_6432988 : CollatzResearch.WordTrace tailWord_6432988 prefixEnd_6432988 1101071629535194046188411 := by
  unfold tailWord_6432988
  simp only [CollatzResearch.WordTrace]
  refine ⟨117315174009195308863085809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156420232012260411817447745 117315174009195308863085809)
  ·
    refine ⟨87986380506896481647314357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117315174009195308863085809 87986380506896481647314357)
    ·
      refine ⟨8248723172521545154435721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87986380506896481647314357 8248723172521545154435721)
      ·
        refine ⟨6186542379391158865826791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8248723172521545154435721 6186542379391158865826791)
        ·
          refine ⟨9279813569086738298740187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186542379391158865826791 9279813569086738298740187)
          ·
            refine ⟨13919720353630107448110281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279813569086738298740187 13919720353630107448110281)
            ·
              refine ⟨10439790265222580586082711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13919720353630107448110281 10439790265222580586082711)
              ·
                refine ⟨15659685397833870879124067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10439790265222580586082711 15659685397833870879124067)
                ·
                  refine ⟨23489528096750806318686101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15659685397833870879124067 23489528096750806318686101)
                  ·
                    refine ⟨1101071629535194046188411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23489528096750806318686101 1101071629535194046188411)
                    ·
                      rfl

theorem cell23_6432988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_6432988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432988 prefixEnd_6432988 := by exact prefixLift 6432988
  have htrace : WordTrace (prefixWord ++ tailWord_6432988) baseStart_6432988 baseEnd_6432988 := by
    simpa [prefixWord, tailWord_6432988, baseEnd_6432988] using wordTrace_append hprefix tailTrace_6432988
  have hstable : (prefixWord ++ tailWord_6432988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432988).length < 2 ^ (prefixWord ++ tailWord_6432988).sum := by decide
  have hdescent : baseEnd_6432988 < baseStart_6432988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6432995 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 3, 2, 2]
def baseStart_6432995 : Nat := 118140960795 + 6432995 * 2 ^ 59
def prefixEnd_6432995 : Nat := 4983230072969 + 3 ^ 40 * 6432995 * 2
def baseEnd_6432995 : Nat := 3303218482970163611177701

theorem tailTrace_6432995 : CollatzResearch.WordTrace tailWord_6432995 prefixEnd_6432995 3303218482970163611177701 := by
  unfold tailWord_6432995
  simp only [CollatzResearch.WordTrace]
  refine ⟨234630603329365257921676439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156420402219576838614450959 234630603329365257921676439)
  ·
    refine ⟨351945904994047886882514659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234630603329365257921676439 351945904994047886882514659)
    ·
      refine ⟨527918857491071830323771989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351945904994047886882514659 527918857491071830323771989)
      ·
        refine ⟨6186549111223498011606703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 527918857491071830323771989 6186549111223498011606703)
        ·
          refine ⟨9279823666835247017410055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186549111223498011606703 9279823666835247017410055)
          ·
            refine ⟨13919735500252870526115083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279823666835247017410055 13919735500252870526115083)
            ·
              refine ⟨20879603250379305789172625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13919735500252870526115083 20879603250379305789172625)
              ·
                refine ⟨15659702437784479341879469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20879603250379305789172625 15659702437784479341879469)
                ·
                  refine ⟨5872388414169179753204801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15659702437784479341879469 5872388414169179753204801)
                  ·
                    refine ⟨4404291310626884814903601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5872388414169179753204801 4404291310626884814903601)
                    ·
                      refine ⟨3303218482970163611177701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404291310626884814903601 3303218482970163611177701)
                      ·
                        rfl

theorem cell23_6432995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_6432995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6432995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6432995 prefixEnd_6432995 := by exact prefixLift 6432995
  have htrace : WordTrace (prefixWord ++ tailWord_6432995) baseStart_6432995 baseEnd_6432995 := by
    simpa [prefixWord, tailWord_6432995, baseEnd_6432995] using wordTrace_append hprefix tailTrace_6432995
  have hstable : (prefixWord ++ tailWord_6432995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6432995).length < 2 ^ (prefixWord ++ tailWord_6432995).sum := by decide
  have hdescent : baseEnd_6432995 < baseStart_6432995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6432995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433017 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 4]
def baseStart_6433017 : Nat := 118140960795 + 6433017 * 2 ^ 59
def prefixEnd_6433017 : Nat := 4983230072969 + 3 ^ 40 * 6433017 * 2
def baseEnd_6433017 : Nat := 3303229779544562525102599

theorem tailTrace_6433017 : CollatzResearch.WordTrace tailWord_6433017 prefixEnd_6433017 3303229779544562525102599 := by
  unfold tailWord_6433017
  simp only [CollatzResearch.WordTrace]
  refine ⟨234631405735285555678977305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156420937156857037119318203 234631405735285555678977305)
  ·
    refine ⟨175973554301464166759232979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234631405735285555678977305 175973554301464166759232979)
    ·
      refine ⟨263960331452196250138849469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175973554301464166759232979 263960331452196250138849469)
      ·
        refine ⟨98985124294573593802068551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263960331452196250138849469 98985124294573593802068551)
        ·
          refine ⟨148477686441860390703102827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98985124294573593802068551 148477686441860390703102827)
          ·
            refine ⟨222716529662790586054654241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148477686441860390703102827 222716529662790586054654241)
            ·
              refine ⟨167037397247092939540990681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222716529662790586054654241 167037397247092939540990681)
              ·
                refine ⟨125278047935319704655743011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167037397247092939540990681 125278047935319704655743011)
                ·
                  refine ⟨187917071902979556983614517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125278047935319704655743011 187917071902979556983614517)
                  ·
                    refine ⟨17617225490904333467213861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 187917071902979556983614517 17617225490904333467213861)
                    ·
                      refine ⟨3303229779544562525102599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17617225490904333467213861 3303229779544562525102599)
                      ·
                        rfl

theorem cell23_6433017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_6433017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433017 prefixEnd_6433017 := by exact prefixLift 6433017
  have htrace : WordTrace (prefixWord ++ tailWord_6433017) baseStart_6433017 baseEnd_6433017 := by
    simpa [prefixWord, tailWord_6433017, baseEnd_6433017] using wordTrace_append hprefix tailTrace_6433017
  have hstable : (prefixWord ++ tailWord_6433017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433017).length < 2 ^ (prefixWord ++ tailWord_6433017).sum := by decide
  have hdescent : baseEnd_6433017 < baseStart_6433017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433027 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 4, 6]
def baseStart_6433027 : Nat := 118140960795 + 6433027 * 2 ^ 59
def prefixEnd_6433027 : Nat := 4983230072969 + 3 ^ 40 * 6433027 * 2
def baseEnd_6433027 : Nat := 1101078304783702495325851

theorem tailTrace_6433027 : CollatzResearch.WordTrace tailWord_6433027 prefixEnd_6433027 1101078304783702495325851 := by
  unfold tailWord_6433027
  simp only [CollatzResearch.WordTrace]
  refine ⟨234631770465249327386841335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156421180310166218257894223 234631770465249327386841335)
  ·
    refine ⟨351947655697873991080262003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234631770465249327386841335 351947655697873991080262003)
    ·
      refine ⟨527921483546810986620393005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351947655697873991080262003 527921483546810986620393005)
      ·
        refine ⟨197970556330054119982647377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 527921483546810986620393005 197970556330054119982647377)
        ·
          refine ⟨148477917247540589986985533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197970556330054119982647377 148477917247540589986985533)
          ·
            refine ⟨55679218967827721245119575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148477917247540589986985533 55679218967827721245119575)
            ·
              refine ⟨83518828451741581867679363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55679218967827721245119575 83518828451741581867679363)
              ·
                refine ⟨125278242677612372801519045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83518828451741581867679363 125278242677612372801519045)
                ·
                  refine ⟨23489670502052319900284821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125278242677612372801519045 23489670502052319900284821)
                  ·
                    refine ⟨1101078304783702495325851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23489670502052319900284821 1101078304783702495325851)
                    ·
                      rfl

theorem cell23_6433027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 6].length) (baseStart_6433027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433027 prefixEnd_6433027 := by exact prefixLift 6433027
  have htrace : WordTrace (prefixWord ++ tailWord_6433027) baseStart_6433027 baseEnd_6433027 := by
    simpa [prefixWord, tailWord_6433027, baseEnd_6433027] using wordTrace_append hprefix tailTrace_6433027
  have hstable : (prefixWord ++ tailWord_6433027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433027).length < 2 ^ (prefixWord ++ tailWord_6433027).sum := by decide
  have hdescent : baseEnd_6433027 < baseStart_6433027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433028 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_6433028 : Nat := 118140960795 + 6433028 * 2 ^ 59
def prefixEnd_6433028 : Nat := 4983230072969 + 3 ^ 40 * 6433028 * 2
def baseEnd_6433028 : Nat := 3303235427831761982065049

theorem tailTrace_6433028 : CollatzResearch.WordTrace tailWord_6433028 prefixEnd_6433028 3303235427831761982065049 := by
  unfold tailWord_6433028
  simp only [CollatzResearch.WordTrace]
  refine ⟨117315903469122852278813869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156421204625497136371751825 117315903469122852278813869)
  ·
    refine ⟨43993463800921069604555201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117315903469122852278813869 43993463800921069604555201)
    ·
      refine ⟨32995097850690802203416401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43993463800921069604555201 32995097850690802203416401)
      ·
        refine ⟨24746323388018101652562301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32995097850690802203416401 24746323388018101652562301)
        ·
          refine ⟨9279871270506788119710863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24746323388018101652562301 9279871270506788119710863)
          ·
            refine ⟨13919806905760182179566295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279871270506788119710863 13919806905760182179566295)
            ·
              refine ⟨20879710358640273269349443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13919806905760182179566295 20879710358640273269349443)
              ·
                refine ⟨31319565537960409904024165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20879710358640273269349443 31319565537960409904024165)
                ·
                  refine ⟨5872418538367576857004531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31319565537960409904024165 5872418538367576857004531)
                  ·
                    refine ⟨8808627807551365285506797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5872418538367576857004531 8808627807551365285506797)
                    ·
                      refine ⟨3303235427831761982065049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8808627807551365285506797 3303235427831761982065049)
                      ·
                        rfl

theorem cell23_6433028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_6433028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433028 prefixEnd_6433028 := by exact prefixLift 6433028
  have htrace : WordTrace (prefixWord ++ tailWord_6433028) baseStart_6433028 baseEnd_6433028 := by
    simpa [prefixWord, tailWord_6433028, baseEnd_6433028] using wordTrace_append hprefix tailTrace_6433028
  have hstable : (prefixWord ++ tailWord_6433028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433028).length < 2 ^ (prefixWord ++ tailWord_6433028).sum := by decide
  have hdescent : baseEnd_6433028 < baseStart_6433028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433051 : List Nat := [1, 1, 1, 1, 1, 1, 9, 1, 1, 4, 2]
def baseStart_6433051 : Nat := 118140960795 + 6433051 * 2 ^ 59
def prefixEnd_6433051 : Nat := 4983230072969 + 3 ^ 40 * 6433051 * 2
def baseEnd_6433051 : Nat := 3303247237886815392077443

theorem tailTrace_6433051 : CollatzResearch.WordTrace tailWord_6433051 prefixEnd_6433051 3303247237886815392077443 := by
  unfold tailWord_6433051
  simp only [CollatzResearch.WordTrace]
  refine ⟨234632645817162379485715007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156421763878108252990476671 234632645817162379485715007)
  ·
    refine ⟨351948968725743569228572511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234632645817162379485715007 351948968725743569228572511)
    ·
      refine ⟨527923453088615353842858767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351948968725743569228572511 527923453088615353842858767)
      ·
        refine ⟨791885179632923030764288151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527923453088615353842858767 791885179632923030764288151)
        ·
          refine ⟨1187827769449384546146432227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791885179632923030764288151 1187827769449384546146432227)
          ·
            refine ⟨1781741654174076819219648341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187827769449384546146432227 1781741654174076819219648341)
            ·
              refine ⟨10439892504926231362615127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1781741654174076819219648341 10439892504926231362615127)
              ·
                refine ⟨15659838757389347043922691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10439892504926231362615127 15659838757389347043922691)
                ·
                  refine ⟨23489758136084020565884037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15659838757389347043922691 23489758136084020565884037)
                  ·
                    refine ⟨4404329650515753856103257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23489758136084020565884037 4404329650515753856103257)
                    ·
                      refine ⟨3303247237886815392077443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404329650515753856103257 3303247237886815392077443)
                      ·
                        rfl

theorem cell23_6433051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 4, 2].length) (baseStart_6433051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433051 prefixEnd_6433051 := by exact prefixLift 6433051
  have htrace : WordTrace (prefixWord ++ tailWord_6433051) baseStart_6433051 baseEnd_6433051 := by
    simpa [prefixWord, tailWord_6433051, baseEnd_6433051] using wordTrace_append hprefix tailTrace_6433051
  have hstable : (prefixWord ++ tailWord_6433051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433051).length < 2 ^ (prefixWord ++ tailWord_6433051).sum := by decide
  have hdescent : baseEnd_6433051 < baseStart_6433051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433063 : List Nat := [1, 1, 8, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_6433063 : Nat := 118140960795 + 6433063 * 2 ^ 59
def prefixEnd_6433063 : Nat := 4983230072969 + 3 ^ 40 * 6433063 * 2
def baseEnd_6433063 : Nat := 3303253399654669345127389

theorem tailTrace_6433063 : CollatzResearch.WordTrace tailWord_6433063 prefixEnd_6433063 3303253399654669345127389 := by
  unfold tailWord_6433063
  simp only [CollatzResearch.WordTrace]
  refine ⟨234633083493118905535151843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156422055662079270356767895 234633083493118905535151843)
  ·
    refine ⟨351949625239678358302727765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234633083493118905535151843 351949625239678358302727765)
    ·
      refine ⟨4124409670777480761360091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 351949625239678358302727765 4124409670777480761360091)
      ·
        refine ⟨6186614506166221142040137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4124409670777480761360091 6186614506166221142040137)
        ·
          refine ⟨4639960879624665856530103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6186614506166221142040137 4639960879624665856530103)
          ·
            refine ⟨6959941319436998784795155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4639960879624665856530103 6959941319436998784795155)
            ·
              refine ⟨10439911979155498177192733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6959941319436998784795155 10439911979155498177192733)
              ·
                refine ⟨3914966992183311816447275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10439911979155498177192733 3914966992183311816447275)
                ·
                  refine ⟨5872450488274967724670913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3914966992183311816447275 5872450488274967724670913)
                  ·
                    refine ⟨4404337866206225793503185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5872450488274967724670913 4404337866206225793503185)
                    ·
                      refine ⟨3303253399654669345127389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404337866206225793503185 3303253399654669345127389)
                      ·
                        rfl

theorem cell23_6433063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_6433063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433063 prefixEnd_6433063 := by exact prefixLift 6433063
  have htrace : WordTrace (prefixWord ++ tailWord_6433063) baseStart_6433063 baseEnd_6433063 := by
    simpa [prefixWord, tailWord_6433063, baseEnd_6433063] using wordTrace_append hprefix tailTrace_6433063
  have hstable : (prefixWord ++ tailWord_6433063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433063).length < 2 ^ (prefixWord ++ tailWord_6433063).sum := by decide
  have hdescent : baseEnd_6433063 < baseStart_6433063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433178 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3]
def baseStart_6433178 : Nat := 118140960795 + 6433178 * 2 ^ 59
def prefixEnd_6433178 : Nat := 4983230072969 + 3 ^ 40 * 6433178 * 2
def baseEnd_6433178 : Nat := 3303312449929936395189359

theorem tailTrace_6433178 : CollatzResearch.WordTrace tailWord_6433178 prefixEnd_6433178 3303312449929936395189359 := by
  unfold tailWord_6433178
  simp only [CollatzResearch.WordTrace]
  refine ⟨58659319471925570043897047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156424851925134853450392125 58659319471925570043897047)
  ·
    refine ⟨87988979207888355065845571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58659319471925570043897047 87988979207888355065845571)
    ·
      refine ⟨131983468811832532598768357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87988979207888355065845571 131983468811832532598768357)
      ·
        refine ⟨24746900402218599862269067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131983468811832532598768357 24746900402218599862269067)
        ·
          refine ⟨37120350603327899793403601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24746900402218599862269067 37120350603327899793403601)
          ·
            refine ⟨27840262952495924845052701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37120350603327899793403601 27840262952495924845052701)
            ·
              refine ⟨10440098607185971816894763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27840262952495924845052701 10440098607185971816894763)
              ·
                refine ⟨15660147910778957725342145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10440098607185971816894763 15660147910778957725342145)
                ·
                  refine ⟨11745110933084218294006609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15660147910778957725342145 11745110933084218294006609)
                  ·
                    refine ⟨8808833199813163720504957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11745110933084218294006609 8808833199813163720504957)
                    ·
                      refine ⟨3303312449929936395189359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8808833199813163720504957 3303312449929936395189359)
                      ·
                        rfl

theorem cell23_6433178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_6433178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433178 prefixEnd_6433178 := by exact prefixLift 6433178
  have htrace : WordTrace (prefixWord ++ tailWord_6433178) baseStart_6433178 baseEnd_6433178 := by
    simpa [prefixWord, tailWord_6433178, baseEnd_6433178] using wordTrace_append hprefix tailTrace_6433178
  have hstable : (prefixWord ++ tailWord_6433178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433178).length < 2 ^ (prefixWord ++ tailWord_6433178).sum := by decide
  have hdescent : baseEnd_6433178 < baseStart_6433178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433231 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 1, 8, 2]
def baseStart_6433231 : Nat := 118140960795 + 6433231 * 2 ^ 59
def prefixEnd_6433231 : Nat := 4983230072969 + 3 ^ 40 * 6433231 * 2
def baseEnd_6433231 : Nat := 3303339664404624687826615

theorem tailTrace_6433231 : CollatzResearch.WordTrace tailWord_6433231 prefixEnd_6433231 3303339664404624687826615 := by
  unfold tailWord_6433231
  simp only [CollatzResearch.WordTrace]
  refine ⟨234639210956510270227267547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156426140637673513484845031 234639210956510270227267547)
  ·
    refine ⟨351958816434765405340901321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234639210956510270227267547 351958816434765405340901321)
    ·
      refine ⟨263969112326074054005675991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351958816434765405340901321 263969112326074054005675991)
      ·
        refine ⟨395953668489111081008513987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263969112326074054005675991 395953668489111081008513987)
        ·
          refine ⟨593930502733666621512770981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395953668489111081008513987 593930502733666621512770981)
          ·
            refine ⟨111361969262562491533644559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 593930502733666621512770981 111361969262562491533644559)
            ·
              refine ⟨167042953893843737300466839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111361969262562491533644559 167042953893843737300466839)
              ·
                refine ⟨250564430840765605950700259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167042953893843737300466839 250564430840765605950700259)
                ·
                  refine ⟨375846646261148408926050389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250564430840765605950700259 375846646261148408926050389)
                  ·
                    refine ⟨4404452885872832917102153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 375846646261148408926050389 4404452885872832917102153)
                    ·
                      refine ⟨3303339664404624687826615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404452885872832917102153 3303339664404624687826615)
                      ·
                        rfl

theorem cell23_6433231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 8, 2].length) (baseStart_6433231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433231 prefixEnd_6433231 := by exact prefixLift 6433231
  have htrace : WordTrace (prefixWord ++ tailWord_6433231) baseStart_6433231 baseEnd_6433231 := by
    simpa [prefixWord, tailWord_6433231, baseEnd_6433231] using wordTrace_append hprefix tailTrace_6433231
  have hstable : (prefixWord ++ tailWord_6433231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433231).length < 2 ^ (prefixWord ++ tailWord_6433231).sum := by decide
  have hdescent : baseEnd_6433231 < baseStart_6433231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433241 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 6, 4]
def baseStart_6433241 : Nat := 118140960795 + 6433241 * 2 ^ 59
def prefixEnd_6433241 : Nat := 4983230072969 + 3 ^ 40 * 6433241 * 2
def baseEnd_6433241 : Nat := 1101114933070389882900523

theorem tailTrace_6433241 : CollatzResearch.WordTrace tailWord_6433241 prefixEnd_6433241 1101114933070389882900523 := by
  unfold tailWord_6433241
  simp only [CollatzResearch.WordTrace]
  refine ⟨234639575686474041935131577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156426383790982694623421051 234639575686474041935131577)
  ·
    refine ⟨175979681764855531451348683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234639575686474041935131577 175979681764855531451348683)
    ·
      refine ⟨263969522647283297177023025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175979681764855531451348683 263969522647283297177023025)
      ·
        refine ⟨197977141985462472882767269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263969522647283297177023025 197977141985462472882767269)
        ·
          refine ⟨37120714122274213665518863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197977141985462472882767269 37120714122274213665518863)
          ·
            refine ⟨55681071183411320498278295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37120714122274213665518863 55681071183411320498278295)
            ·
              refine ⟨83521606775116980747417443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55681071183411320498278295 83521606775116980747417443)
              ·
                refine ⟨125282410162675471121126165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83521606775116980747417443 125282410162675471121126165)
                ·
                  refine ⟨5872612976375412708802789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125282410162675471121126165 5872612976375412708802789)
                  ·
                    refine ⟨1101114933070389882900523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5872612976375412708802789 1101114933070389882900523)
                    ·
                      rfl

theorem cell23_6433241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 4].length) (baseStart_6433241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433241 prefixEnd_6433241 := by exact prefixLift 6433241
  have htrace : WordTrace (prefixWord ++ tailWord_6433241) baseStart_6433241 baseEnd_6433241 := by
    simpa [prefixWord, tailWord_6433241, baseEnd_6433241] using wordTrace_append hprefix tailTrace_6433241
  have hstable : (prefixWord ++ tailWord_6433241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433241).length < 2 ^ (prefixWord ++ tailWord_6433241).sum := by decide
  have hdescent : baseEnd_6433241 < baseStart_6433241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433258 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 4, 4]
def baseStart_6433258 : Nat := 118140960795 + 6433258 * 2 ^ 59
def prefixEnd_6433258 : Nat := 4983230072969 + 3 ^ 40 * 6433258 * 2
def baseEnd_6433258 : Nat := 1101117842794098694062997

theorem tailTrace_6433258 : CollatzResearch.WordTrace tailWord_6433258 prefixEnd_6433258 1101117842794098694062997 := by
  unfold tailWord_6433258
  simp only [CollatzResearch.WordTrace]
  refine ⟨58660048931853113459625107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156426797151608302559000285 58660048931853113459625107)
  ·
    refine ⟨87990073397779670189437661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58660048931853113459625107 87990073397779670189437661)
    ·
      refine ⟨32996277524167376321039123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87990073397779670189437661 32996277524167376321039123)
      ·
        refine ⟨49494416286251064481558685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32996277524167376321039123 49494416286251064481558685)
        ·
          refine ⟨18560406107344149180584507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49494416286251064481558685 18560406107344149180584507)
          ·
            refine ⟨27840609161016223770876761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18560406107344149180584507 27840609161016223770876761)
            ·
              refine ⟨20880456870762167828157571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27840609161016223770876761 20880456870762167828157571)
              ·
                refine ⟨31320685306143251742236357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20880456870762167828157571 31320685306143251742236357)
                ·
                  refine ⟨5872628494901859701669317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31320685306143251742236357 5872628494901859701669317)
                  ·
                    refine ⟨1101117842794098694062997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5872628494901859701669317 1101117842794098694062997)
                    ·
                      rfl

theorem cell23_6433258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_6433258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433258 prefixEnd_6433258 := by exact prefixLift 6433258
  have htrace : WordTrace (prefixWord ++ tailWord_6433258) baseStart_6433258 baseEnd_6433258 := by
    simpa [prefixWord, tailWord_6433258, baseEnd_6433258] using wordTrace_append hprefix tailTrace_6433258
  have hstable : (prefixWord ++ tailWord_6433258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433258).length < 2 ^ (prefixWord ++ tailWord_6433258).sum := by decide
  have hdescent : baseEnd_6433258 < baseStart_6433258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433286 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_6433286 : Nat := 118140960795 + 6433286 * 2 ^ 59
def prefixEnd_6433286 : Nat := 4983230072969 + 3 ^ 40 * 6433286 * 2
def baseEnd_6433286 : Nat := 3303367905840621972638863

theorem tailTrace_6433286 : CollatzResearch.WordTrace tailWord_6433286 prefixEnd_6433286 3303367905840621972638863 := by
  unfold tailWord_6433286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7332538030353469206891241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156427477980874009747013141 7332538030353469206891241)
  ·
    refine ⟨5499403522765101905168431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7332538030353469206891241 5499403522765101905168431)
    ·
      refine ⟨8249105284147652857752647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5499403522765101905168431 8249105284147652857752647)
      ·
        refine ⟨12373657926221479286628971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8249105284147652857752647 12373657926221479286628971)
        ·
          refine ⟨18560486889332218929943457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12373657926221479286628971 18560486889332218929943457)
          ·
            refine ⟨13920365166999164197457593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18560486889332218929943457 13920365166999164197457593)
            ·
              refine ⟨10440273875249373148093195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13920365166999164197457593 10440273875249373148093195)
              ·
                refine ⟨15660410812874059722139793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10440273875249373148093195 15660410812874059722139793)
                ·
                  refine ⟨11745308109655544791604845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15660410812874059722139793 11745308109655544791604845)
                  ·
                    refine ⟨4404490541120829296851817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11745308109655544791604845 4404490541120829296851817)
                    ·
                      refine ⟨3303367905840621972638863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404490541120829296851817 3303367905840621972638863)
                      ·
                        rfl

theorem cell23_6433286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_6433286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433286 prefixEnd_6433286 := by exact prefixLift 6433286
  have htrace : WordTrace (prefixWord ++ tailWord_6433286) baseStart_6433286 baseEnd_6433286 := by
    simpa [prefixWord, tailWord_6433286, baseEnd_6433286] using wordTrace_append hprefix tailTrace_6433286
  have hstable : (prefixWord ++ tailWord_6433286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433286).length < 2 ^ (prefixWord ++ tailWord_6433286).sum := by decide
  have hdescent : baseEnd_6433286 < baseStart_6433286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433315 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 2, 1, 3]
def baseStart_6433315 : Nat := 118140960795 + 6433315 * 2 ^ 59
def prefixEnd_6433315 : Nat := 4983230072969 + 3 ^ 40 * 6433315 * 2
def baseEnd_6433315 : Nat := 3303382796779602359176229

theorem tailTrace_6433315 : CollatzResearch.WordTrace tailWord_6433315 prefixEnd_6433315 3303382796779602359176229 := by
  unfold tailWord_6433315
  simp only [CollatzResearch.WordTrace]
  refine ⟨234642274688205952573325399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156428183125470635048883599 234642274688205952573325399)
  ·
    refine ⟨351963412032308928859988099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234642274688205952573325399 351963412032308928859988099)
    ·
      refine ⟨527945118048463393289982149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351963412032308928859988099 527945118048463393289982149)
      ·
        refine ⟨98989709634086886241871653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 527945118048463393289982149 98989709634086886241871653)
        ·
          refine ⟨18560570556391291170350935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98989709634086886241871653 18560570556391291170350935)
          ·
            refine ⟨27840855834586936755526403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18560570556391291170350935 27840855834586936755526403)
            ·
              refine ⟨41761283751880405133289605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27840855834586936755526403 41761283751880405133289605)
              ·
                refine ⟨7830240703477575962491801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41761283751880405133289605 7830240703477575962491801)
                ·
                  refine ⟨5872680527608181971868851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7830240703477575962491801 5872680527608181971868851)
                  ·
                    refine ⟨8809020791412272957803277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5872680527608181971868851 8809020791412272957803277)
                    ·
                      refine ⟨3303382796779602359176229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8809020791412272957803277 3303382796779602359176229)
                      ·
                        rfl

theorem cell23_6433315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_6433315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433315 prefixEnd_6433315 := by exact prefixLift 6433315
  have htrace : WordTrace (prefixWord ++ tailWord_6433315) baseStart_6433315 baseEnd_6433315 := by
    simpa [prefixWord, tailWord_6433315, baseEnd_6433315] using wordTrace_append hprefix tailTrace_6433315
  have hstable : (prefixWord ++ tailWord_6433315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433315).length < 2 ^ (prefixWord ++ tailWord_6433315).sum := by decide
  have hdescent : baseEnd_6433315 < baseStart_6433315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433316 : List Nat := [2, 3, 1, 5, 1, 1, 1, 4, 1, 2, 2]
def baseStart_6433316 : Nat := 118140960795 + 6433316 * 2 ^ 59
def prefixEnd_6433316 : Nat := 4983230072969 + 3 ^ 40 * 6433316 * 2
def baseEnd_6433316 : Nat := 3303383310260256855263725

theorem tailTrace_6433316 : CollatzResearch.WordTrace tailWord_6433316 prefixEnd_6433316 3303383310260256855263725 := by
  unfold tailWord_6433316
  simp only [CollatzResearch.WordTrace]
  refine ⟨117321155580601164872055901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156428207440801553162741201 117321155580601164872055901)
  ·
    refine ⟨43995433342725436827020963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117321155580601164872055901 43995433342725436827020963)
    ·
      refine ⟨65993150014088155240531445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43995433342725436827020963 65993150014088155240531445)
      ·
        refine ⟨6186857813820764553799823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65993150014088155240531445 6186857813820764553799823)
        ·
          refine ⟨9280286720731146830699735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186857813820764553799823 9280286720731146830699735)
          ·
            refine ⟨13920430081096720246049603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9280286720731146830699735 13920430081096720246049603)
            ·
              refine ⟨20880645121645080369074405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13920430081096720246049603 20880645121645080369074405)
              ·
                refine ⟨3915120960308452569201451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20880645121645080369074405 3915120960308452569201451)
                ·
                  refine ⟨5872681440462678853802177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3915120960308452569201451 5872681440462678853802177)
                  ·
                    refine ⟨4404511080347009140351633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5872681440462678853802177 4404511080347009140351633)
                    ·
                      refine ⟨3303383310260256855263725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404511080347009140351633 3303383310260256855263725)
                      ·
                        rfl

theorem cell23_6433316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_6433316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433316 prefixEnd_6433316 := by exact prefixLift 6433316
  have htrace : WordTrace (prefixWord ++ tailWord_6433316) baseStart_6433316 baseEnd_6433316 := by
    simpa [prefixWord, tailWord_6433316, baseEnd_6433316] using wordTrace_append hprefix tailTrace_6433316
  have hstable : (prefixWord ++ tailWord_6433316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433316).length < 2 ^ (prefixWord ++ tailWord_6433316).sum := by decide
  have hdescent : baseEnd_6433316 < baseStart_6433316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433331 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 2, 6]
def baseStart_6433331 : Nat := 118140960795 + 6433331 * 2 ^ 59
def prefixEnd_6433331 : Nat := 4983230072969 + 3 ^ 40 * 6433331 * 2
def baseEnd_6433331 : Nat := 1101130337490024765525385

theorem tailTrace_6433331 : CollatzResearch.WordTrace tailWord_6433331 prefixEnd_6433331 1101130337490024765525385 := by
  unfold tailWord_6433331
  simp only [CollatzResearch.WordTrace]
  refine ⟨234642858256147987305907847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156428572170765324870605231 234642858256147987305907847)
  ·
    refine ⟨351964287384221980958861771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234642858256147987305907847 351964287384221980958861771)
    ·
      refine ⟨527946431076332971438292657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351964287384221980958861771 527946431076332971438292657)
      ·
        refine ⟨395959823307249728578719493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527946431076332971438292657 395959823307249728578719493)
        ·
          refine ⟨74242466870109324108509905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395959823307249728578719493 74242466870109324108509905)
          ·
            refine ⟨55681850152581993081382429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74242466870109324108509905 55681850152581993081382429)
            ·
              refine ⟨20880693807218247405518411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55681850152581993081382429 20880693807218247405518411)
              ·
                refine ⟨31321040710827371108277617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20880693807218247405518411 31321040710827371108277617)
                ·
                  refine ⟨23490780533120528331208213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31321040710827371108277617 23490780533120528331208213)
                  ·
                    refine ⟨1101130337490024765525385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23490780533120528331208213 1101130337490024765525385)
                    ·
                      rfl

theorem cell23_6433331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 6].length) (baseStart_6433331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433331 prefixEnd_6433331 := by exact prefixLift 6433331
  have htrace : WordTrace (prefixWord ++ tailWord_6433331) baseStart_6433331 baseEnd_6433331 := by
    simpa [prefixWord, tailWord_6433331, baseEnd_6433331] using wordTrace_append hprefix tailTrace_6433331
  have hstable : (prefixWord ++ tailWord_6433331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433331).length < 2 ^ (prefixWord ++ tailWord_6433331).sum := by decide
  have hdescent : baseEnd_6433331 < baseStart_6433331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433371 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 3]
def baseStart_6433371 : Nat := 118140960795 + 6433371 * 2 ^ 59
def prefixEnd_6433371 : Nat := 4983230072969 + 3 ^ 40 * 6433371 * 2
def baseEnd_6433371 : Nat := 3303411551696254140075971

theorem tailTrace_6433371 : CollatzResearch.WordTrace tailWord_6433371 prefixEnd_6433371 3303411551696254140075971 := by
  unfold tailWord_6433371
  simp only [CollatzResearch.WordTrace]
  refine ⟨234644317176003074137363967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156429544784002049424909311 234644317176003074137363967)
  ·
    refine ⟨351966475764004611206045951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234644317176003074137363967 351966475764004611206045951)
    ·
      refine ⟨527949713646006916809068927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351966475764004611206045951 527949713646006916809068927)
      ·
        refine ⟨791924570469010375213603391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527949713646006916809068927 791924570469010375213603391)
        ·
          refine ⟨1187886855703515562820405087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791924570469010375213603391 1187886855703515562820405087)
          ·
            refine ⟨1781830283555273344230607631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1187886855703515562820405087 1781830283555273344230607631)
            ·
              refine ⟨2672745425332910016345911447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1781830283555273344230607631 2672745425332910016345911447)
              ·
                refine ⟨4009118137999365024518867171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2672745425332910016345911447 4009118137999365024518867171)
                ·
                  refine ⟨6013677206999047536778300757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4009118137999365024518867171 6013677206999047536778300757)
                  ·
                    refine ⟨8809097471190011040202589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 6013677206999047536778300757 8809097471190011040202589)
                    ·
                      refine ⟨3303411551696254140075971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8809097471190011040202589 3303411551696254140075971)
                      ·
                        rfl

theorem cell23_6433371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 3].length) (baseStart_6433371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433371 prefixEnd_6433371 := by exact prefixLift 6433371
  have htrace : WordTrace (prefixWord ++ tailWord_6433371) baseStart_6433371 baseEnd_6433371 := by
    simpa [prefixWord, tailWord_6433371, baseEnd_6433371] using wordTrace_append hprefix tailTrace_6433371
  have hstable : (prefixWord ++ tailWord_6433371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433371).length < 2 ^ (prefixWord ++ tailWord_6433371).sum := by decide
  have hdescent : baseEnd_6433371 < baseStart_6433371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433388 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 3]
def baseStart_6433388 : Nat := 118140960795 + 6433388 * 2 ^ 59
def prefixEnd_6433388 : Nat := 4983230072969 + 3 ^ 40 * 6433388 * 2
def baseEnd_6433388 : Nat := 3303420280867380573563393

theorem tailTrace_6433388 : CollatzResearch.WordTrace tailWord_6433388 prefixEnd_6433388 3303420280867380573563393 := by
  unfold tailWord_6433388
  simp only [CollatzResearch.WordTrace]
  refine ⟨117322468608470743020366409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156429958144627657360488545 117322468608470743020366409)
  ·
    refine ⟨87991851456353057265274807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117322468608470743020366409 87991851456353057265274807)
    ·
      refine ⟨131987777184529585897912211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87991851456353057265274807 131987777184529585897912211)
      ·
        refine ⟨197981665776794378846868317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131987777184529585897912211 197981665776794378846868317)
        ·
          refine ⟨74243124666297892067575619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197981665776794378846868317 74243124666297892067575619)
          ·
            refine ⟨111364686999446838101363429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74243124666297892067575619 111364686999446838101363429)
            ·
              refine ⟨20880878812396282144005643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111364686999446838101363429 20880878812396282144005643)
              ·
                refine ⟨31321318218594423216008465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20880878812396282144005643 31321318218594423216008465)
                ·
                  refine ⟨23490988663945817412006349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31321318218594423216008465 23490988663945817412006349)
                  ·
                    refine ⟨8809120748979681529502381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23490988663945817412006349 8809120748979681529502381)
                    ·
                      refine ⟨3303420280867380573563393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8809120748979681529502381 3303420280867380573563393)
                      ·
                        rfl

theorem cell23_6433388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_6433388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433388 prefixEnd_6433388 := by exact prefixLift 6433388
  have htrace : WordTrace (prefixWord ++ tailWord_6433388) baseStart_6433388 baseEnd_6433388 := by
    simpa [prefixWord, tailWord_6433388, baseEnd_6433388] using wordTrace_append hprefix tailTrace_6433388
  have hstable : (prefixWord ++ tailWord_6433388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433388).length < 2 ^ (prefixWord ++ tailWord_6433388).sum := by decide
  have hdescent : baseEnd_6433388 < baseStart_6433388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433391 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 1, 7]
def baseStart_6433391 : Nat := 118140960795 + 6433391 * 2 ^ 59
def prefixEnd_6433391 : Nat := 4983230072969 + 3 ^ 40 * 6433391 * 2
def baseEnd_6433391 : Nat := 1101140607103114687275293

theorem tailTrace_6433391 : CollatzResearch.WordTrace tailWord_6433391 prefixEnd_6433391 1101140607103114687275293 := by
  unfold tailWord_6433391
  simp only [CollatzResearch.WordTrace]
  refine ⟨234645046635930617553092027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156430031090620411702061351 234645046635930617553092027)
  ·
    refine ⟨351967569953895926329638041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234645046635930617553092027 351967569953895926329638041)
    ·
      refine ⟨263975677465421944747228531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351967569953895926329638041 263975677465421944747228531)
      ·
        refine ⟨395963516198132917120842797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263975677465421944747228531 395963516198132917120842797)
        ·
          refine ⟨148486318574299843920316049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395963516198132917120842797 148486318574299843920316049)
          ·
            refine ⟨111364738930724882940237037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148486318574299843920316049 111364738930724882940237037)
            ·
              refine ⟨41761777099021831102588889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111364738930724882940237037 41761777099021831102588889)
              ·
                refine ⟨31321332824266373326941667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41761777099021831102588889 31321332824266373326941667)
                ·
                  refine ⟨46981999236399559990412501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31321332824266373326941667 46981999236399559990412501)
                  ·
                    refine ⟨1101140607103114687275293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46981999236399559990412501 1101140607103114687275293)
                    ·
                      rfl

theorem cell23_6433391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_6433391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433391 prefixEnd_6433391 := by exact prefixLift 6433391
  have htrace : WordTrace (prefixWord ++ tailWord_6433391) baseStart_6433391 baseEnd_6433391 := by
    simpa [prefixWord, tailWord_6433391, baseEnd_6433391] using wordTrace_append hprefix tailTrace_6433391
  have hstable : (prefixWord ++ tailWord_6433391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433391).length < 2 ^ (prefixWord ++ tailWord_6433391).sum := by decide
  have hdescent : baseEnd_6433391 < baseStart_6433391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433412 : List Nat := [2, 3, 2, 1, 3, 3, 1, 3, 5]
def baseStart_6433412 : Nat := 118140960795 + 6433412 * 2 ^ 59
def prefixEnd_6433412 : Nat := 4983230072969 + 3 ^ 40 * 6433412 * 2
def baseEnd_6433412 : Nat := 367048067155898719962587

theorem tailTrace_6433412 : CollatzResearch.WordTrace tailWord_6433412 prefixEnd_6433412 367048067155898719962587 := by
  unfold tailWord_6433412
  simp only [CollatzResearch.WordTrace]
  refine ⟨117322906284427269069803245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156430541712569692093070993 117322906284427269069803245)
  ·
    refine ⟨43996089856660225901176217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117322906284427269069803245 43996089856660225901176217)
    ·
      refine ⟨32997067392495169425882163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43996089856660225901176217 32997067392495169425882163)
      ·
        refine ⟨49495601088742754138823245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32997067392495169425882163 49495601088742754138823245)
        ·
          refine ⟨18560850408278532802058717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49495601088742754138823245 18560850408278532802058717)
          ·
            refine ⟨6960318903104449800772019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18560850408278532802058717 6960318903104449800772019)
            ·
              refine ⟨10440478354656674701158029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6960318903104449800772019 10440478354656674701158029)
              ·
                refine ⟨3915179382996253012934261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10440478354656674701158029 3915179382996253012934261)
                ·
                  refine ⟨367048067155898719962587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3915179382996253012934261 367048067155898719962587)
                  ·
                    rfl

theorem cell23_6433412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_6433412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433412 prefixEnd_6433412 := by exact prefixLift 6433412
  have htrace : WordTrace (prefixWord ++ tailWord_6433412) baseStart_6433412 baseEnd_6433412 := by
    simpa [prefixWord, tailWord_6433412, baseEnd_6433412] using wordTrace_append hprefix tailTrace_6433412
  have hstable : (prefixWord ++ tailWord_6433412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433412).length < 2 ^ (prefixWord ++ tailWord_6433412).sum := by decide
  have hdescent : baseEnd_6433412 < baseStart_6433412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433498 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_6433498 : Nat := 118140960795 + 6433498 * 2 ^ 59
def prefixEnd_6433498 : Nat := 4983230072969 + 3 ^ 40 * 6433498 * 2
def baseEnd_6433498 : Nat := 1101158921246458381062629

theorem tailTrace_6433498 : CollatzResearch.WordTrace tailWord_6433498 prefixEnd_6433498 1101158921246458381062629 := by
  unfold tailWord_6433498
  simp only [CollatzResearch.WordTrace]
  refine ⟨58662237311635743706809287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156432632831028649884824765 58662237311635743706809287)
  ·
    refine ⟨87993355967453615560213931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58662237311635743706809287 87993355967453615560213931)
    ·
      refine ⟨131990033951180423340320897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87993355967453615560213931 131990033951180423340320897)
      ·
        refine ⟨98992525463385317505240673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131990033951180423340320897 98992525463385317505240673)
        ·
          refine ⟨74244394097538988128930505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98992525463385317505240673 74244394097538988128930505)
          ·
            refine ⟨55683295573154241096697879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74244394097538988128930505 55683295573154241096697879)
            ·
              refine ⟨83524943359731361645046819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55683295573154241096697879 83524943359731361645046819)
              ·
                refine ⟨125287415039597042467570229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83524943359731361645046819 125287415039597042467570229)
                ·
                  refine ⟨11745695159962222731334709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125287415039597042467570229 11745695159962222731334709)
                  ·
                    refine ⟨1101158921246458381062629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11745695159962222731334709 1101158921246458381062629)
                    ·
                      rfl

theorem cell23_6433498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_6433498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433498 prefixEnd_6433498 := by exact prefixLift 6433498
  have htrace : WordTrace (prefixWord ++ tailWord_6433498) baseStart_6433498 baseEnd_6433498 := by
    simpa [prefixWord, tailWord_6433498, baseEnd_6433498] using wordTrace_append hprefix tailTrace_6433498
  have hstable : (prefixWord ++ tailWord_6433498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433498).length < 2 ^ (prefixWord ++ tailWord_6433498).sum := by decide
  have hdescent : baseEnd_6433498 < baseStart_6433498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433522 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 1, 5, 2]
def baseStart_6433522 : Nat := 118140960795 + 6433522 * 2 ^ 59
def prefixEnd_6433522 : Nat := 4983230072969 + 3 ^ 40 * 6433522 * 2
def baseEnd_6433522 : Nat := 3303489087275083049287777

theorem tailTrace_6433522 : CollatzResearch.WordTrace tailWord_6433522 prefixEnd_6433522 3303489087275083049287777 := by
  unfold tailWord_6433522
  simp only [CollatzResearch.WordTrace]
  refine ⟨58662456149614006731527705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156433216398970684617407213 58662456149614006731527705)
  ·
    refine ⟨43996842112210505048645779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58662456149614006731527705 43996842112210505048645779)
    ·
      refine ⟨65995263168315757572968669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43996842112210505048645779 65995263168315757572968669)
      ·
        refine ⟨24748223688118409089863251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65995263168315757572968669 24748223688118409089863251)
        ·
          refine ⟨37122335532177613634794877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24748223688118409089863251 37122335532177613634794877)
          ·
            refine ⟨13920875824566605113048079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37122335532177613634794877 13920875824566605113048079)
            ·
              refine ⟨20881313736849907669572119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13920875824566605113048079 20881313736849907669572119)
              ·
                refine ⟨31321970605274861504358179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20881313736849907669572119 31321970605274861504358179)
                ·
                  refine ⟨46982955907912292256537269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31321970605274861504358179 46982955907912292256537269)
                  ·
                    refine ⟨4404652116366777399050369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46982955907912292256537269 4404652116366777399050369)
                    ·
                      refine ⟨3303489087275083049287777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404652116366777399050369 3303489087275083049287777)
                      ·
                        rfl

theorem cell23_6433522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_6433522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433522 prefixEnd_6433522 := by exact prefixLift 6433522
  have htrace : WordTrace (prefixWord ++ tailWord_6433522) baseStart_6433522 baseEnd_6433522 := by
    simpa [prefixWord, tailWord_6433522, baseEnd_6433522] using wordTrace_append hprefix tailTrace_6433522
  have hstable : (prefixWord ++ tailWord_6433522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433522).length < 2 ^ (prefixWord ++ tailWord_6433522).sum := by decide
  have hdescent : baseEnd_6433522 < baseStart_6433522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433528 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 1, 6]
def baseStart_6433528 : Nat := 118140960795 + 6433528 * 2 ^ 59
def prefixEnd_6433528 : Nat := 4983230072969 + 3 ^ 40 * 6433528 * 2
def baseEnd_6433528 : Nat := 1101164056053003341937583

theorem tailTrace_6433528 : CollatzResearch.WordTrace tailWord_6433528 prefixEnd_6433528 1101164056053003341937583 := by
  unfold tailWord_6433528
  simp only [CollatzResearch.WordTrace]
  refine ⟨117325021718217144975414619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156433362290956193300552825 117325021718217144975414619)
  ·
    refine ⟨175987532577325717463121929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117325021718217144975414619 175987532577325717463121929)
    ·
      refine ⟨131990649432994288097341447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175987532577325717463121929 131990649432994288097341447)
      ·
        refine ⟨197985974149491432146012171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131990649432994288097341447 197985974149491432146012171)
        ·
          refine ⟨296978961224237148219018257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197985974149491432146012171 296978961224237148219018257)
          ·
            refine ⟨222734220918177861164263693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296978961224237148219018257 222734220918177861164263693)
            ·
              refine ⟨83525332844316697936598885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222734220918177861164263693 83525332844316697936598885)
              ·
                refine ⟨15660999908309380863112291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83525332844316697936598885 15660999908309380863112291)
                ·
                  refine ⟨23491499862464071294668437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15660999908309380863112291 23491499862464071294668437)
                  ·
                    refine ⟨1101164056053003341937583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23491499862464071294668437 1101164056053003341937583)
                    ·
                      rfl

theorem cell23_6433528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_6433528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433528 prefixEnd_6433528 := by exact prefixLift 6433528
  have htrace : WordTrace (prefixWord ++ tailWord_6433528) baseStart_6433528 baseEnd_6433528 := by
    simpa [prefixWord, tailWord_6433528, baseEnd_6433528] using wordTrace_append hprefix tailTrace_6433528
  have hstable : (prefixWord ++ tailWord_6433528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433528).length < 2 ^ (prefixWord ++ tailWord_6433528).sum := by decide
  have hdescent : baseEnd_6433528 < baseStart_6433528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433532 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 1, 5]
def baseStart_6433532 : Nat := 118140960795 + 6433532 * 2 ^ 59
def prefixEnd_6433532 : Nat := 4983230072969 + 3 ^ 40 * 6433532 * 2
def baseEnd_6433532 : Nat := 1101164740693876003387577

theorem tailTrace_6433532 : CollatzResearch.WordTrace tailWord_6433532 prefixEnd_6433532 1101164740693876003387577 := by
  unfold tailWord_6433532
  simp only [CollatzResearch.WordTrace]
  refine ⟨117325094664209899316987425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156433459552279865755983233 117325094664209899316987425)
  ·
    refine ⟨87993820998157424487740569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117325094664209899316987425 87993820998157424487740569)
    ·
      refine ⟨65995365748618068365805427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87993820998157424487740569 65995365748618068365805427)
      ·
        refine ⟨98993048622927102548708141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65995365748618068365805427 98993048622927102548708141)
        ·
          refine ⟨37122393233597663455765553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98993048622927102548708141 37122393233597663455765553)
          ·
            refine ⟨27841794925198247591824165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37122393233597663455765553 27841794925198247591824165)
            ·
              refine ⟨5220336548474671423467031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27841794925198247591824165 5220336548474671423467031)
              ·
                refine ⟨7830504822712007135200547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5220336548474671423467031 7830504822712007135200547)
                ·
                  refine ⟨11745757234068010702800821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7830504822712007135200547 11745757234068010702800821)
                  ·
                    refine ⟨1101164740693876003387577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11745757234068010702800821 1101164740693876003387577)
                    ·
                      rfl

theorem cell23_6433532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_6433532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433532 prefixEnd_6433532 := by exact prefixLift 6433532
  have htrace : WordTrace (prefixWord ++ tailWord_6433532) baseStart_6433532 baseEnd_6433532 := by
    simpa [prefixWord, tailWord_6433532, baseEnd_6433532] using wordTrace_append hprefix tailTrace_6433532
  have hstable : (prefixWord ++ tailWord_6433532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433532).length < 2 ^ (prefixWord ++ tailWord_6433532).sum := by decide
  have hdescent : baseEnd_6433532 < baseStart_6433532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433548 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_6433548 : Nat := 118140960795 + 6433548 * 2 ^ 59
def prefixEnd_6433548 : Nat := 4983230072969 + 3 ^ 40 * 6433548 * 2
def baseEnd_6433548 : Nat := 3303502437772099947562657

theorem tailTrace_6433548 : CollatzResearch.WordTrace tailWord_6433548 prefixEnd_6433548 3303502437772099947562657 := by
  unfold tailWord_6433548
  simp only [CollatzResearch.WordTrace]
  refine ⟨117325386448180916683278649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156433848597574555577704865 117325386448180916683278649)
  ·
    refine ⟨87994039836135687512458987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117325386448180916683278649 87994039836135687512458987)
    ·
      refine ⟨131991059754203531268688481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87994039836135687512458987 131991059754203531268688481)
      ·
        refine ⟨98993294815652648451516361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131991059754203531268688481 98993294815652648451516361)
        ·
          refine ⟨74244971111739486338637271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98993294815652648451516361 74244971111739486338637271)
          ·
            refine ⟨111367456667609229507955907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74244971111739486338637271 111367456667609229507955907)
            ·
              refine ⟨167051185001413844261933861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111367456667609229507955907 167051185001413844261933861)
              ·
                refine ⟨31322097187765095799112599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 167051185001413844261933861 31322097187765095799112599)
                ·
                  refine ⟨46983145781647643698668899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31322097187765095799112599 46983145781647643698668899)
                  ·
                    refine ⟨70474718672471465548003349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46983145781647643698668899 70474718672471465548003349)
                    ·
                      refine ⟨3303502437772099947562657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70474718672471465548003349 3303502437772099947562657)
                      ·
                        rfl

theorem cell23_6433548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_6433548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433548 prefixEnd_6433548 := by exact prefixLift 6433548
  have htrace : WordTrace (prefixWord ++ tailWord_6433548) baseStart_6433548 baseEnd_6433548 := by
    simpa [prefixWord, tailWord_6433548, baseEnd_6433548] using wordTrace_append hprefix tailTrace_6433548
  have hstable : (prefixWord ++ tailWord_6433548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433548).length < 2 ^ (prefixWord ++ tailWord_6433548).sum := by decide
  have hdescent : baseEnd_6433548 < baseStart_6433548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433585 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 3, 3, 3]
def baseStart_6433585 : Nat := 118140960795 + 6433585 * 2 ^ 59
def prefixEnd_6433585 : Nat := 4983230072969 + 3 ^ 40 * 6433585 * 2
def baseEnd_6433585 : Nat := 3303521436556316302799987

theorem tailTrace_6433585 : CollatzResearch.WordTrace tailWord_6433585 prefixEnd_6433585 3303521436556316302799987 := by
  unfold tailWord_6433585
  simp only [CollatzResearch.WordTrace]
  refine ⟨234652122397227788685654209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156434748264818525790436139 234652122397227788685654209)
  ·
    refine ⟨175989091797920841514240657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234652122397227788685654209 175989091797920841514240657)
    ·
      refine ⟨131991818848440631135680493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175989091797920841514240657 131991818848440631135680493)
      ·
        refine ⟨49496932068165236675880185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131991818848440631135680493 49496932068165236675880185)
        ·
          refine ⟨37122699051123927506910139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49496932068165236675880185 37122699051123927506910139)
          ·
            refine ⟨55684048576685891260365209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37122699051123927506910139 55684048576685891260365209)
            ·
              refine ⟨41763036432514418445273907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55684048576685891260365209 41763036432514418445273907)
              ·
                refine ⟨62644554648771627667910861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41763036432514418445273907 62644554648771627667910861)
                ·
                  refine ⟨23491707993289360375466573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62644554648771627667910861 23491707993289360375466573)
                  ·
                    refine ⟨8809390497483510140799965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23491707993289360375466573 8809390497483510140799965)
                    ·
                      refine ⟨3303521436556316302799987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8809390497483510140799965 3303521436556316302799987)
                      ·
                        rfl

theorem cell23_6433585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_6433585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433585 prefixEnd_6433585 := by exact prefixLift 6433585
  have htrace : WordTrace (prefixWord ++ tailWord_6433585) baseStart_6433585 baseEnd_6433585 := by
    simpa [prefixWord, tailWord_6433585, baseEnd_6433585] using wordTrace_append hprefix tailTrace_6433585
  have hstable : (prefixWord ++ tailWord_6433585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433585).length < 2 ^ (prefixWord ++ tailWord_6433585).sum := by decide
  have hdescent : baseEnd_6433585 < baseStart_6433585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433613 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_6433613 : Nat := 118140960795 + 6433613 * 2 ^ 59
def prefixEnd_6433613 : Nat := 4983230072969 + 3 ^ 40 * 6433613 * 2
def baseEnd_6433613 : Nat := 1101178604671547397749953

theorem tailTrace_6433613 : CollatzResearch.WordTrace tailWord_6433613 prefixEnd_6433613 1101178604671547397749953 := by
  unfold tailWord_6433613
  simp only [CollatzResearch.WordTrace]
  refine ⟨234653143641126349467673493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156435429094084232978448995 234653143641126349467673493)
  ·
    refine ⟨10999366108177797631297195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 234653143641126349467673493 10999366108177797631297195)
    ·
      refine ⟨16499049162266696446945793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10999366108177797631297195 16499049162266696446945793)
      ·
        refine ⟨12374286871700022335209345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16499049162266696446945793 12374286871700022335209345)
        ·
          refine ⟨9280715153775016751407009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12374286871700022335209345 9280715153775016751407009)
          ·
            refine ⟨6960536365331262563555257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9280715153775016751407009 6960536365331262563555257)
            ·
              refine ⟨5220402273998446922666443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6960536365331262563555257 5220402273998446922666443)
              ·
                refine ⟨7830603410997670383999665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5220402273998446922666443 7830603410997670383999665)
                ·
                  refine ⟨5872952558248252787999749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7830603410997670383999665 5872952558248252787999749)
                  ·
                    refine ⟨1101178604671547397749953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5872952558248252787999749 1101178604671547397749953)
                    ·
                      rfl

theorem cell23_6433613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_6433613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433613 prefixEnd_6433613 := by exact prefixLift 6433613
  have htrace : WordTrace (prefixWord ++ tailWord_6433613) baseStart_6433613 baseEnd_6433613 := by
    simpa [prefixWord, tailWord_6433613, baseEnd_6433613] using wordTrace_append hprefix tailTrace_6433613
  have hstable : (prefixWord ++ tailWord_6433613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433613).length < 2 ^ (prefixWord ++ tailWord_6433613).sum := by decide
  have hdescent : baseEnd_6433613 < baseStart_6433613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433659 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 2, 2, 2]
def baseStart_6433659 : Nat := 118140960795 + 6433659 * 2 ^ 59
def prefixEnd_6433659 : Nat := 4983230072969 + 3 ^ 40 * 6433659 * 2
def baseEnd_6433659 : Nat := 3303559434124749013274647

theorem tailTrace_6433659 : CollatzResearch.WordTrace tailWord_6433659 prefixEnd_6433659 3303559434124749013274647 := by
  unfold tailWord_6433659
  simp only [CollatzResearch.WordTrace]
  refine ⟨234654821398959699323848031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156436547599306466215898687 234654821398959699323848031)
  ·
    refine ⟨351982232098439548985772047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234654821398959699323848031 351982232098439548985772047)
    ·
      refine ⟨527973348147659323478658071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351982232098439548985772047 527973348147659323478658071)
      ·
        refine ⟨791960022221488985217987107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527973348147659323478658071 791960022221488985217987107)
        ·
          refine ⟨1187940033332233477826980661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791960022221488985217987107 1187940033332233477826980661)
          ·
            refine ⟨111369378124896888546279437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1187940033332233477826980661 111369378124896888546279437)
            ·
              refine ⟨41763516796836333204854789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111369378124896888546279437 41763516796836333204854789)
              ·
                refine ⟨7830659399406812475910273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41763516796836333204854789 7830659399406812475910273)
                ·
                  refine ⟨5872994549555109356932705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7830659399406812475910273 5872994549555109356932705)
                  ·
                    refine ⟨4404745912166332017699529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5872994549555109356932705 4404745912166332017699529)
                    ·
                      refine ⟨3303559434124749013274647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404745912166332017699529 3303559434124749013274647)
                      ·
                        rfl

theorem cell23_6433659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 2, 2].length) (baseStart_6433659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433659 prefixEnd_6433659 := by exact prefixLift 6433659
  have htrace : WordTrace (prefixWord ++ tailWord_6433659) baseStart_6433659 baseEnd_6433659 := by
    simpa [prefixWord, tailWord_6433659, baseEnd_6433659] using wordTrace_append hprefix tailTrace_6433659
  have hstable : (prefixWord ++ tailWord_6433659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433659).length < 2 ^ (prefixWord ++ tailWord_6433659).sum := by decide
  have hdescent : baseEnd_6433659 < baseStart_6433659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433672 : List Nat := [2, 1, 3, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_6433672 : Nat := 118140960795 + 6433672 * 2 ^ 59
def prefixEnd_6433672 : Nat := 4983230072969 + 3 ^ 40 * 6433672 * 2
def baseEnd_6433672 : Nat := 3303566109373257462412087

theorem tailTrace_6433672 : CollatzResearch.WordTrace tailWord_6433672 prefixEnd_6433672 3303566109373257462412087 := by
  unfold tailWord_6433672
  simp only [CollatzResearch.WordTrace]
  refine ⟨117327647773956301272035635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156436863698608401696047513 117327647773956301272035635)
  ·
    refine ⟨175991471660934451908053453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117327647773956301272035635 175991471660934451908053453)
    ·
      refine ⟨65996801872850419465520045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175991471660934451908053453 65996801872850419465520045)
      ·
        refine ⟨24748800702318907299570017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65996801872850419465520045 24748800702318907299570017)
        ·
          refine ⟨18561600526739180474677513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24748800702318907299570017 18561600526739180474677513)
          ·
            refine ⟨13921200395054385356008135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18561600526739180474677513 13921200395054385356008135)
            ·
              refine ⟨20881800592581578034012203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13921200395054385356008135 20881800592581578034012203)
              ·
                refine ⟨31322700888872367051018305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20881800592581578034012203 31322700888872367051018305)
                ·
                  refine ⟨23492025666654275288263729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31322700888872367051018305 23492025666654275288263729)
                  ·
                    refine ⟨17619019249990706466197797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23492025666654275288263729 17619019249990706466197797)
                    ·
                      refine ⟨3303566109373257462412087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17619019249990706466197797 3303566109373257462412087)
                      ·
                        rfl

theorem cell23_6433672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_6433672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433672 prefixEnd_6433672 := by exact prefixLift 6433672
  have htrace : WordTrace (prefixWord ++ tailWord_6433672) baseStart_6433672 baseEnd_6433672 := by
    simpa [prefixWord, tailWord_6433672, baseEnd_6433672] using wordTrace_append hprefix tailTrace_6433672
  have hstable : (prefixWord ++ tailWord_6433672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433672).length < 2 ^ (prefixWord ++ tailWord_6433672).sum := by decide
  have hdescent : baseEnd_6433672 < baseStart_6433672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433675 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 3]
def baseStart_6433675 : Nat := 118140960795 + 6433675 * 2 ^ 59
def prefixEnd_6433675 : Nat := 4983230072969 + 3 ^ 40 * 6433675 * 2
def baseEnd_6433675 : Nat := 3303567649815220950674573

theorem tailTrace_6433675 : CollatzResearch.WordTrace tailWord_6433675 prefixEnd_6433675 3303567649815220950674573 := by
  unfold tailWord_6433675
  simp only [CollatzResearch.WordTrace]
  refine ⟨234655404966901734056430479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156436936644601156037620319 234655404966901734056430479)
  ·
    refine ⟨351983107450352601084645719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234655404966901734056430479 351983107450352601084645719)
    ·
      refine ⟨527974661175528901626968579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351983107450352601084645719 527974661175528901626968579)
      ·
        refine ⟨791961991763293352440452869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527974661175528901626968579 791961991763293352440452869)
        ·
          refine ⟨148492873455617503582584913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 791961991763293352440452869 148492873455617503582584913)
          ·
            refine ⟨111369655091713127686938685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148492873455617503582584913 111369655091713127686938685)
            ·
              refine ⟨41763620659392422882602007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111369655091713127686938685 41763620659392422882602007)
              ·
                refine ⟨62645430989088634323903011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41763620659392422882602007 62645430989088634323903011)
                ·
                  refine ⟨93968146483632951485854517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62645430989088634323903011 93968146483632951485854517)
                  ·
                    refine ⟨8809513732840589201798861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93968146483632951485854517 8809513732840589201798861)
                    ·
                      refine ⟨3303567649815220950674573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8809513732840589201798861 3303567649815220950674573)
                      ·
                        rfl

theorem cell23_6433675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 3].length) (baseStart_6433675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433675 prefixEnd_6433675 := by exact prefixLift 6433675
  have htrace : WordTrace (prefixWord ++ tailWord_6433675) baseStart_6433675 baseEnd_6433675 := by
    simpa [prefixWord, tailWord_6433675, baseEnd_6433675] using wordTrace_append hprefix tailTrace_6433675
  have hstable : (prefixWord ++ tailWord_6433675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433675).length < 2 ^ (prefixWord ++ tailWord_6433675).sum := by decide
  have hdescent : baseEnd_6433675 < baseStart_6433675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433716 : List Nat := [2, 5, 2, 1, 1, 1, 2, 4, 5]
def baseStart_6433716 : Nat := 118140960795 + 6433716 * 2 ^ 59
def prefixEnd_6433716 : Nat := 4983230072969 + 3 ^ 40 * 6433716 * 2
def baseEnd_6433716 : Nat := 367065411391339476695765

theorem tailTrace_6433716 : CollatzResearch.WordTrace tailWord_6433716 prefixEnd_6433716 367065411391339476695765 := by
  unfold tailWord_6433716
  simp only [CollatzResearch.WordTrace]
  refine ⟨117328450179876599029336501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156437933573168798705782001 117328450179876599029336501)
  ·
    refine ⟨10999542204363431159000297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 117328450179876599029336501 10999542204363431159000297)
    ·
      refine ⟨8249656653272573369250223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10999542204363431159000297 8249656653272573369250223)
      ·
        refine ⟨12374484979908860053875335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8249656653272573369250223 12374484979908860053875335)
        ·
          refine ⟨18561727469863290080813003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12374484979908860053875335 18561727469863290080813003)
          ·
            refine ⟨27842591204794935121219505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18561727469863290080813003 27842591204794935121219505)
            ·
              refine ⟨20881943403596201340914629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27842591204794935121219505 20881943403596201340914629)
              ·
                refine ⟨3915364388174287751421493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20881943403596201340914629 3915364388174287751421493)
                ·
                  refine ⟨367065411391339476695765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3915364388174287751421493 367065411391339476695765)
                  ·
                    rfl

theorem cell23_6433716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_6433716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433716 prefixEnd_6433716 := by exact prefixLift 6433716
  have htrace : WordTrace (prefixWord ++ tailWord_6433716) baseStart_6433716 baseEnd_6433716 := by
    simpa [prefixWord, tailWord_6433716, baseEnd_6433716] using wordTrace_append hprefix tailTrace_6433716
  have hstable : (prefixWord ++ tailWord_6433716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433716).length < 2 ^ (prefixWord ++ tailWord_6433716).sum := by decide
  have hdescent : baseEnd_6433716 < baseStart_6433716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433745 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_6433745 : Nat := 118140960795 + 6433745 * 2 ^ 59
def prefixEnd_6433745 : Nat := 4983230072969 + 3 ^ 40 * 6433745 * 2
def baseEnd_6433745 : Nat := 3303603593461035676799251

theorem tailTrace_6433745 : CollatzResearch.WordTrace tailWord_6433745 prefixEnd_6433745 3303603593461035676799251 := by
  unfold tailWord_6433745
  simp only [CollatzResearch.WordTrace]
  refine ⟨234657958076648136011478689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156438638717765424007652459 234657958076648136011478689)
  ·
    refine ⟨175993468557486102008609017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234657958076648136011478689 175993468557486102008609017)
    ·
      refine ⟨131995101418114576506456763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175993468557486102008609017 131995101418114576506456763)
      ·
        refine ⟨197992652127171864759685145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131995101418114576506456763 197992652127171864759685145)
        ·
          refine ⟨148494489095378898569763859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197992652127171864759685145 148494489095378898569763859)
          ·
            refine ⟨222741733643068347854645789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148494489095378898569763859 222741733643068347854645789)
            ·
              refine ⟨83528150116150630445492171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222741733643068347854645789 83528150116150630445492171)
              ·
                refine ⟨125292225174225945668238257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83528150116150630445492171 125292225174225945668238257)
                ·
                  refine ⟨93969168880669459251178693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125292225174225945668238257 93969168880669459251178693)
                  ·
                    refine ⟨17619219165125523609596005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93969168880669459251178693 17619219165125523609596005)
                    ·
                      refine ⟨3303603593461035676799251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17619219165125523609596005 3303603593461035676799251)
                      ·
                        rfl

theorem cell23_6433745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_6433745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433745 prefixEnd_6433745 := by exact prefixLift 6433745
  have htrace : WordTrace (prefixWord ++ tailWord_6433745) baseStart_6433745 baseEnd_6433745 := by
    simpa [prefixWord, tailWord_6433745, baseEnd_6433745] using wordTrace_append hprefix tailTrace_6433745
  have hstable : (prefixWord ++ tailWord_6433745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433745).length < 2 ^ (prefixWord ++ tailWord_6433745).sum := by decide
  have hdescent : baseEnd_6433745 < baseStart_6433745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433752 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 1, 4, 3]
def baseStart_6433752 : Nat := 118140960795 + 6433752 * 2 ^ 59
def prefixEnd_6433752 : Nat := 4983230072969 + 3 ^ 40 * 6433752 * 2
def baseEnd_6433752 : Nat := 3303607187825617149411719

theorem tailTrace_6433752 : CollatzResearch.WordTrace tailWord_6433752 prefixEnd_6433752 3303607187825617149411719 := by
  unfold tailWord_6433752
  simp only [CollatzResearch.WordTrace]
  refine ⟨117329106693811388103491755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156438808925081850804655673 117329106693811388103491755)
  ·
    refine ⟨175993660040717082155237633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117329106693811388103491755 175993660040717082155237633)
    ·
      refine ⟨131995245030537811616428225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175993660040717082155237633 131995245030537811616428225)
      ·
        refine ⟨98996433772903358712321169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131995245030537811616428225 98996433772903358712321169)
        ·
          refine ⟨74247325329677519034240877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98996433772903358712321169 74247325329677519034240877)
          ·
            refine ⟨27842746998629069637840329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74247325329677519034240877 27842746998629069637840329)
            ·
              refine ⟨20882060248971802228380247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27842746998629069637840329 20882060248971802228380247)
              ·
                refine ⟨31323090373457703342570371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20882060248971802228380247 31323090373457703342570371)
                ·
                  refine ⟨46984635560186555013855557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31323090373457703342570371 46984635560186555013855557)
                  ·
                    refine ⟨8809619167534979065097917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46984635560186555013855557 8809619167534979065097917)
                    ·
                      refine ⟨3303607187825617149411719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8809619167534979065097917 3303607187825617149411719)
                      ·
                        rfl

theorem cell23_6433752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_6433752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433752 prefixEnd_6433752 := by exact prefixLift 6433752
  have htrace : WordTrace (prefixWord ++ tailWord_6433752) baseStart_6433752 baseEnd_6433752 := by
    simpa [prefixWord, tailWord_6433752, baseEnd_6433752] using wordTrace_append hprefix tailTrace_6433752
  have hstable : (prefixWord ++ tailWord_6433752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433752).length < 2 ^ (prefixWord ++ tailWord_6433752).sum := by decide
  have hdescent : baseEnd_6433752 < baseStart_6433752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433799 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_6433799 : Nat := 118140960795 + 6433799 * 2 ^ 59
def prefixEnd_6433799 : Nat := 4983230072969 + 3 ^ 40 * 6433799 * 2
def baseEnd_6433799 : Nat := 3303631321416378465524003

theorem tailTrace_6433799 : CollatzResearch.WordTrace tailWord_6433799 prefixEnd_6433799 3303631321416378465524003 := by
  unfold tailWord_6433799
  simp only [CollatzResearch.WordTrace]
  refine ⟨234659927618452503233944451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156439951745635002155962967 234659927618452503233944451)
  ·
    refine ⟨351989891427678754850916677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234659927618452503233944451 351989891427678754850916677)
    ·
      refine ⟨65998104642689766534546877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351989891427678754850916677 65998104642689766534546877)
      ·
        refine ⟨24749289241008662450455079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65998104642689766534546877 24749289241008662450455079)
        ·
          refine ⟨37123933861512993675682619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24749289241008662450455079 37123933861512993675682619)
          ·
            refine ⟨55685900792269490513523929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37123933861512993675682619 55685900792269490513523929)
            ·
              refine ⟨41764425594202117885142947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55685900792269490513523929 41764425594202117885142947)
              ·
                refine ⟨62646638391303176827714421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41764425594202117885142947 62646638391303176827714421)
                ·
                  refine ⟨5873122349184672827598227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62646638391303176827714421 5873122349184672827598227)
                  ·
                    refine ⟨8809683523777009241397341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5873122349184672827598227 8809683523777009241397341)
                    ·
                      refine ⟨3303631321416378465524003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8809683523777009241397341 3303631321416378465524003)
                      ·
                        rfl

theorem cell23_6433799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_6433799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433799 prefixEnd_6433799 := by exact prefixLift 6433799
  have htrace : WordTrace (prefixWord ++ tailWord_6433799) baseStart_6433799 baseEnd_6433799 := by
    simpa [prefixWord, tailWord_6433799, baseEnd_6433799] using wordTrace_append hprefix tailTrace_6433799
  have hstable : (prefixWord ++ tailWord_6433799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433799).length < 2 ^ (prefixWord ++ tailWord_6433799).sum := by decide
  have hdescent : baseEnd_6433799 < baseStart_6433799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433826 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_6433826 : Nat := 118140960795 + 6433826 * 2 ^ 59
def prefixEnd_6433826 : Nat := 4983230072969 + 3 ^ 40 * 6433826 * 2
def baseEnd_6433826 : Nat := 3303645185394049859886379

theorem tailTrace_6433826 : CollatzResearch.WordTrace tailWord_6433826 prefixEnd_6433826 3303645185394049859886379 := by
  unfold tailWord_6433826
  simp only [CollatzResearch.WordTrace]
  refine ⟨58665228097338671711294333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156440608259569791230118221 58665228097338671711294333)
  ·
    refine ⟨21999460536502001891735375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58665228097338671711294333 21999460536502001891735375)
    ·
      refine ⟨32999190804753002837603063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21999460536502001891735375 32999190804753002837603063)
      ·
        refine ⟨49498786207129504256404595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32999190804753002837603063 49498786207129504256404595)
        ·
          refine ⟨74248179310694256384606893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49498786207129504256404595 74248179310694256384606893)
          ·
            refine ⟨27843067241510346144227585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74248179310694256384606893 27843067241510346144227585)
            ·
              refine ⟨20882300431132759608170689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27843067241510346144227585 20882300431132759608170689)
              ·
                refine ⟨15661725323349569706128017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20882300431132759608170689 15661725323349569706128017)
                ·
                  refine ⟨11746293992512177279596013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15661725323349569706128017 11746293992512177279596013)
                  ·
                    refine ⟨4404860247192066479848505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11746293992512177279596013 4404860247192066479848505)
                    ·
                      refine ⟨3303645185394049859886379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404860247192066479848505 3303645185394049859886379)
                      ·
                        rfl

theorem cell23_6433826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_6433826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433826 prefixEnd_6433826 := by exact prefixLift 6433826
  have htrace : WordTrace (prefixWord ++ tailWord_6433826) baseStart_6433826 baseEnd_6433826 := by
    simpa [prefixWord, tailWord_6433826, baseEnd_6433826] using wordTrace_append hprefix tailTrace_6433826
  have hstable : (prefixWord ++ tailWord_6433826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433826).length < 2 ^ (prefixWord ++ tailWord_6433826).sum := by decide
  have hdescent : baseEnd_6433826 < baseStart_6433826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433842 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_6433842 : Nat := 118140960795 + 6433842 * 2 ^ 59
def prefixEnd_6433842 : Nat := 4983230072969 + 3 ^ 40 * 6433842 * 2
def baseEnd_6433842 : Nat := 3303653401084521797286305

theorem tailTrace_6433842 : CollatzResearch.WordTrace tailWord_6433842 prefixEnd_6433842 3303653401084521797286305 := by
  unfold tailWord_6433842
  simp only [CollatzResearch.WordTrace]
  refine ⟨58665373989324180394439945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156440997304864481051839853 58665373989324180394439945)
  ·
    refine ⟨43999030491993135295829959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58665373989324180394439945 43999030491993135295829959)
    ·
      refine ⟨65998545737989702943744939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43999030491993135295829959 65998545737989702943744939)
      ·
        refine ⟨98997818606984554415617409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65998545737989702943744939 98997818606984554415617409)
        ·
          refine ⟨74248363955238415811713057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98997818606984554415617409 74248363955238415811713057)
          ·
            refine ⟨55686272966428811858784793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74248363955238415811713057 55686272966428811858784793)
            ·
              refine ⟨41764704724821608894088595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55686272966428811858784793 41764704724821608894088595)
              ·
                refine ⟨62647057087232413341132893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41764704724821608894088595 62647057087232413341132893)
                ·
                  refine ⟨23492646407712155002924835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62647057087232413341132893 23492646407712155002924835)
                  ·
                    refine ⟨35238969611568232504387253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23492646407712155002924835 35238969611568232504387253)
                    ·
                      refine ⟨3303653401084521797286305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35238969611568232504387253 3303653401084521797286305)
                      ·
                        rfl

theorem cell23_6433842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_6433842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433842 prefixEnd_6433842 := by exact prefixLift 6433842
  have htrace : WordTrace (prefixWord ++ tailWord_6433842) baseStart_6433842 baseEnd_6433842 := by
    simpa [prefixWord, tailWord_6433842, baseEnd_6433842] using wordTrace_append hprefix tailTrace_6433842
  have hstable : (prefixWord ++ tailWord_6433842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433842).length < 2 ^ (prefixWord ++ tailWord_6433842).sum := by decide
  have hdescent : baseEnd_6433842 < baseStart_6433842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433849 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 1, 6]
def baseStart_6433849 : Nat := 118140960795 + 6433849 * 2 ^ 59
def prefixEnd_6433849 : Nat := 4983230072969 + 3 ^ 40 * 6433849 * 2
def baseEnd_6433849 : Nat := 1101218998483034423299591

theorem tailTrace_6433849 : CollatzResearch.WordTrace tailWord_6433849 prefixEnd_6433849 1101218998483034423299591 := by
  unfold tailWord_6433849
  simp only [CollatzResearch.WordTrace]
  refine ⟨234661751268271361773264601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156441167512180907848843067 234661751268271361773264601)
  ·
    refine ⟨175996313451203521329948451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234661751268271361773264601 175996313451203521329948451)
    ·
      refine ⟨263994470176805281994922677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175996313451203521329948451 263994470176805281994922677)
      ·
        refine ⟨24749481579075495187024001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 263994470176805281994922677 24749481579075495187024001)
        ·
          refine ⟨18562111184306621390268001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24749481579075495187024001 18562111184306621390268001)
          ·
            refine ⟨13921583388229966042701001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18562111184306621390268001 13921583388229966042701001)
            ·
              refine ⟨10441187541172474532025751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13921583388229966042701001 10441187541172474532025751)
              ·
                refine ⟨15661781311758711798038627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10441187541172474532025751 15661781311758711798038627)
                ·
                  refine ⟨23492671967638067697057941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15661781311758711798038627 23492671967638067697057941)
                  ·
                    refine ⟨1101218998483034423299591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23492671967638067697057941 1101218998483034423299591)
                    ·
                      rfl

theorem cell23_6433849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 6].length) (baseStart_6433849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433849 prefixEnd_6433849 := by exact prefixLift 6433849
  have htrace : WordTrace (prefixWord ++ tailWord_6433849) baseStart_6433849 baseEnd_6433849 := by
    simpa [prefixWord, tailWord_6433849, baseEnd_6433849] using wordTrace_append hprefix tailTrace_6433849
  have hstable : (prefixWord ++ tailWord_6433849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433849).length < 2 ^ (prefixWord ++ tailWord_6433849).sum := by decide
  have hdescent : baseEnd_6433849 < baseStart_6433849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433856 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 3, 2, 2]
def baseStart_6433856 : Nat := 118140960795 + 6433856 * 2 ^ 59
def prefixEnd_6433856 : Nat := 4983230072969 + 3 ^ 40 * 6433856 * 2
def baseEnd_6433856 : Nat := 3303660589813684742511241

theorem tailTrace_6433856 : CollatzResearch.WordTrace tailWord_6433856 prefixEnd_6433856 3303660589813684742511241 := by
  unfold tailWord_6433856
  simp only [CollatzResearch.WordTrace]
  refine ⟨117331003289623000984384711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156441337719497334645846281 117331003289623000984384711)
  ·
    refine ⟨175996504934434501476577067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117331003289623000984384711 175996504934434501476577067)
    ·
      refine ⟨263994757401651752214865601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175996504934434501476577067 263994757401651752214865601)
      ·
        refine ⟨197996068051238814161149201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263994757401651752214865601 197996068051238814161149201)
        ·
          refine ⟨148497051038429110620861901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197996068051238814161149201 148497051038429110620861901)
          ·
            refine ⟨55686394139410916482823213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148497051038429110620861901 55686394139410916482823213)
            ·
              refine ⟨20882397802279093681058705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55686394139410916482823213 20882397802279093681058705)
              ·
                refine ⟨15661798351709320260794029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20882397802279093681058705 15661798351709320260794029)
                ·
                  refine ⟨5873174381890995097797761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15661798351709320260794029 5873174381890995097797761)
                  ·
                    refine ⟨4404880786418246323348321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5873174381890995097797761 4404880786418246323348321)
                    ·
                      refine ⟨3303660589813684742511241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404880786418246323348321 3303660589813684742511241)
                      ·
                        rfl

theorem cell23_6433856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 3, 2, 2].length) (baseStart_6433856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433856 prefixEnd_6433856 := by exact prefixLift 6433856
  have htrace : WordTrace (prefixWord ++ tailWord_6433856) baseStart_6433856 baseEnd_6433856 := by
    simpa [prefixWord, tailWord_6433856, baseEnd_6433856] using wordTrace_append hprefix tailTrace_6433856
  have hstable : (prefixWord ++ tailWord_6433856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433856).length < 2 ^ (prefixWord ++ tailWord_6433856).sum := by decide
  have hdescent : baseEnd_6433856 < baseStart_6433856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433859 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 1, 2, 3]
def baseStart_6433859 : Nat := 118140960795 + 6433859 * 2 ^ 59
def prefixEnd_6433859 : Nat := 4983230072969 + 3 ^ 40 * 6433859 * 2
def baseEnd_6433859 : Nat := 3303662130255648230773727

theorem tailTrace_6433859 : CollatzResearch.WordTrace tailWord_6433859 prefixEnd_6433859 3303662130255648230773727 := by
  unfold tailWord_6433859
  simp only [CollatzResearch.WordTrace]
  refine ⟨234662115998235133481128631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156441410665490088987419087 234662115998235133481128631)
  ·
    refine ⟨351993173997352700221692947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234662115998235133481128631 351993173997352700221692947)
    ·
      refine ⟨527989760996029050332539421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351993173997352700221692947 527989760996029050332539421)
      ·
        refine ⟨197996160373510893874702283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 527989760996029050332539421 197996160373510893874702283)
        ·
          refine ⟨296994240560266340812053425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197996160373510893874702283 296994240560266340812053425)
          ·
            refine ⟨222745680420199755609040069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296994240560266340812053425 222745680420199755609040069)
            ·
              refine ⟨41764815078787454176695013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222745680420199755609040069 41764815078787454176695013)
              ·
                refine ⟨7830902827272647658130315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41764815078787454176695013 7830902827272647658130315)
                ·
                  refine ⟨11746354240908971487195473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7830902827272647658130315 11746354240908971487195473)
                  ·
                    refine ⟨8809765680681728615396605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11746354240908971487195473 8809765680681728615396605)
                    ·
                      refine ⟨3303662130255648230773727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8809765680681728615396605 3303662130255648230773727)
                      ·
                        rfl

theorem cell23_6433859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 2, 3].length) (baseStart_6433859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433859 prefixEnd_6433859 := by exact prefixLift 6433859
  have htrace : WordTrace (prefixWord ++ tailWord_6433859) baseStart_6433859 baseEnd_6433859 := by
    simpa [prefixWord, tailWord_6433859, baseEnd_6433859] using wordTrace_append hprefix tailTrace_6433859
  have hstable : (prefixWord ++ tailWord_6433859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433859).length < 2 ^ (prefixWord ++ tailWord_6433859).sum := by decide
  have hdescent : baseEnd_6433859 < baseStart_6433859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433873 : List Nat := [1, 2, 2, 1, 3, 1, 3, 5, 1, 2, 2]
def baseStart_6433873 : Nat := 118140960795 + 6433873 * 2 ^ 59
def prefixEnd_6433873 : Nat := 4983230072969 + 3 ^ 40 * 6433873 * 2
def baseEnd_6433873 : Nat := 3303669318984811175998663

theorem tailTrace_6433873 : CollatzResearch.WordTrace tailWord_6433873 prefixEnd_6433873 3303669318984811175998663 := by
  unfold tailWord_6433873
  simp only [CollatzResearch.WordTrace]
  refine ⟨234662626620184413872138273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156441751080122942581425515 234662626620184413872138273)
  ·
    refine ⟨175996969965138310404103705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234662626620184413872138273 175996969965138310404103705)
    ·
      refine ⟨131997727473853732803077779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175996969965138310404103705 131997727473853732803077779)
      ·
        refine ⟨197996591210780599204616669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131997727473853732803077779 197996591210780599204616669)
        ·
          refine ⟨74248721704042724701731251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197996591210780599204616669 74248721704042724701731251)
          ·
            refine ⟨111373082556064087052596877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74248721704042724701731251 111373082556064087052596877)
            ·
              refine ⟨41764905958524032644723829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111373082556064087052596877 41764905958524032644723829)
              ·
                refine ⟨3915459933611628060442859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41764905958524032644723829 3915459933611628060442859)
                ·
                  refine ⟨5873189900417442090664289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3915459933611628060442859 5873189900417442090664289)
                  ·
                    refine ⟨4404892425313081567998217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5873189900417442090664289 4404892425313081567998217)
                    ·
                      refine ⟨3303669318984811175998663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404892425313081567998217 3303669318984811175998663)
                      ·
                        rfl

theorem cell23_6433873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 1, 2, 2].length) (baseStart_6433873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433873 prefixEnd_6433873 := by exact prefixLift 6433873
  have htrace : WordTrace (prefixWord ++ tailWord_6433873) baseStart_6433873 baseEnd_6433873 := by
    simpa [prefixWord, tailWord_6433873, baseEnd_6433873] using wordTrace_append hprefix tailTrace_6433873
  have hstable : (prefixWord ++ tailWord_6433873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433873).length < 2 ^ (prefixWord ++ tailWord_6433873).sum := by decide
  have hdescent : baseEnd_6433873 < baseStart_6433873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433890 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_6433890 : Nat := 118140960795 + 6433890 * 2 ^ 59
def prefixEnd_6433890 : Nat := 4983230072969 + 3 ^ 40 * 6433890 * 2
def baseEnd_6433890 : Nat := 3303678048155937609486085

theorem tailTrace_6433890 : CollatzResearch.WordTrace tailWord_6433890 prefixEnd_6433890 3303678048155937609486085 := by
  unfold tailWord_6433890
  simp only [CollatzResearch.WordTrace]
  refine ⟨58665811665280706443876781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156442164440748550517004749 58665811665280706443876781)
  ·
    refine ⟨21999679374480264916453793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58665811665280706443876781 21999679374480264916453793)
    ·
      refine ⟨16499759530860198687340345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21999679374480264916453793 16499759530860198687340345)
      ·
        refine ⟨12374819648145149015505259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16499759530860198687340345 12374819648145149015505259)
        ·
          refine ⟨18562229472217723523257889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12374819648145149015505259 18562229472217723523257889)
          ·
            refine ⟨13921672104163292642443417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18562229472217723523257889 13921672104163292642443417)
            ·
              refine ⟨10441254078122469481832563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13921672104163292642443417 10441254078122469481832563)
              ·
                refine ⟨15661881117183704222748845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10441254078122469481832563 15661881117183704222748845)
                ·
                  refine ⟨5873205418943889083530817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15661881117183704222748845 5873205418943889083530817)
                  ·
                    refine ⟨4404904064207916812648113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5873205418943889083530817 4404904064207916812648113)
                    ·
                      refine ⟨3303678048155937609486085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4404904064207916812648113 3303678048155937609486085)
                      ·
                        rfl

theorem cell23_6433890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_6433890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433890 prefixEnd_6433890 := by exact prefixLift 6433890
  have htrace : WordTrace (prefixWord ++ tailWord_6433890) baseStart_6433890 baseEnd_6433890 := by
    simpa [prefixWord, tailWord_6433890, baseEnd_6433890] using wordTrace_append hprefix tailTrace_6433890
  have hstable : (prefixWord ++ tailWord_6433890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433890).length < 2 ^ (prefixWord ++ tailWord_6433890).sum := by decide
  have hdescent : baseEnd_6433890 < baseStart_6433890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433912 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_6433912 : Nat := 118140960795 + 6433912 * 2 ^ 59
def prefixEnd_6433912 : Nat := 4983230072969 + 3 ^ 40 * 6433912 * 2
def baseEnd_6433912 : Nat := 3303689344730336523410983

theorem tailTrace_6433912 : CollatzResearch.WordTrace tailWord_6433912 prefixEnd_6433912 3303689344730336523410983 := by
  unfold tailWord_6433912
  simp only [CollatzResearch.WordTrace]
  refine ⟨117332024533521561766403995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156442699378028749021871993 117332024533521561766403995)
  ·
    refine ⟨175998036800282342649605993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117332024533521561766403995 175998036800282342649605993)
    ·
      refine ⟨131998527600211756987204495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175998036800282342649605993 131998527600211756987204495)
      ·
        refine ⟨197997791400317635480806743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131998527600211756987204495 197997791400317635480806743)
        ·
          refine ⟨296996687100476453221210115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197997791400317635480806743 296996687100476453221210115)
          ·
            refine ⟨445495030650714679831815173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296996687100476453221210115 445495030650714679831815173)
            ·
              refine ⟨83530318247009002468465345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 445495030650714679831815173 83530318247009002468465345)
              ·
                refine ⟨62647738685256751851349009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83530318247009002468465345 62647738685256751851349009)
                ·
                  refine ⟨46985804013942563888511757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62647738685256751851349009 46985804013942563888511757)
                  ·
                    refine ⟨17619676505228461458191909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46985804013942563888511757 17619676505228461458191909)
                    ·
                      refine ⟨3303689344730336523410983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17619676505228461458191909 3303689344730336523410983)
                      ·
                        rfl

theorem cell23_6433912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_6433912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433912 prefixEnd_6433912 := by exact prefixLift 6433912
  have htrace : WordTrace (prefixWord ++ tailWord_6433912) baseStart_6433912 baseEnd_6433912 := by
    simpa [prefixWord, tailWord_6433912, baseEnd_6433912] using wordTrace_append hprefix tailTrace_6433912
  have hstable : (prefixWord ++ tailWord_6433912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433912).length < 2 ^ (prefixWord ++ tailWord_6433912).sum := by decide
  have hdescent : baseEnd_6433912 < baseStart_6433912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6433949 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_6433949 : Nat := 118140960795 + 6433949 * 2 ^ 59
def prefixEnd_6433949 : Nat := 4983230072969 + 3 ^ 40 * 6433949 * 2
def baseEnd_6433949 : Nat := 3303708343514552878648313

theorem tailTrace_6433949 : CollatzResearch.WordTrace tailWord_6433949 prefixEnd_6433949 3303708343514552878648313 := by
  unfold tailWord_6433949
  simp only [CollatzResearch.WordTrace]
  refine ⟨234665398567909078851904901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156443599045272719234603267 234665398567909078851904901)
  ·
    refine ⟨43999762231482952284732169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234665398567909078851904901 43999762231482952284732169)
    ·
      refine ⟨32999821673612214213549127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43999762231482952284732169 32999821673612214213549127)
      ·
        refine ⟨49499732510418321320323691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32999821673612214213549127 49499732510418321320323691)
        ·
          refine ⟨74249598765627481980485537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49499732510418321320323691 74249598765627481980485537)
          ·
            refine ⟨55687199074220611485364153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74249598765627481980485537 55687199074220611485364153)
            ·
              refine ⟨41765399305665458614023115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55687199074220611485364153 41765399305665458614023115)
              ·
                refine ⟨62648098958498187921034673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41765399305665458614023115 62648098958498187921034673)
                ·
                  refine ⟨46986074218873640940776005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62648098958498187921034673 46986074218873640940776005)
                  ·
                    refine ⟨8809888916038807676395501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46986074218873640940776005 8809888916038807676395501)
                    ·
                      refine ⟨3303708343514552878648313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8809888916038807676395501 3303708343514552878648313)
                      ·
                        rfl

theorem cell23_6433949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_6433949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6433949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6433949 prefixEnd_6433949 := by exact prefixLift 6433949
  have htrace : WordTrace (prefixWord ++ tailWord_6433949) baseStart_6433949 baseEnd_6433949 := by
    simpa [prefixWord, tailWord_6433949, baseEnd_6433949] using wordTrace_append hprefix tailTrace_6433949
  have hstable : (prefixWord ++ tailWord_6433949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6433949).length < 2 ^ (prefixWord ++ tailWord_6433949).sum := by decide
  have hdescent : baseEnd_6433949 < baseStart_6433949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6433949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434013 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_6434013 : Nat := 118140960795 + 6434013 * 2 ^ 59
def prefixEnd_6434013 : Nat := 4983230072969 + 3 ^ 40 * 6434013 * 2
def baseEnd_6434013 : Nat := 3303741206276440628248019

theorem tailTrace_6434013 : CollatzResearch.WordTrace tailWord_6434013 prefixEnd_6434013 3303741206276440628248019 := by
  unfold tailWord_6434013
  simp only [CollatzResearch.WordTrace]
  refine ⟨234667732839677217782234693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156445155226451478521489795 234667732839677217782234693)
  ·
    refine ⟨44000199907439478334169005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234667732839677217782234693 44000199907439478334169005)
    ·
      refine ⟨16500074965289804375313377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44000199907439478334169005 16500074965289804375313377)
      ·
        refine ⟨12375056223967353281485033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16500074965289804375313377 12375056223967353281485033)
        ·
          refine ⟨9281292167975514961113775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12375056223967353281485033 9281292167975514961113775)
          ·
            refine ⟨13921938251963272441670663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9281292167975514961113775 13921938251963272441670663)
            ·
              refine ⟨20882907377944908662505995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13921938251963272441670663 20882907377944908662505995)
              ·
                refine ⟨31324361066917362993758993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20882907377944908662505995 31324361066917362993758993)
                ·
                  refine ⟨23493270800188022245319245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31324361066917362993758993 23493270800188022245319245)
                  ·
                    refine ⟨8809976550070508341994717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23493270800188022245319245 8809976550070508341994717)
                    ·
                      refine ⟨3303741206276440628248019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8809976550070508341994717 3303741206276440628248019)
                      ·
                        rfl

theorem cell23_6434013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_6434013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434013 prefixEnd_6434013 := by exact prefixLift 6434013
  have htrace : WordTrace (prefixWord ++ tailWord_6434013) baseStart_6434013 baseEnd_6434013 := by
    simpa [prefixWord, tailWord_6434013, baseEnd_6434013] using wordTrace_append hprefix tailTrace_6434013
  have hstable : (prefixWord ++ tailWord_6434013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434013).length < 2 ^ (prefixWord ++ tailWord_6434013).sum := by decide
  have hdescent : baseEnd_6434013 < baseStart_6434013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434039 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 3]
def baseStart_6434039 : Nat := 118140960795 + 6434039 * 2 ^ 59
def prefixEnd_6434039 : Nat := 4983230072969 + 3 ^ 40 * 6434039 * 2
def baseEnd_6434039 : Nat := 3303754556773457526522899

theorem tailTrace_6434039 : CollatzResearch.WordTrace tailWord_6434039 prefixEnd_6434039 3303754556773457526522899 := by
  unfold tailWord_6434039
  simp only [CollatzResearch.WordTrace]
  refine ⟨234668681137583024222681171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156445787425055349481787447 234668681137583024222681171)
  ·
    refine ⟨352003021706374536334021757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234668681137583024222681171 352003021706374536334021757)
    ·
      refine ⟨132001133139890451125258159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 352003021706374536334021757 132001133139890451125258159)
      ·
        refine ⟨198001699709835676687887239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132001133139890451125258159 198001699709835676687887239)
        ·
          refine ⟨297002549564753515031830859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198001699709835676687887239 297002549564753515031830859)
          ·
            refine ⟨445503824347130272547746289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297002549564753515031830859 445503824347130272547746289)
            ·
              refine ⟨334127868260347704410809717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 445503824347130272547746289 334127868260347704410809717)
              ·
                refine ⟨31324487649407597288513411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 334127868260347704410809717 31324487649407597288513411)
                ·
                  refine ⟨46986731474111395932770117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31324487649407597288513411 46986731474111395932770117)
                  ·
                    refine ⟨8810012151395886737394397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46986731474111395932770117 8810012151395886737394397)
                    ·
                      refine ⟨3303754556773457526522899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8810012151395886737394397 3303754556773457526522899)
                      ·
                        rfl

theorem cell23_6434039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_6434039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434039 prefixEnd_6434039 := by exact prefixLift 6434039
  have htrace : WordTrace (prefixWord ++ tailWord_6434039) baseStart_6434039 baseEnd_6434039 := by
    simpa [prefixWord, tailWord_6434039, baseEnd_6434039] using wordTrace_append hprefix tailTrace_6434039
  have hstable : (prefixWord ++ tailWord_6434039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434039).length < 2 ^ (prefixWord ++ tailWord_6434039).sum := by decide
  have hdescent : baseEnd_6434039 < baseStart_6434039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434049 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_6434049 : Nat := 118140960795 + 6434049 * 2 ^ 59
def prefixEnd_6434049 : Nat := 4983230072969 + 3 ^ 40 * 6434049 * 2
def baseEnd_6434049 : Nat := 3303759691580002487397853

theorem tailTrace_6434049 : CollatzResearch.WordTrace tailWord_6434049 prefixEnd_6434049 3303759691580002487397853 := by
  unfold tailWord_6434049
  simp only [CollatzResearch.WordTrace]
  refine ⟨234669045867546795930545201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156446030578364530620363467 234669045867546795930545201)
  ·
    refine ⟨176001784400660096947908901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234669045867546795930545201 176001784400660096947908901)
    ·
      refine ⟨33000334575123768177732919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176001784400660096947908901 33000334575123768177732919)
      ·
        refine ⟨49500501862685652266599379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33000334575123768177732919 49500501862685652266599379)
        ·
          refine ⟨74250752794028478399899069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49500501862685652266599379 74250752794028478399899069)
          ·
            refine ⟨27844032297760679399962151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74250752794028478399899069 27844032297760679399962151)
            ·
              refine ⟨41766048446641019099943227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27844032297760679399962151 41766048446641019099943227)
              ·
                refine ⟨62649072669961528649914841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41766048446641019099943227 62649072669961528649914841)
                ·
                  refine ⟨46986804502471146487436131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62649072669961528649914841 46986804502471146487436131)
                  ·
                    refine ⟨70480206753706719731154197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46986804502471146487436131 70480206753706719731154197)
                    ·
                      refine ⟨3303759691580002487397853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70480206753706719731154197 3303759691580002487397853)
                      ·
                        rfl

theorem cell23_6434049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_6434049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434049 prefixEnd_6434049 := by exact prefixLift 6434049
  have htrace : WordTrace (prefixWord ++ tailWord_6434049) baseStart_6434049 baseEnd_6434049 := by
    simpa [prefixWord, tailWord_6434049, baseEnd_6434049] using wordTrace_append hprefix tailTrace_6434049
  have hstable : (prefixWord ++ tailWord_6434049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434049).length < 2 ^ (prefixWord ++ tailWord_6434049).sum := by decide
  have hdescent : baseEnd_6434049 < baseStart_6434049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434059 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 8]
def baseStart_6434059 : Nat := 118140960795 + 6434059 * 2 ^ 59
def prefixEnd_6434059 : Nat := 4983230072969 + 3 ^ 40 * 6434059 * 2
def baseEnd_6434059 : Nat := 367084980709616383141423

theorem tailTrace_6434059 : CollatzResearch.WordTrace tailWord_6434059 prefixEnd_6434059 367084980709616383141423 := by
  unfold tailWord_6434059
  simp only [CollatzResearch.WordTrace]
  refine ⟨234669410597510567638409231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156446273731673711758939487 234669410597510567638409231)
  ·
    refine ⟨352004115896265851457613847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234669410597510567638409231 352004115896265851457613847)
    ·
      refine ⟨528006173844398777186420771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352004115896265851457613847 528006173844398777186420771)
      ·
        refine ⟨792009260766598165779631157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528006173844398777186420771 792009260766598165779631157)
        ·
          refine ⟨74250868196868578041840421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 792009260766598165779631157 74250868196868578041840421)
          ·
            refine ⟨13922037786912858382845079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74250868196868578041840421 13922037786912858382845079)
            ·
              refine ⟨20883056680369287574267619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13922037786912858382845079 20883056680369287574267619)
              ·
                refine ⟨31324585020553931361401429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20883056680369287574267619 31324585020553931361401429)
                ·
                  refine ⟨367084980709616383141423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31324585020553931361401429 367084980709616383141423)
                  ·
                    rfl

theorem cell23_6434059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 8].length) (baseStart_6434059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434059 prefixEnd_6434059 := by exact prefixLift 6434059
  have htrace : WordTrace (prefixWord ++ tailWord_6434059) baseStart_6434059 baseEnd_6434059 := by
    simpa [prefixWord, tailWord_6434059, baseEnd_6434059] using wordTrace_append hprefix tailTrace_6434059
  have hstable : (prefixWord ++ tailWord_6434059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434059).length < 2 ^ (prefixWord ++ tailWord_6434059).sum := by decide
  have hdescent : baseEnd_6434059 < baseStart_6434059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434096 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 1, 5, 2]
def baseStart_6434096 : Nat := 118140960795 + 6434096 * 2 ^ 59
def prefixEnd_6434096 : Nat := 4983230072969 + 3 ^ 40 * 6434096 * 2
def baseEnd_6434096 : Nat := 3303783825170763803510137

theorem tailTrace_6434096 : CollatzResearch.WordTrace tailWord_6434096 prefixEnd_6434096 3303783825170763803510137 := by
  unfold tailWord_6434096
  simp only [CollatzResearch.WordTrace]
  refine ⟨117335380049188261478753071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156447173398917681971670761 117335380049188261478753071)
  ·
    refine ⟨176003070073782392218129607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117335380049188261478753071 176003070073782392218129607)
    ·
      refine ⟨264004605110673588327194411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176003070073782392218129607 264004605110673588327194411)
      ·
        refine ⟨396006907666010382490791617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264004605110673588327194411 396006907666010382490791617)
        ·
          refine ⟨297005180749507786868093713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396006907666010382490791617 297005180749507786868093713)
          ·
            refine ⟨222753885562130840151070285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297005180749507786868093713 222753885562130840151070285)
            ·
              refine ⟨83532707085799065056651357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222753885562130840151070285 83532707085799065056651357)
              ·
                refine ⟨31324765157174649396244259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83532707085799065056651357 31324765157174649396244259)
                ·
                  refine ⟨46987147735761974094366389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31324765157174649396244259 46987147735761974094366389)
                  ·
                    refine ⟨4405045100227685071346849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46987147735761974094366389 4405045100227685071346849)
                    ·
                      refine ⟨3303783825170763803510137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405045100227685071346849 3303783825170763803510137)
                      ·
                        rfl

theorem cell23_6434096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 1, 5, 2].length) (baseStart_6434096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434096 prefixEnd_6434096 := by exact prefixLift 6434096
  have htrace : WordTrace (prefixWord ++ tailWord_6434096) baseStart_6434096 baseEnd_6434096 := by
    simpa [prefixWord, tailWord_6434096, baseEnd_6434096] using wordTrace_append hprefix tailTrace_6434096
  have hstable : (prefixWord ++ tailWord_6434096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434096).length < 2 ^ (prefixWord ++ tailWord_6434096).sum := by decide
  have hdescent : baseEnd_6434096 < baseStart_6434096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434106 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 1, 5]
def baseStart_6434106 : Nat := 118140960795 + 6434106 * 2 ^ 59
def prefixEnd_6434106 : Nat := 4983230072969 + 3 ^ 40 * 6434106 * 2
def baseEnd_6434106 : Nat := 1101262986659102921461697

theorem tailTrace_6434106 : CollatzResearch.WordTrace tailWord_6434106 prefixEnd_6434106 1101262986659102921461697 := by
  unfold tailWord_6434106
  simp only [CollatzResearch.WordTrace]
  refine ⟨58667781207085073666342543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156447416552226863110246781 58667781207085073666342543)
  ·
    refine ⟨88001671810627610499513815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58667781207085073666342543 88001671810627610499513815)
    ·
      refine ⟨132002507715941415749270723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88001671810627610499513815 132002507715941415749270723)
      ·
        refine ⟨198003761573912123623906085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132002507715941415749270723 198003761573912123623906085)
        ·
          refine ⟨37125705295108523179482391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 198003761573912123623906085 37125705295108523179482391)
          ·
            refine ⟨55688557942662784769223587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37125705295108523179482391 55688557942662784769223587)
            ·
              refine ⟨83532836913994177153835381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55688557942662784769223587 83532836913994177153835381)
              ·
                refine ⟨7831203460686954108172067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83532836913994177153835381 7831203460686954108172067)
                ·
                  refine ⟨11746805191030431162258101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7831203460686954108172067 11746805191030431162258101)
                  ·
                    refine ⟨1101262986659102921461697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11746805191030431162258101 1101262986659102921461697)
                    ·
                      rfl

theorem cell23_6434106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_6434106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434106 prefixEnd_6434106 := by exact prefixLift 6434106
  have htrace : WordTrace (prefixWord ++ tailWord_6434106) baseStart_6434106 baseEnd_6434106 := by
    simpa [prefixWord, tailWord_6434106, baseEnd_6434106] using wordTrace_append hprefix tailTrace_6434106
  have hstable : (prefixWord ++ tailWord_6434106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434106).length < 2 ^ (prefixWord ++ tailWord_6434106).sum := by decide
  have hdescent : baseEnd_6434106 < baseStart_6434106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434126 : List Nat := [4, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_6434126 : Nat := 118140960795 + 6434126 * 2 ^ 59
def prefixEnd_6434126 : Nat := 4983230072969 + 3 ^ 40 * 6434126 * 2
def baseEnd_6434126 : Nat := 3303799229590398686134999

theorem tailTrace_6434126 : CollatzResearch.WordTrace tailWord_6434126 prefixEnd_6434126 3303799229590398686134999 := by
  unfold tailWord_6434126
  simp only [CollatzResearch.WordTrace]
  refine ⟨29333981786033479760137279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156447902858845225387398821 29333981786033479760137279)
  ·
    refine ⟨44000972679050219640205919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29333981786033479760137279 44000972679050219640205919)
    ·
      refine ⟨66001459018575329460308879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44000972679050219640205919 66001459018575329460308879)
      ·
        refine ⟨99002188527862994190463319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66001459018575329460308879 99002188527862994190463319)
        ·
          refine ⟨148503282791794491285694979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99002188527862994190463319 148503282791794491285694979)
          ·
            refine ⟨222754924187691736928542469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148503282791794491285694979 222754924187691736928542469)
            ·
              refine ⟨41766548285192200674101713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222754924187691736928542469 41766548285192200674101713)
              ·
                refine ⟨31324911213894150505576285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41766548285192200674101713 31324911213894150505576285)
                ·
                  refine ⟨11746841705210306439591107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31324911213894150505576285 11746841705210306439591107)
                  ·
                    refine ⟨17620262557815459659386661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11746841705210306439591107 17620262557815459659386661)
                    ·
                      refine ⟨3303799229590398686134999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17620262557815459659386661 3303799229590398686134999)
                      ·
                        rfl

theorem cell23_6434126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_6434126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434126 prefixEnd_6434126 := by exact prefixLift 6434126
  have htrace : WordTrace (prefixWord ++ tailWord_6434126) baseStart_6434126 baseEnd_6434126 := by
    simpa [prefixWord, tailWord_6434126, baseEnd_6434126] using wordTrace_append hprefix tailTrace_6434126
  have hstable : (prefixWord ++ tailWord_6434126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434126).length < 2 ^ (prefixWord ++ tailWord_6434126).sum := by decide
  have hdescent : baseEnd_6434126 < baseStart_6434126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434143 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 5, 2, 2]
def baseStart_6434143 : Nat := 118140960795 + 6434143 * 2 ^ 59
def prefixEnd_6434143 : Nat := 4983230072969 + 3 ^ 40 * 6434143 * 2
def baseEnd_6434143 : Nat := 3303807958761525119622421

theorem tailTrace_6434143 : CollatzResearch.WordTrace tailWord_6434143 prefixEnd_6434143 3303807958761525119622421 := by
  unfold tailWord_6434143
  simp only [CollatzResearch.WordTrace]
  refine ⟨234672474329206249984467083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156448316219470833322978055 234672474329206249984467083)
  ·
    refine ⟨352008711493809374976700625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234672474329206249984467083 352008711493809374976700625)
    ·
      refine ⟨264006533620357031232525469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352008711493809374976700625 264006533620357031232525469)
      ·
        refine ⟨99002450107633886712197051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264006533620357031232525469 99002450107633886712197051)
        ·
          refine ⟨148503675161450830068295577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99002450107633886712197051 148503675161450830068295577)
          ·
            refine ⟨111377756371088122551221683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148503675161450830068295577 111377756371088122551221683)
            ·
              refine ⟨167066634556632183826832525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111377756371088122551221683 167066634556632183826832525)
              ·
                refine ⟨62649987958737068935062197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167066634556632183826832525 62649987958737068935062197)
                ·
                  refine ⟨5873436371131600212662081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62649987958737068935062197 5873436371131600212662081)
                  ·
                    refine ⟨4405077278348700159496561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5873436371131600212662081 4405077278348700159496561)
                    ·
                      refine ⟨3303807958761525119622421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405077278348700159496561 3303807958761525119622421)
                      ·
                        rfl

theorem cell23_6434143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_6434143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434143 prefixEnd_6434143 := by exact prefixLift 6434143
  have htrace : WordTrace (prefixWord ++ tailWord_6434143) baseStart_6434143 baseEnd_6434143 := by
    simpa [prefixWord, tailWord_6434143, baseEnd_6434143] using wordTrace_append hprefix tailTrace_6434143
  have hstable : (prefixWord ++ tailWord_6434143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434143).length < 2 ^ (prefixWord ++ tailWord_6434143).sum := by decide
  have hdescent : baseEnd_6434143 < baseStart_6434143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434149 : List Nat := [1, 3, 1, 3, 1, 2, 1, 11]
def baseStart_6434149 : Nat := 118140960795 + 6434149 * 2 ^ 59
def prefixEnd_6434149 : Nat := 4983230072969 + 3 ^ 40 * 6434149 * 2
def baseEnd_6434149 : Nat := 122363371838720448005459

theorem tailTrace_6434149 : CollatzResearch.WordTrace tailWord_6434149 prefixEnd_6434149 122363371838720448005459 := by
  unfold tailWord_6434149
  simp only [CollatzResearch.WordTrace]
  refine ⟨234672693167184513009185501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156448462111456342006123667 234672693167184513009185501)
  ·
    refine ⟨88002259937694192378444563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234672693167184513009185501 88002259937694192378444563)
    ·
      refine ⟨132003389906541288567666845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88002259937694192378444563 132003389906541288567666845)
      ·
        refine ⟨49501271214952983212875067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132003389906541288567666845 49501271214952983212875067)
        ·
          refine ⟨74251906822429474819312601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49501271214952983212875067 74251906822429474819312601)
          ·
            refine ⟨55688930116822106114484451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74251906822429474819312601 55688930116822106114484451)
            ·
              refine ⟨83533395175233159171726677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55688930116822106114484451 83533395175233159171726677)
              ·
                refine ⟨122363371838720448005459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 83533395175233159171726677 122363371838720448005459)
                ·
                  rfl

theorem cell23_6434149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 11].length) (baseStart_6434149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434149 prefixEnd_6434149 := by exact prefixLift 6434149
  have htrace : WordTrace (prefixWord ++ tailWord_6434149) baseStart_6434149 baseEnd_6434149 := by
    simpa [prefixWord, tailWord_6434149, baseEnd_6434149] using wordTrace_append hprefix tailTrace_6434149
  have hstable : (prefixWord ++ tailWord_6434149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434149).length < 2 ^ (prefixWord ++ tailWord_6434149).sum := by decide
  have hdescent : baseEnd_6434149 < baseStart_6434149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434156 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_6434156 : Nat := 118140960795 + 6434156 * 2 ^ 59
def prefixEnd_6434156 : Nat := 4983230072969 + 3 ^ 40 * 6434156 * 2
def baseEnd_6434156 : Nat := 3303814634010033568759861

theorem tailTrace_6434156 : CollatzResearch.WordTrace tailWord_6434156 prefixEnd_6434156 3303814634010033568759861 := by
  unfold tailWord_6434156
  simp only [CollatzResearch.WordTrace]
  refine ⟨117336474239079576602345161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156448632318772768803126881 117336474239079576602345161)
  ·
    refine ⟨88002355679309682451758871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117336474239079576602345161 88002355679309682451758871)
    ·
      refine ⟨132003533518964523677638307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88002355679309682451758871 132003533518964523677638307)
      ·
        refine ⟨198005300278446785516457461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132003533518964523677638307 198005300278446785516457461)
        ·
          refine ⟨18562996901104386142167887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198005300278446785516457461 18562996901104386142167887)
          ·
            refine ⟨27844495351656579213251831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18562996901104386142167887 27844495351656579213251831)
            ·
              refine ⟨41766743027484868819877747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27844495351656579213251831 41766743027484868819877747)
              ·
                refine ⟨62650114541227303229816621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41766743027484868819877747 62650114541227303229816621)
                ·
                  refine ⟨23493792952960238711181233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62650114541227303229816621 23493792952960238711181233)
                  ·
                    refine ⟨17620344714720179033385925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23493792952960238711181233 17620344714720179033385925)
                    ·
                      refine ⟨3303814634010033568759861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17620344714720179033385925 3303814634010033568759861)
                      ·
                        rfl

theorem cell23_6434156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_6434156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434156 prefixEnd_6434156 := by exact prefixLift 6434156
  have htrace : WordTrace (prefixWord ++ tailWord_6434156) baseStart_6434156 baseEnd_6434156 := by
    simpa [prefixWord, tailWord_6434156, baseEnd_6434156] using wordTrace_append hprefix tailTrace_6434156
  have hstable : (prefixWord ++ tailWord_6434156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434156).length < 2 ^ (prefixWord ++ tailWord_6434156).sum := by decide
  have hdescent : baseEnd_6434156 < baseStart_6434156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434190 : List Nat := [4, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6434190 : Nat := 118140960795 + 6434190 * 2 ^ 59
def prefixEnd_6434190 : Nat := 4983230072969 + 3 ^ 40 * 6434190 * 2
def baseEnd_6434190 : Nat := 3303832092352286435734705

theorem tailTrace_6434190 : CollatzResearch.WordTrace tailWord_6434190 prefixEnd_6434190 3303832092352286435734705 := by
  unfold tailWord_6434190
  simp only [CollatzResearch.WordTrace]
  refine ⟨29334273570004497126428503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156449459040023984674285349 29334273570004497126428503)
  ·
    refine ⟨44001410355006745689642755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29334273570004497126428503 44001410355006745689642755)
    ·
      refine ⟨66002115532510118534464133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44001410355006745689642755 66002115532510118534464133)
      ·
        refine ⟨12375396662345647225212025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66002115532510118534464133 12375396662345647225212025)
        ·
          refine ⟨9281547496759235418909019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12375396662345647225212025 9281547496759235418909019)
          ·
            refine ⟨13922321245138853128363529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9281547496759235418909019 13922321245138853128363529)
            ·
              refine ⟨10441740933854139846272647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13922321245138853128363529 10441740933854139846272647)
              ·
                refine ⟨15662611400781209769408971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10441740933854139846272647 15662611400781209769408971)
                ·
                  refine ⟨23493917101171814654113457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15662611400781209769408971 23493917101171814654113457)
                  ·
                    refine ⟨17620437825878860990585093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23493917101171814654113457 17620437825878860990585093)
                    ·
                      refine ⟨3303832092352286435734705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17620437825878860990585093 3303832092352286435734705)
                      ·
                        rfl

theorem cell23_6434190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6434190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434190 prefixEnd_6434190 := by exact prefixLift 6434190
  have htrace : WordTrace (prefixWord ++ tailWord_6434190) baseStart_6434190 baseEnd_6434190 := by
    simpa [prefixWord, tailWord_6434190, baseEnd_6434190] using wordTrace_append hprefix tailTrace_6434190
  have hstable : (prefixWord ++ tailWord_6434190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434190).length < 2 ^ (prefixWord ++ tailWord_6434190).sum := by decide
  have hdescent : baseEnd_6434190 < baseStart_6434190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434194 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_6434194 : Nat := 118140960795 + 6434194 * 2 ^ 59
def prefixEnd_6434194 : Nat := 4983230072969 + 3 ^ 40 * 6434194 * 2
def baseEnd_6434194 : Nat := 3303834146274904420084687

theorem tailTrace_6434194 : CollatzResearch.WordTrace tailWord_6434194 prefixEnd_6434194 3303834146274904420084687 := by
  unfold tailWord_6434194
  simp only [CollatzResearch.WordTrace]
  refine ⟨58668583613005371423643409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156449556301347657129715757 58668583613005371423643409)
  ·
    refine ⟨44001437709754028567732557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58668583613005371423643409 44001437709754028567732557)
    ·
      refine ⟨16500539141157760712899709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44001437709754028567732557 16500539141157760712899709)
      ·
        refine ⟨6187702177934160267337391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16500539141157760712899709 6187702177934160267337391)
        ·
          refine ⟨9281553266901240401006087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6187702177934160267337391 9281553266901240401006087)
          ·
            refine ⟨13922329900351860601509131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9281553266901240401006087 13922329900351860601509131)
            ·
              refine ⟨20883494850527790902263697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13922329900351860601509131 20883494850527790902263697)
              ·
                refine ⟨15662621137895843176697773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20883494850527790902263697 15662621137895843176697773)
                ·
                  refine ⟨5873482926710941191261665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15662621137895843176697773 5873482926710941191261665)
                  ·
                    refine ⟨4405112195033205893446249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5873482926710941191261665 4405112195033205893446249)
                    ·
                      refine ⟨3303834146274904420084687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405112195033205893446249 3303834146274904420084687)
                      ·
                        rfl

theorem cell23_6434194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_6434194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434194 prefixEnd_6434194 := by exact prefixLift 6434194
  have htrace : WordTrace (prefixWord ++ tailWord_6434194) baseStart_6434194 baseEnd_6434194 := by
    simpa [prefixWord, tailWord_6434194, baseEnd_6434194] using wordTrace_append hprefix tailTrace_6434194
  have hstable : (prefixWord ++ tailWord_6434194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434194).length < 2 ^ (prefixWord ++ tailWord_6434194).sum := by decide
  have hdescent : baseEnd_6434194 < baseStart_6434194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434219 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 9]
def baseStart_6434219 : Nat := 118140960795 + 6434219 * 2 ^ 59
def prefixEnd_6434219 : Nat := 4983230072969 + 3 ^ 40 * 6434219 * 2
def baseEnd_6434219 : Nat := 3303846983291266822272071

theorem tailTrace_6434219 : CollatzResearch.WordTrace tailWord_6434219 prefixEnd_6434219 3303846983291266822272071 := by
  unfold tailWord_6434219
  simp only [CollatzResearch.WordTrace]
  refine ⟨234675246276930914964233711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156450164184620609976155807 234675246276930914964233711)
  ·
    refine ⟨352012869415396372446350567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234675246276930914964233711 352012869415396372446350567)
    ·
      refine ⟨528019304123094558669525851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352012869415396372446350567 528019304123094558669525851)
      ·
        refine ⟨792028956184641838004288777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528019304123094558669525851 792028956184641838004288777)
        ·
          refine ⟨594021717138481378503216583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792028956184641838004288777 594021717138481378503216583)
          ·
            refine ⟨891032575707722067754824875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594021717138481378503216583 891032575707722067754824875)
            ·
              refine ⟨1336548863561583101632237313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891032575707722067754824875 1336548863561583101632237313)
              ·
                refine ⟨1002411647671187326224177985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1336548863561583101632237313 1002411647671187326224177985)
                ·
                  refine ⟨751808735753390494668133489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1002411647671187326224177985 751808735753390494668133489)
                  ·
                    refine ⟨563856551815042871001100117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 751808735753390494668133489 563856551815042871001100117)
                    ·
                      refine ⟨3303846983291266822272071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 563856551815042871001100117 3303846983291266822272071)
                      ·
                        rfl

theorem cell23_6434219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_6434219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434219 prefixEnd_6434219 := by exact prefixLift 6434219
  have htrace : WordTrace (prefixWord ++ tailWord_6434219) baseStart_6434219 baseEnd_6434219 := by
    simpa [prefixWord, tailWord_6434219, baseEnd_6434219] using wordTrace_append hprefix tailTrace_6434219
  have hstable : (prefixWord ++ tailWord_6434219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434219).length < 2 ^ (prefixWord ++ tailWord_6434219).sum := by decide
  have hdescent : baseEnd_6434219 < baseStart_6434219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434244 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_6434244 : Nat := 118140960795 + 6434244 * 2 ^ 59
def prefixEnd_6434244 : Nat := 4983230072969 + 3 ^ 40 * 6434244 * 2
def baseEnd_6434244 : Nat := 3303859820307629224459457

theorem tailTrace_6434244 : CollatzResearch.WordTrace tailWord_6434244 prefixEnd_6434244 3303859820307629224459457 := by
  unfold tailWord_6434244
  simp only [CollatzResearch.WordTrace]
  refine ⟨117338079050920172116946893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156450772067893562822595857 117338079050920172116946893)
  ·
    refine ⟨44001779644095064543855085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117338079050920172116946893 44001779644095064543855085)
    ·
      refine ⟨16500667366535649203945657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44001779644095064543855085 16500667366535649203945657)
      ·
        refine ⟨12375500524901736902959243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16500667366535649203945657 12375500524901736902959243)
        ·
          refine ⟨18563250787352605354438865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12375500524901736902959243 18563250787352605354438865)
          ·
            refine ⟨13922438090514454015829149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18563250787352605354438865 13922438090514454015829149)
            ·
              refine ⟨5220914283942920255935931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13922438090514454015829149 5220914283942920255935931)
              ·
                refine ⟨7831371425914380383903897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5220914283942920255935931 7831371425914380383903897)
                ·
                  refine ⟨5873528569435785287927923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7831371425914380383903897 5873528569435785287927923)
                  ·
                    refine ⟨8810292854153677931891885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5873528569435785287927923 8810292854153677931891885)
                    ·
                      refine ⟨3303859820307629224459457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8810292854153677931891885 3303859820307629224459457)
                      ·
                        rfl

theorem cell23_6434244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_6434244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434244 prefixEnd_6434244 := by exact prefixLift 6434244
  have htrace : WordTrace (prefixWord ++ tailWord_6434244) baseStart_6434244 baseEnd_6434244 := by
    simpa [prefixWord, tailWord_6434244, baseEnd_6434244] using wordTrace_append hprefix tailTrace_6434244
  have hstable : (prefixWord ++ tailWord_6434244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434244).length < 2 ^ (prefixWord ++ tailWord_6434244).sum := by decide
  have hdescent : baseEnd_6434244 < baseStart_6434244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434250 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2]
def baseStart_6434250 : Nat := 118140960795 + 6434250 * 2 ^ 59
def prefixEnd_6434250 : Nat := 4983230072969 + 3 ^ 40 * 6434250 * 2
def baseEnd_6434250 : Nat := 3303862901191556200984429

theorem tailTrace_6434250 : CollatzResearch.WordTrace tailWord_6434250 prefixEnd_6434250 3303862901191556200984429 := by
  unfold tailWord_6434250
  simp only [CollatzResearch.WordTrace]
  refine ⟨58669094234954651814653051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156450917959879071505741469 58669094234954651814653051)
  ·
    refine ⟨88003641352431977721979577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58669094234954651814653051 88003641352431977721979577)
    ·
      refine ⟨66002731014323983291484683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88003641352431977721979577 66002731014323983291484683)
      ·
        refine ⟨99004096521485974937227025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66002731014323983291484683 99004096521485974937227025)
        ·
          refine ⟨74253072391114481202920269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99004096521485974937227025 74253072391114481202920269)
          ·
            refine ⟨27844902146667930451095101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74253072391114481202920269 27844902146667930451095101)
            ·
              refine ⟨10441838305000473919160663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27844902146667930451095101 10441838305000473919160663)
              ·
                refine ⟨15662757457500710878740995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10441838305000473919160663 15662757457500710878740995)
                ·
                  refine ⟨23494136186251066318111493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15662757457500710878740995 23494136186251066318111493)
                  ·
                    refine ⟨4405150534922074934645905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23494136186251066318111493 4405150534922074934645905)
                    ·
                      refine ⟨3303862901191556200984429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405150534922074934645905 3303862901191556200984429)
                      ·
                        rfl

theorem cell23_6434250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_6434250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434250 prefixEnd_6434250 := by exact prefixLift 6434250
  have htrace : WordTrace (prefixWord ++ tailWord_6434250) baseStart_6434250 baseEnd_6434250 := by
    simpa [prefixWord, tailWord_6434250, baseEnd_6434250] using wordTrace_append hprefix tailTrace_6434250
  have hstable : (prefixWord ++ tailWord_6434250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434250).length < 2 ^ (prefixWord ++ tailWord_6434250).sum := by decide
  have hdescent : baseEnd_6434250 < baseStart_6434250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434290 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 7]
def baseStart_6434290 : Nat := 118140960795 + 6434290 * 2 ^ 59
def prefixEnd_6434290 : Nat := 4983230072969 + 3 ^ 40 * 6434290 * 2
def baseEnd_6434290 : Nat := 367098160046415116053805

theorem tailTrace_6434290 : CollatzResearch.WordTrace tailWord_6434290 prefixEnd_6434290 367098160046415116053805 := by
  unfold tailWord_6434290
  simp only [CollatzResearch.WordTrace]
  refine ⟨58669458964918423522517081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156451890573115796060045549 58669458964918423522517081)
  ·
    refine ⟨44002094223688817641887811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58669458964918423522517081 44002094223688817641887811)
    ·
      refine ⟨66003141335533226462831717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44002094223688817641887811 66003141335533226462831717)
      ·
        refine ⟨12375589000412479961780947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66003141335533226462831717 12375589000412479961780947)
        ·
          refine ⟨18563383500618719942671421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12375589000412479961780947 18563383500618719942671421)
          ·
            refine ⟨6961268812732019978501783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18563383500618719942671421 6961268812732019978501783)
            ·
              refine ⟨10441903219098029967752675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6961268812732019978501783 10441903219098029967752675)
              ·
                refine ⟨15662854828647044951629013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10441903219098029967752675 15662854828647044951629013)
                ·
                  refine ⟨367098160046415116053805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15662854828647044951629013 367098160046415116053805)
                  ·
                    rfl

theorem cell23_6434290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_6434290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434290 prefixEnd_6434290 := by exact prefixLift 6434290
  have htrace : WordTrace (prefixWord ++ tailWord_6434290) baseStart_6434290 baseEnd_6434290 := by
    simpa [prefixWord, tailWord_6434290, baseEnd_6434290] using wordTrace_append hprefix tailTrace_6434290
  have hstable : (prefixWord ++ tailWord_6434290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434290).length < 2 ^ (prefixWord ++ tailWord_6434290).sum := by decide
  have hdescent : baseEnd_6434290 < baseStart_6434290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434296 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_6434296 : Nat := 118140960795 + 6434296 * 2 ^ 59
def prefixEnd_6434296 : Nat := 4983230072969 + 3 ^ 40 * 6434296 * 2
def baseEnd_6434296 : Nat := 3303886521301663021009217

theorem tailTrace_6434296 : CollatzResearch.WordTrace tailWord_6434296 prefixEnd_6434296 3303886521301663021009217 := by
  unfold tailWord_6434296
  simp only [CollatzResearch.WordTrace]
  refine ⟨117339027348825978557393371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156452036465101304743191161 117339027348825978557393371)
  ·
    refine ⟨176008541023238967836090057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117339027348825978557393371 176008541023238967836090057)
    ·
      refine ⟨132006405767429225877067543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176008541023238967836090057 132006405767429225877067543)
      ·
        refine ⟨198009608651143838815601315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132006405767429225877067543 198009608651143838815601315)
        ·
          refine ⟨297014412976715758223401973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198009608651143838815601315 297014412976715758223401973)
          ·
            refine ⟨27845101216567102333443935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 297014412976715758223401973 27845101216567102333443935)
            ·
              refine ⟨41767651824850653500165903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27845101216567102333443935 41767651824850653500165903)
              ·
                refine ⟨62651477737275980250248855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41767651824850653500165903 62651477737275980250248855)
                ·
                  refine ⟨93977216605913970375373283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62651477737275980250248855 93977216605913970375373283)
                  ·
                    refine ⟨140965824908870955563059925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93977216605913970375373283 140965824908870955563059925)
                    ·
                      refine ⟨3303886521301663021009217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140965824908870955563059925 3303886521301663021009217)
                      ·
                        rfl

theorem cell23_6434296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_6434296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434296 prefixEnd_6434296 := by exact prefixLift 6434296
  have htrace : WordTrace (prefixWord ++ tailWord_6434296) baseStart_6434296 baseEnd_6434296 := by
    simpa [prefixWord, tailWord_6434296, baseEnd_6434296] using wordTrace_append hprefix tailTrace_6434296
  have hstable : (prefixWord ++ tailWord_6434296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434296).length < 2 ^ (prefixWord ++ tailWord_6434296).sum := by decide
  have hdescent : baseEnd_6434296 < baseStart_6434296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434323 : List Nat := [1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 4]
def baseStart_6434323 : Nat := 118140960795 + 6434323 * 2 ^ 59
def prefixEnd_6434323 : Nat := 4983230072969 + 3 ^ 40 * 6434323 * 2
def baseEnd_6434323 : Nat := 3303900385279334415371593

theorem tailTrace_6434323 : CollatzResearch.WordTrace tailWord_6434323 prefixEnd_6434323 3303900385279334415371593 := by
  unfold tailWord_6434323
  simp only [CollatzResearch.WordTrace]
  refine ⟨234679039468554140726019623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156452692979036093817346415 234679039468554140726019623)
  ·
    refine ⟨352018559202831211089029435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234679039468554140726019623 352018559202831211089029435)
    ·
      refine ⟨528027838804246816633544153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352018559202831211089029435 528027838804246816633544153)
      ·
        refine ⟨396020879103185112475158115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528027838804246816633544153 396020879103185112475158115)
        ·
          refine ⟨594031318654777668712737173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396020879103185112475158115 594031318654777668712737173)
          ·
            refine ⟨27845218061942703220909555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 594031318654777668712737173 27845218061942703220909555)
            ·
              refine ⟨41767827092914054831364333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27845218061942703220909555 41767827092914054831364333)
              ·
                refine ⟨15662935159842770561761625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41767827092914054831364333 15662935159842770561761625)
                ·
                  refine ⟨11747201369882077921321219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15662935159842770561761625 11747201369882077921321219)
                  ·
                    refine ⟨17620802054823116881981829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11747201369882077921321219 17620802054823116881981829)
                    ·
                      refine ⟨3303900385279334415371593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17620802054823116881981829 3303900385279334415371593)
                      ·
                        rfl

theorem cell23_6434323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_6434323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434323 prefixEnd_6434323 := by exact prefixLift 6434323
  have htrace : WordTrace (prefixWord ++ tailWord_6434323) baseStart_6434323 baseEnd_6434323 := by
    simpa [prefixWord, tailWord_6434323, baseEnd_6434323] using wordTrace_append hprefix tailTrace_6434323
  have hstable : (prefixWord ++ tailWord_6434323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434323).length < 2 ^ (prefixWord ++ tailWord_6434323).sum := by decide
  have hdescent : baseEnd_6434323 < baseStart_6434323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434397 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 8]
def baseStart_6434397 : Nat := 118140960795 + 6434397 * 2 ^ 59
def prefixEnd_6434397 : Nat := 4983230072969 + 3 ^ 40 * 6434397 * 2
def baseEnd_6434397 : Nat := 367104264760863013982917

theorem tailTrace_6434397 : CollatzResearch.WordTrace tailWord_6434397 prefixEnd_6434397 367104264760863013982917 := by
  unfold tailWord_6434397
  simp only [CollatzResearch.WordTrace]
  refine ⟨234681738470286051364213445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156454492313524034242808963 234681738470286051364213445)
  ·
    refine ⟨44002825963178634630790021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234681738470286051364213445 44002825963178634630790021)
    ·
      refine ⟨8250529868095993993273129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44002825963178634630790021 8250529868095993993273129)
      ·
        refine ⟨6187897401071995494954847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8250529868095993993273129 6187897401071995494954847)
        ·
          refine ⟨9281846101607993242432271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6187897401071995494954847 9281846101607993242432271)
          ·
            refine ⟨13922769152411989863648407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9281846101607993242432271 13922769152411989863648407)
            ·
              refine ⟨20884153728617984795472611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13922769152411989863648407 20884153728617984795472611)
              ·
                refine ⟨31326230592926977193208917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20884153728617984795472611 31326230592926977193208917)
                ·
                  refine ⟨367104264760863013982917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31326230592926977193208917 367104264760863013982917)
                  ·
                    rfl

theorem cell23_6434397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_6434397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434397 prefixEnd_6434397 := by exact prefixLift 6434397
  have htrace : WordTrace (prefixWord ++ tailWord_6434397) baseStart_6434397 baseEnd_6434397 := by
    simpa [prefixWord, tailWord_6434397, baseEnd_6434397] using wordTrace_append hprefix tailTrace_6434397
  have hstable : (prefixWord ++ tailWord_6434397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434397).length < 2 ^ (prefixWord ++ tailWord_6434397).sum := by decide
  have hdescent : baseEnd_6434397 < baseStart_6434397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434400 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 4, 3, 2]
def baseStart_6434400 : Nat := 118140960795 + 6434400 * 2 ^ 59
def prefixEnd_6434400 : Nat := 4983230072969 + 3 ^ 40 * 6434400 * 2
def baseEnd_6434400 : Nat := 3303939923289730614108739

theorem tailTrace_6434400 : CollatzResearch.WordTrace tailWord_6434400 prefixEnd_6434400 3303939923289730614108739 := by
  unfold tailWord_6434400
  simp only [CollatzResearch.WordTrace]
  refine ⟨117340923944637591438286327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156454565259516788584381769 117340923944637591438286327)
  ·
    refine ⟨176011385916956387157429491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117340923944637591438286327 176011385916956387157429491)
    ·
      refine ⟨264017078875434580736144237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176011385916956387157429491 264017078875434580736144237)
      ·
        refine ⟨99006404578287967776054089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264017078875434580736144237 99006404578287967776054089)
        ·
          refine ⟨74254803433715975832040567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99006404578287967776054089 74254803433715975832040567)
          ·
            refine ⟨111382205150573963748060851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74254803433715975832040567 111382205150573963748060851)
            ·
              refine ⟨167073307725860945622091277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111382205150573963748060851 167073307725860945622091277)
              ·
                refine ⟨62652490397197854608284229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167073307725860945622091277 62652490397197854608284229)
                ·
                  refine ⟨11747341949474597739053293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62652490397197854608284229 11747341949474597739053293)
                  ·
                    refine ⟨4405253231052974152144985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11747341949474597739053293 4405253231052974152144985)
                    ·
                      refine ⟨3303939923289730614108739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405253231052974152144985 3303939923289730614108739)
                      ·
                        rfl

theorem cell23_6434400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_6434400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434400 prefixEnd_6434400 := by exact prefixLift 6434400
  have htrace : WordTrace (prefixWord ++ tailWord_6434400) baseStart_6434400 baseEnd_6434400 := by
    simpa [prefixWord, tailWord_6434400, baseEnd_6434400] using wordTrace_append hprefix tailTrace_6434400
  have hstable : (prefixWord ++ tailWord_6434400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434400).length < 2 ^ (prefixWord ++ tailWord_6434400).sum := by decide
  have hdescent : baseEnd_6434400 < baseStart_6434400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434443 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 4]
def baseStart_6434443 : Nat := 118140960795 + 6434443 * 2 ^ 59
def prefixEnd_6434443 : Nat := 4983230072969 + 3 ^ 40 * 6434443 * 2
def baseEnd_6434443 : Nat := 3303962002957873945871041

theorem tailTrace_6434443 : CollatzResearch.WordTrace tailWord_6434443 prefixEnd_6434443 3303962002957873945871041 := by
  unfold tailWord_6434443
  simp only [CollatzResearch.WordTrace]
  refine ⟨234683416228119401220387983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156455610818746267480258655 234683416228119401220387983)
  ·
    refine ⟨352025124342179101830581975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234683416228119401220387983 352025124342179101830581975)
    ·
      refine ⟨528037686513268652745872963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352025124342179101830581975 528037686513268652745872963)
      ·
        refine ⟨792056529769902979118809445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528037686513268652745872963 792056529769902979118809445)
        ·
          refine ⟨148510599331856808584776771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 792056529769902979118809445 148510599331856808584776771)
          ·
            refine ⟨222765898997785212877165157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148510599331856808584776771 222765898997785212877165157)
            ·
              refine ⟨41768606062084727414468467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222765898997785212877165157 41768606062084727414468467)
              ·
                refine ⟨62652909093127091121702701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41768606062084727414468467 62652909093127091121702701)
                ·
                  refine ⟨23494840909922659170638513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62652909093127091121702701 23494840909922659170638513)
                  ·
                    refine ⟨17621130682441994377978885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23494840909922659170638513 17621130682441994377978885)
                    ·
                      refine ⟨3303962002957873945871041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17621130682441994377978885 3303962002957873945871041)
                      ·
                        rfl

theorem cell23_6434443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 4].length) (baseStart_6434443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434443 prefixEnd_6434443 := by exact prefixLift 6434443
  have htrace : WordTrace (prefixWord ++ tailWord_6434443) baseStart_6434443 baseEnd_6434443 := by
    simpa [prefixWord, tailWord_6434443, baseEnd_6434443] using wordTrace_append hprefix tailTrace_6434443
  have hstable : (prefixWord ++ tailWord_6434443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434443).length < 2 ^ (prefixWord ++ tailWord_6434443).sum := by decide
  have hdescent : baseEnd_6434443 < baseStart_6434443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434464 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 3, 2, 2]
def baseStart_6434464 : Nat := 118140960795 + 6434464 * 2 ^ 59
def prefixEnd_6434464 : Nat := 4983230072969 + 3 ^ 40 * 6434464 * 2
def baseEnd_6434464 : Nat := 3303972786051618363708445

theorem tailTrace_6434464 : CollatzResearch.WordTrace tailWord_6434464 prefixEnd_6434464 3303972786051618363708445 := by
  unfold tailWord_6434464
  simp only [CollatzResearch.WordTrace]
  refine ⟨117342091080521660903451223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156456121440695547871268297 117342091080521660903451223)
  ·
    refine ⟨176013136620782491355176835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117342091080521660903451223 176013136620782491355176835)
    ·
      refine ⟨264019704931173737032765253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176013136620782491355176835 264019704931173737032765253)
      ·
        refine ⟨49503694674595075693643485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264019704931173737032765253 49503694674595075693643485)
        ·
          refine ⟨18563885502973153385116307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49503694674595075693643485 18563885502973153385116307)
          ·
            refine ⟨27845828254459730077674461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18563885502973153385116307 27845828254459730077674461)
            ·
              refine ⟨10442185595422398779127923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27845828254459730077674461 10442185595422398779127923)
              ·
                refine ⟨15663278393133598168691885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10442185595422398779127923 15663278393133598168691885)
                ·
                  refine ⟨5873729397425099313259457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15663278393133598168691885 5873729397425099313259457)
                  ·
                    refine ⟨4405297048068824484944593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5873729397425099313259457 4405297048068824484944593)
                    ·
                      refine ⟨3303972786051618363708445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405297048068824484944593 3303972786051618363708445)
                      ·
                        rfl

theorem cell23_6434464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_6434464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434464 prefixEnd_6434464 := by exact prefixLift 6434464
  have htrace : WordTrace (prefixWord ++ tailWord_6434464) baseStart_6434464 baseEnd_6434464 := by
    simpa [prefixWord, tailWord_6434464, baseEnd_6434464] using wordTrace_append hprefix tailTrace_6434464
  have hstable : (prefixWord ++ tailWord_6434464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434464).length < 2 ^ (prefixWord ++ tailWord_6434464).sum := by decide
  have hdescent : baseEnd_6434464 < baseStart_6434464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434507 : List Nat := [1, 1, 1, 1, 3, 2, 1, 7, 1, 3, 2]
def baseStart_6434507 : Nat := 118140960795 + 6434507 * 2 ^ 59
def prefixEnd_6434507 : Nat := 4983230072969 + 3 ^ 40 * 6434507 * 2
def baseEnd_6434507 : Nat := 3303994865719761695470747

theorem tailTrace_6434507 : CollatzResearch.WordTrace tailWord_6434507 prefixEnd_6434507 3303994865719761695470747 := by
  unfold tailWord_6434507
  simp only [CollatzResearch.WordTrace]
  refine ⟨234685750499887540150717775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156457166999925026767145183 234685750499887540150717775)
  ·
    refine ⟨352028625749831310226076663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234685750499887540150717775 352028625749831310226076663)
    ·
      refine ⟨528042938624746965339114995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352028625749831310226076663 528042938624746965339114995)
      ·
        refine ⟨792064407937120448008672493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528042938624746965339114995 792064407937120448008672493)
        ·
          refine ⟨297024152976420168003252185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 792064407937120448008672493 297024152976420168003252185)
          ·
            refine ⟨222768114732315126002439139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297024152976420168003252185 222768114732315126002439139)
            ·
              refine ⟨334152172098472689003658709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222768114732315126002439139 334152172098472689003658709)
              ·
                refine ⟨7831691533557953648523251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 334152172098472689003658709 7831691533557953648523251)
                ·
                  refine ⟨11747537300336930472784877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7831691533557953648523251 11747537300336930472784877)
                  ·
                    refine ⟨4405326487626348927294329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11747537300336930472784877 4405326487626348927294329)
                    ·
                      refine ⟨3303994865719761695470747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405326487626348927294329 3303994865719761695470747)
                      ·
                        rfl

theorem cell23_6434507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 3, 2].length) (baseStart_6434507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434507 prefixEnd_6434507 := by exact prefixLift 6434507
  have htrace : WordTrace (prefixWord ++ tailWord_6434507) baseStart_6434507 baseEnd_6434507 := by
    simpa [prefixWord, tailWord_6434507, baseEnd_6434507] using wordTrace_append hprefix tailTrace_6434507
  have hstable : (prefixWord ++ tailWord_6434507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434507).length < 2 ^ (prefixWord ++ tailWord_6434507).sum := by decide
  have hdescent : baseEnd_6434507 < baseStart_6434507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434514 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_6434514 : Nat := 118140960795 + 6434514 * 2 ^ 59
def prefixEnd_6434514 : Nat := 4983230072969 + 3 ^ 40 * 6434514 * 2
def baseEnd_6434514 : Nat := 3303998460084343168083215

theorem tailTrace_6434514 : CollatzResearch.WordTrace tailWord_6434514 prefixEnd_6434514 3303998460084343168083215 := by
  unfold tailWord_6434514
  simp only [CollatzResearch.WordTrace]
  refine ⟨58671501452715545086555649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156457337207241453564148397 58671501452715545086555649)
  ·
    refine ⟨44003626089536658814916737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58671501452715545086555649 44003626089536658814916737)
    ·
      refine ⟨33002719567152494111187553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44003626089536658814916737 33002719567152494111187553)
      ·
        refine ⟨24752039675364370583390665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33002719567152494111187553 24752039675364370583390665)
        ·
          refine ⟨18564029756523277937542999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24752039675364370583390665 18564029756523277937542999)
          ·
            refine ⟨27846044634784916906314499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18564029756523277937542999 27846044634784916906314499)
            ·
              refine ⟨41769066952177375359471749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27846044634784916906314499 41769066952177375359471749)
              ·
                refine ⟨7831700053533257879900953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41769066952177375359471749 7831700053533257879900953)
                ·
                  refine ⟨5873775040149943409925715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7831700053533257879900953 5873775040149943409925715)
                  ·
                    refine ⟨8810662560224915114888573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5873775040149943409925715 8810662560224915114888573)
                    ·
                      refine ⟨3303998460084343168083215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8810662560224915114888573 3303998460084343168083215)
                      ·
                        rfl

theorem cell23_6434514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_6434514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434514 prefixEnd_6434514 := by exact prefixLift 6434514
  have htrace : WordTrace (prefixWord ++ tailWord_6434514) baseStart_6434514 baseEnd_6434514 := by
    simpa [prefixWord, tailWord_6434514, baseEnd_6434514] using wordTrace_append hprefix tailTrace_6434514
  have hstable : (prefixWord ++ tailWord_6434514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434514).length < 2 ^ (prefixWord ++ tailWord_6434514).sum := by decide
  have hdescent : baseEnd_6434514 < baseStart_6434514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434537 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 6, 2, 2]
def baseStart_6434537 : Nat := 118140960795 + 6434537 * 2 ^ 59
def prefixEnd_6434537 : Nat := 4983230072969 + 3 ^ 40 * 6434537 * 2
def baseEnd_6434537 : Nat := 3304010270139396578095609

theorem tailTrace_6434537 : CollatzResearch.WordTrace tailWord_6434537 prefixEnd_6434537 3304010270139396578095609 := by
  unfold tailWord_6434537
  simp only [CollatzResearch.WordTrace]
  refine ⟨234686844689778855274309865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156457896459852570182873243 234686844689778855274309865)
  ·
    refine ⟨176015133517334141455732399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234686844689778855274309865 176015133517334141455732399)
    ·
      refine ⟨264022700276001212183598599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176015133517334141455732399 264022700276001212183598599)
      ·
        refine ⟨396034050414001818275397899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264022700276001212183598599 396034050414001818275397899)
        ·
          refine ⟨594051075621002727413096849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396034050414001818275397899 594051075621002727413096849)
          ·
            refine ⟨445538306715752045559822637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594051075621002727413096849 445538306715752045559822637)
            ·
              refine ⟨167076865018407017084933489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445538306715752045559822637 167076865018407017084933489)
              ·
                refine ⟨125307648763805262813700117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167076865018407017084933489 125307648763805262813700117)
                ·
                  refine ⟨5873796035803371694392193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125307648763805262813700117 5873796035803371694392193)
                  ·
                    refine ⟨4405347026852528770794145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5873796035803371694392193 4405347026852528770794145)
                    ·
                      refine ⟨3304010270139396578095609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405347026852528770794145 3304010270139396578095609)
                      ·
                        rfl

theorem cell23_6434537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 2, 2].length) (baseStart_6434537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434537 prefixEnd_6434537 := by exact prefixLift 6434537
  have htrace : WordTrace (prefixWord ++ tailWord_6434537) baseStart_6434537 baseEnd_6434537 := by
    simpa [prefixWord, tailWord_6434537, baseEnd_6434537] using wordTrace_append hprefix tailTrace_6434537
  have hstable : (prefixWord ++ tailWord_6434537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434537).length < 2 ^ (prefixWord ++ tailWord_6434537).sum := by decide
  have hdescent : baseEnd_6434537 < baseStart_6434537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434553 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_6434553 : Nat := 118140960795 + 6434553 * 2 ^ 59
def prefixEnd_6434553 : Nat := 4983230072969 + 3 ^ 40 * 6434553 * 2
def baseEnd_6434553 : Nat := 3304018485829868515495535

theorem tailTrace_6434553 : CollatzResearch.WordTrace tailWord_6434553 prefixEnd_6434553 3304018485829868515495535 := by
  unfold tailWord_6434553
  simp only [CollatzResearch.WordTrace]
  refine ⟨234687428257720890006892313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156458285505147260004594875 234687428257720890006892313)
  ·
    refine ⟨176015571193290667505169235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234687428257720890006892313 176015571193290667505169235)
    ·
      refine ⟨264023356789936001257753853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176015571193290667505169235 264023356789936001257753853)
      ·
        refine ⟨99008758796226000471657695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264023356789936001257753853 99008758796226000471657695)
        ·
          refine ⟨148513138194339000707486543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99008758796226000471657695 148513138194339000707486543)
          ·
            refine ⟨222769707291508501061229815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148513138194339000707486543 222769707291508501061229815)
            ·
              refine ⟨334154560937262751591844723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222769707291508501061229815 334154560937262751591844723)
              ·
                refine ⟨501231841405894127387767085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 334154560937262751591844723 501231841405894127387767085)
                ·
                  refine ⟨187961940527210297770412657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 501231841405894127387767085 187961940527210297770412657)
                  ·
                    refine ⟨140971455395407723327809493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187961940527210297770412657 140971455395407723327809493)
                    ·
                      refine ⟨3304018485829868515495535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140971455395407723327809493 3304018485829868515495535)
                      ·
                        rfl

theorem cell23_6434553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_6434553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434553 prefixEnd_6434553 := by exact prefixLift 6434553
  have htrace : WordTrace (prefixWord ++ tailWord_6434553) baseStart_6434553 baseEnd_6434553 := by
    simpa [prefixWord, tailWord_6434553, baseEnd_6434553] using wordTrace_append hprefix tailTrace_6434553
  have hstable : (prefixWord ++ tailWord_6434553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434553).length < 2 ^ (prefixWord ++ tailWord_6434553).sum := by decide
  have hdescent : baseEnd_6434553 < baseStart_6434553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434611 : List Nat := [1, 1, 1, 2, 8, 1, 1, 3, 5]
def baseStart_6434611 : Nat := 118140960795 + 6434611 * 2 ^ 59
def prefixEnd_6434611 : Nat := 4983230072969 + 3 ^ 40 * 6434611 * 2
def baseEnd_6434611 : Nat := 367116474189758809841141

theorem tailTrace_6434611 : CollatzResearch.WordTrace tailWord_6434611 prefixEnd_6434611 367116474189758809841141 := by
  unfold tailWord_6434611
  simp only [CollatzResearch.WordTrace]
  refine ⟨234689543691510765912503687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156459695794340510608335791 234689543691510765912503687)
  ·
    refine ⟨352034315537266148868755531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234689543691510765912503687 352034315537266148868755531)
    ·
      refine ⟨528051473305899223303133297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352034315537266148868755531 528051473305899223303133297)
      ·
        refine ⟨396038604979424417477349973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 528051473305899223303133297 396038604979424417477349973)
        ·
          refine ⟨4641077402102629892312695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 396038604979424417477349973 4641077402102629892312695)
          ·
            refine ⟨6961616103153944838469043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4641077402102629892312695 6961616103153944838469043)
            ·
              refine ⟨10442424154730917257703565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6961616103153944838469043 10442424154730917257703565)
              ·
                refine ⟨3915909058024093971638837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10442424154730917257703565 3915909058024093971638837)
                ·
                  refine ⟨367116474189758809841141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3915909058024093971638837 367116474189758809841141)
                  ·
                    rfl

theorem cell23_6434611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 5].length) (baseStart_6434611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434611 prefixEnd_6434611 := by exact prefixLift 6434611
  have htrace : WordTrace (prefixWord ++ tailWord_6434611) baseStart_6434611 baseEnd_6434611 := by
    simpa [prefixWord, tailWord_6434611, baseEnd_6434611] using wordTrace_append hprefix tailTrace_6434611
  have hstable : (prefixWord ++ tailWord_6434611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434611).length < 2 ^ (prefixWord ++ tailWord_6434611).sum := by decide
  have hdescent : baseEnd_6434611 < baseStart_6434611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434627 : List Nat := [1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 4]
def baseStart_6434627 : Nat := 118140960795 + 6434627 * 2 ^ 59
def prefixEnd_6434627 : Nat := 4983230072969 + 3 ^ 40 * 6434627 * 2
def baseEnd_6434627 : Nat := 3304056483398301225970195

theorem tailTrace_6434627 : CollatzResearch.WordTrace tailWord_6434627 prefixEnd_6434627 3304056483398301225970195 := by
  unfold tailWord_6434627
  simp only [CollatzResearch.WordTrace]
  refine ⟨234690127259452800645086135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156460084839635200430057423 234690127259452800645086135)
  ·
    refine ⟨352035190889179200967629203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234690127259452800645086135 352035190889179200967629203)
    ·
      refine ⟨528052786333768801451443805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352035190889179200967629203 528052786333768801451443805)
      ·
        refine ⟨198019794875163300544291427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 528052786333768801451443805 198019794875163300544291427)
        ·
          refine ⟨297029692312744950816437141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198019794875163300544291427 297029692312744950816437141)
          ·
            refine ⟨13923266827159919569520491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 297029692312744950816437141 13923266827159919569520491)
            ·
              refine ⟨20884900240739879354280737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13923266827159919569520491 20884900240739879354280737)
              ·
                refine ⟨15663675180554909515710553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20884900240739879354280737 15663675180554909515710553)
                ·
                  refine ⟨11747756385416182136782915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15663675180554909515710553 11747756385416182136782915)
                  ·
                    refine ⟨17621634578124273205174373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11747756385416182136782915 17621634578124273205174373)
                    ·
                      refine ⟨3304056483398301225970195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17621634578124273205174373 3304056483398301225970195)
                      ·
                        rfl

theorem cell23_6434627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_6434627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434627 prefixEnd_6434627 := by exact prefixLift 6434627
  have htrace : WordTrace (prefixWord ++ tailWord_6434627) baseStart_6434627 baseEnd_6434627 := by
    simpa [prefixWord, tailWord_6434627, baseEnd_6434627] using wordTrace_append hprefix tailTrace_6434627
  have hstable : (prefixWord ++ tailWord_6434627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434627).length < 2 ^ (prefixWord ++ tailWord_6434627).sum := by decide
  have hdescent : baseEnd_6434627 < baseStart_6434627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434664 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_6434664 : Nat := 118140960795 + 6434664 * 2 ^ 59
def prefixEnd_6434664 : Nat := 4983230072969 + 3 ^ 40 * 6434664 * 2
def baseEnd_6434664 : Nat := 3304075482182517581207525

theorem tailTrace_6434664 : CollatzResearch.WordTrace tailWord_6434664 prefixEnd_6434664 3304075482182517581207525 := by
  unfold tailWord_6434664
  simp only [CollatzResearch.WordTrace]
  refine ⟨117345738380159377982091523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156460984506879170642788697 117345738380159377982091523)
  ·
    refine ⟨176018607570239066973137285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117345738380159377982091523 176018607570239066973137285)
    ·
      refine ⟨33003488919419825057463241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176018607570239066973137285 33003488919419825057463241)
      ·
        refine ⟨24752616689564868793097431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33003488919419825057463241 24752616689564868793097431)
        ·
          refine ⟨37128925034347303189646147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24752616689564868793097431 37128925034347303189646147)
          ·
            refine ⟨55693387551520954784469221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37128925034347303189646147 55693387551520954784469221)
            ·
              refine ⟨10442510165910179022087979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55693387551520954784469221 10442510165910179022087979)
              ·
                refine ⟨15663765248865268533131969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10442510165910179022087979 15663765248865268533131969)
                ·
                  refine ⟨11747823936648951399848977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15663765248865268533131969 11747823936648951399848977)
                  ·
                    refine ⟨8810867952486713549886733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11747823936648951399848977 8810867952486713549886733)
                    ·
                      refine ⟨3304075482182517581207525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8810867952486713549886733 3304075482182517581207525)
                      ·
                        rfl

theorem cell23_6434664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_6434664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434664 prefixEnd_6434664 := by exact prefixLift 6434664
  have htrace : WordTrace (prefixWord ++ tailWord_6434664) baseStart_6434664 baseEnd_6434664 := by
    simpa [prefixWord, tailWord_6434664, baseEnd_6434664] using wordTrace_append hprefix tailTrace_6434664
  have hstable : (prefixWord ++ tailWord_6434664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434664).length < 2 ^ (prefixWord ++ tailWord_6434664).sum := by decide
  have hdescent : baseEnd_6434664 < baseStart_6434664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434687 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 3, 5, 2]
def baseStart_6434687 : Nat := 118140960795 + 6434687 * 2 ^ 59
def prefixEnd_6434687 : Nat := 4983230072969 + 3 ^ 40 * 6434687 * 2
def baseEnd_6434687 : Nat := 3304087292237570991219919

theorem tailTrace_6434687 : CollatzResearch.WordTrace tailWord_6434687 prefixEnd_6434687 3304087292237570991219919 := by
  unfold tailWord_6434687
  simp only [CollatzResearch.WordTrace]
  refine ⟨234692315639235430892270315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156461543759490287261513543 234692315639235430892270315)
  ·
    refine ⟨352038473458853146338405473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234692315639235430892270315 352038473458853146338405473)
    ·
      refine ⟨264028855094139859753804105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352038473458853146338405473 264028855094139859753804105)
      ·
        refine ⟨198021641320604894815353079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264028855094139859753804105 198021641320604894815353079)
        ·
          refine ⟨297032461980907342223029619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198021641320604894815353079 297032461980907342223029619)
          ·
            refine ⟨445548692971361013334544429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297032461980907342223029619 445548692971361013334544429)
            ·
              refine ⟨167080759864260380000454161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 445548692971361013334544429 167080759864260380000454161)
              ·
                refine ⟨125310569898195285000340621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167080759864260380000454161 125310569898195285000340621)
                ·
                  refine ⟨46991463711823231875127733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125310569898195285000340621 46991463711823231875127733)
                  ·
                    refine ⟨4405449722983427988293225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46991463711823231875127733 4405449722983427988293225)
                    ·
                      refine ⟨3304087292237570991219919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405449722983427988293225 3304087292237570991219919)
                      ·
                        rfl

theorem cell23_6434687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 5, 2].length) (baseStart_6434687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434687 prefixEnd_6434687 := by exact prefixLift 6434687
  have htrace : WordTrace (prefixWord ++ tailWord_6434687) baseStart_6434687 baseEnd_6434687 := by
    simpa [prefixWord, tailWord_6434687, baseEnd_6434687] using wordTrace_append hprefix tailTrace_6434687
  have hstable : (prefixWord ++ tailWord_6434687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434687).length < 2 ^ (prefixWord ++ tailWord_6434687).sum := by decide
  have hdescent : baseEnd_6434687 < baseStart_6434687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434721 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 1, 5, 2]
def baseStart_6434721 : Nat := 118140960795 + 6434721 * 2 ^ 59
def prefixEnd_6434721 : Nat := 4983230072969 + 3 ^ 40 * 6434721 * 2
def baseEnd_6434721 : Nat := 3304104750579823858194763

theorem tailTrace_6434721 : CollatzResearch.WordTrace tailWord_6434721 prefixEnd_6434721 3304104750579823858194763 := by
  unfold tailWord_6434721
  simp only [CollatzResearch.WordTrace]
  refine ⟨234693555721112254699008017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156462370480741503132672011 234693555721112254699008017)
  ·
    refine ⟨176020166790834191024256013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234693555721112254699008017 176020166790834191024256013)
    ·
      refine ⟨66007562546562821634096005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176020166790834191024256013 66007562546562821634096005)
      ·
        refine ⟨12376417977480529056393001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66007562546562821634096005 12376417977480529056393001)
        ·
          refine ⟨9282313483110396792294751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12376417977480529056393001 9282313483110396792294751)
          ·
            refine ⟨13923470224665595188442127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9282313483110396792294751 13923470224665595188442127)
            ·
              refine ⟨20885205336998392782663191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13923470224665595188442127 20885205336998392782663191)
              ·
                refine ⟨31327808005497589173994787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20885205336998392782663191 31327808005497589173994787)
                ·
                  refine ⟨46991712008246383760992181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31327808005497589173994787 46991712008246383760992181)
                  ·
                    refine ⟨4405473000773098477593017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46991712008246383760992181 4405473000773098477593017)
                    ·
                      refine ⟨3304104750579823858194763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405473000773098477593017 3304104750579823858194763)
                      ·
                        rfl

theorem cell23_6434721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_6434721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434721 prefixEnd_6434721 := by exact prefixLift 6434721
  have htrace : WordTrace (prefixWord ++ tailWord_6434721) baseStart_6434721 baseEnd_6434721 := by
    simpa [prefixWord, tailWord_6434721, baseEnd_6434721] using wordTrace_append hprefix tailTrace_6434721
  have hstable : (prefixWord ++ tailWord_6434721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434721).length < 2 ^ (prefixWord ++ tailWord_6434721).sum := by decide
  have hdescent : baseEnd_6434721 < baseStart_6434721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434751 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 3, 2, 2]
def baseStart_6434751 : Nat := 118140960795 + 6434751 * 2 ^ 59
def prefixEnd_6434751 : Nat := 4983230072969 + 3 ^ 40 * 6434751 * 2
def baseEnd_6434751 : Nat := 3304120154999458740819625

theorem tailTrace_6434751 : CollatzResearch.WordTrace tailWord_6434751 prefixEnd_6434751 3304120154999458740819625 := by
  unfold tailWord_6434751
  simp only [CollatzResearch.WordTrace]
  refine ⟨234694649911003569822600107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156463099940669046548400071 234694649911003569822600107)
  ·
    refine ⟨352041974866505354733900161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234694649911003569822600107 352041974866505354733900161)
    ·
      refine ⟨264031481149879016050425121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352041974866505354733900161 264031481149879016050425121)
      ·
        refine ⟨198023610862409262037818841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264031481149879016050425121 198023610862409262037818841)
        ·
          refine ⟨148517708146806946528364131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198023610862409262037818841 148517708146806946528364131)
          ·
            refine ⟨222776562220210419792546197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148517708146806946528364131 222776562220210419792546197)
            ·
              refine ⟨10442651354072363427775603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222776562220210419792546197 10442651354072363427775603)
              ·
                refine ⟨15663977031108545141663405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10442651354072363427775603 15663977031108545141663405)
                ·
                  refine ⟨5873991386665704428123777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15663977031108545141663405 5873991386665704428123777)
                  ·
                    refine ⟨4405493539999278321092833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5873991386665704428123777 4405493539999278321092833)
                    ·
                      refine ⟨3304120154999458740819625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405493539999278321092833 3304120154999458740819625)
                      ·
                        rfl

theorem cell23_6434751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 2, 2].length) (baseStart_6434751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434751 prefixEnd_6434751 := by exact prefixLift 6434751
  have htrace : WordTrace (prefixWord ++ tailWord_6434751) baseStart_6434751 baseEnd_6434751 := by
    simpa [prefixWord, tailWord_6434751, baseEnd_6434751] using wordTrace_append hprefix tailTrace_6434751
  have hstable : (prefixWord ++ tailWord_6434751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434751).length < 2 ^ (prefixWord ++ tailWord_6434751).sum := by decide
  have hdescent : baseEnd_6434751 < baseStart_6434751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434764 : List Nat := [2, 2, 1, 4, 1, 2, 3, 1, 1, 2, 4]
def baseStart_6434764 : Nat := 118140960795 + 6434764 * 2 ^ 59
def prefixEnd_6434764 : Nat := 4983230072969 + 3 ^ 40 * 6434764 * 2
def baseEnd_6434764 : Nat := 3304126830247967189957065

theorem tailTrace_6434764 : CollatzResearch.WordTrace tailWord_6434764 prefixEnd_6434764 3304126830247967189957065 := by
  unfold tailWord_6434764
  simp only [CollatzResearch.WordTrace]
  refine ⟨117347562029978236521411673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156463416039970982028548897 117347562029978236521411673)
  ·
    refine ⟨88010671522483677391058755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117347562029978236521411673 88010671522483677391058755)
    ·
      refine ⟨132016007283725516086588133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88010671522483677391058755 132016007283725516086588133)
      ·
        refine ⟨24753001365698534266235275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132016007283725516086588133 24753001365698534266235275)
        ·
          refine ⟨37129502048547801399352913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24753001365698534266235275 37129502048547801399352913)
          ·
            refine ⟨27847126536410851049514685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37129502048547801399352913 27847126536410851049514685)
            ·
              refine ⟨10442672451154069143568007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27847126536410851049514685 10442672451154069143568007)
              ·
                refine ⟨15664008676731103715352011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10442672451154069143568007 15664008676731103715352011)
                ·
                  refine ⟨23496013015096655573028017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15664008676731103715352011 23496013015096655573028017)
                  ·
                    refine ⟨17622009761322491679771013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23496013015096655573028017 17622009761322491679771013)
                    ·
                      refine ⟨3304126830247967189957065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17622009761322491679771013 3304126830247967189957065)
                      ·
                        rfl

theorem cell23_6434764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_6434764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434764 prefixEnd_6434764 := by exact prefixLift 6434764
  have htrace : WordTrace (prefixWord ++ tailWord_6434764) baseStart_6434764 baseEnd_6434764 := by
    simpa [prefixWord, tailWord_6434764, baseEnd_6434764] using wordTrace_append hprefix tailTrace_6434764
  have hstable : (prefixWord ++ tailWord_6434764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434764).length < 2 ^ (prefixWord ++ tailWord_6434764).sum := by decide
  have hdescent : baseEnd_6434764 < baseStart_6434764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434817 : List Nat := [1, 2, 4, 1, 2, 1, 2, 1, 1, 8]
def baseStart_6434817 : Nat := 118140960795 + 6434817 * 2 ^ 59
def prefixEnd_6434817 : Nat := 4983230072969 + 3 ^ 40 * 6434817 * 2
def baseEnd_6434817 : Nat := 1101384681574218494198107

theorem tailTrace_6434817 : CollatzResearch.WordTrace tailWord_6434817 prefixEnd_6434817 1101384681574218494198107 := by
  unfold tailWord_6434817
  simp only [CollatzResearch.WordTrace]
  refine ⟨234697057128764463094502705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156464704752509642063001803 234697057128764463094502705)
  ·
    refine ⟨176022792846573347320877029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234697057128764463094502705 176022792846573347320877029)
    ·
      refine ⟨33004273658732502622664443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176022792846573347320877029 33004273658732502622664443)
      ·
        refine ⟨49506410488098753933996665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33004273658732502622664443 49506410488098753933996665)
        ·
          refine ⟨37129807866074065450497499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49506410488098753933996665 37129807866074065450497499)
          ·
            refine ⟨55694711799111098175746249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37129807866074065450497499 55694711799111098175746249)
            ·
              refine ⟨41771033849333323631809687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55694711799111098175746249 41771033849333323631809687)
              ·
                refine ⟨62656550773999985447714531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41771033849333323631809687 62656550773999985447714531)
                ·
                  refine ⟨93984826160999978171571797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62656550773999985447714531 93984826160999978171571797)
                  ·
                    refine ⟨1101384681574218494198107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93984826160999978171571797 1101384681574218494198107)
                    ·
                      rfl

theorem cell23_6434817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_6434817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434817 prefixEnd_6434817 := by exact prefixLift 6434817
  have htrace : WordTrace (prefixWord ++ tailWord_6434817) baseStart_6434817 baseEnd_6434817 := by
    simpa [prefixWord, tailWord_6434817, baseEnd_6434817] using wordTrace_append hprefix tailTrace_6434817
  have hstable : (prefixWord ++ tailWord_6434817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434817).length < 2 ^ (prefixWord ++ tailWord_6434817).sum := by decide
  have hdescent : baseEnd_6434817 < baseStart_6434817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434822 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6434822 : Nat := 118140960795 + 6434822 * 2 ^ 59
def prefixEnd_6434822 : Nat := 4983230072969 + 3 ^ 40 * 6434822 * 2
def baseEnd_6434822 : Nat := 3304156612125927963031799

theorem tailTrace_6434822 : CollatzResearch.WordTrace tailWord_6434822 prefixEnd_6434822 3304156612125927963031799 := by
  unfold tailWord_6434822
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334288734179573404638585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156464826329164232632289813 7334288734179573404638585)
  ·
    refine ⟨5500716550634680053478939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7334288734179573404638585 5500716550634680053478939)
    ·
      refine ⟨8251074825952020080218409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5500716550634680053478939 8251074825952020080218409)
      ·
        refine ⟨6188306119464015060163807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8251074825952020080218409 6188306119464015060163807)
        ·
          refine ⟨9282459179196022590245711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6188306119464015060163807 9282459179196022590245711)
          ·
            refine ⟨13923688768794033885368567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9282459179196022590245711 13923688768794033885368567)
            ·
              refine ⟨20885533153191050828052851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13923688768794033885368567 20885533153191050828052851)
              ·
                refine ⟨31328299729786576242079277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20885533153191050828052851 31328299729786576242079277)
                ·
                  refine ⟨11748112398669966090779729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31328299729786576242079277 11748112398669966090779729)
                  ·
                    refine ⟨8811084299002474568084797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11748112398669966090779729 8811084299002474568084797)
                    ·
                      refine ⟨3304156612125927963031799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8811084299002474568084797 3304156612125927963031799)
                      ·
                        rfl

theorem cell23_6434822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6434822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434822 prefixEnd_6434822 := by exact prefixLift 6434822
  have htrace : WordTrace (prefixWord ++ tailWord_6434822) baseStart_6434822 baseEnd_6434822 := by
    simpa [prefixWord, tailWord_6434822, baseEnd_6434822] using wordTrace_append hprefix tailTrace_6434822
  have hstable : (prefixWord ++ tailWord_6434822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434822).length < 2 ^ (prefixWord ++ tailWord_6434822).sum := by decide
  have hdescent : baseEnd_6434822 < baseStart_6434822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434827 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 5]
def baseStart_6434827 : Nat := 118140960795 + 6434827 * 2 ^ 59
def prefixEnd_6434827 : Nat := 4983230072969 + 3 ^ 40 * 6434827 * 2
def baseEnd_6434827 : Nat := 3304159179529200443469275

theorem tailTrace_6434827 : CollatzResearch.WordTrace tailWord_6434827 prefixEnd_6434827 3304159179529200443469275 := by
  unfold tailWord_6434827
  simp only [CollatzResearch.WordTrace]
  refine ⟨234697421858728234802366735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156464947905818823201577823 234697421858728234802366735)
  ·
    refine ⟨352046132788092352203550103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234697421858728234802366735 352046132788092352203550103)
    ·
      refine ⟨528069199182138528305325155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352046132788092352203550103 528069199182138528305325155)
      ·
        refine ⟨792103798773207792457987733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528069199182138528305325155 792103798773207792457987733)
        ·
          refine ⟨37129865567494115271468175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 792103798773207792457987733 37129865567494115271468175)
          ·
            refine ⟨55694798351241172907202263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37129865567494115271468175 55694798351241172907202263)
            ·
              refine ⟨83542197526861759360803395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55694798351241172907202263 83542197526861759360803395)
              ·
                refine ⟨125313296290292639041205093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83542197526861759360803395 125313296290292639041205093)
                ·
                  refine ⟨23496243054429869820225955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125313296290292639041205093 23496243054429869820225955)
                  ·
                    refine ⟨35244364581644804730338933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23496243054429869820225955 35244364581644804730338933)
                    ·
                      refine ⟨3304159179529200443469275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35244364581644804730338933 3304159179529200443469275)
                      ·
                        rfl

theorem cell23_6434827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 5].length) (baseStart_6434827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434827 prefixEnd_6434827 := by exact prefixLift 6434827
  have htrace : WordTrace (prefixWord ++ tailWord_6434827) baseStart_6434827 baseEnd_6434827 := by
    simpa [prefixWord, tailWord_6434827, baseEnd_6434827] using wordTrace_append hprefix tailTrace_6434827
  have hstable : (prefixWord ++ tailWord_6434827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434827).length < 2 ^ (prefixWord ++ tailWord_6434827).sum := by decide
  have hdescent : baseEnd_6434827 < baseStart_6434827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434844 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_6434844 : Nat := 118140960795 + 6434844 * 2 ^ 59
def prefixEnd_6434844 : Nat := 4983230072969 + 3 ^ 40 * 6434844 * 2
def baseEnd_6434844 : Nat := 3304167908700326876956697

theorem tailTrace_6434844 : CollatzResearch.WordTrace tailWord_6434844 prefixEnd_6434844 3304167908700326876956697 := by
  unfold tailWord_6434844
  simp only [CollatzResearch.WordTrace]
  refine ⟨117349020949833323352867793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156465361266444431137157057 117349020949833323352867793)
  ·
    refine ⟨88011765712374992514650845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117349020949833323352867793 88011765712374992514650845)
    ·
      refine ⟨33004412142140622192994067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88011765712374992514650845 33004412142140622192994067)
      ·
        refine ⟨49506618213210933289491101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33004412142140622192994067 49506618213210933289491101)
        ·
          refine ⟨18564981829954099983559163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49506618213210933289491101 18564981829954099983559163)
          ·
            refine ⟨27847472744931149975338745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18564981829954099983559163 27847472744931149975338745)
            ·
              refine ⟨20885604558698362481504059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27847472744931149975338745 20885604558698362481504059)
              ·
                refine ⟨31328406838047543722256089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20885604558698362481504059 31328406838047543722256089)
                ·
                  refine ⟨23496305128535657791692067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31328406838047543722256089 23496305128535657791692067)
                  ·
                    refine ⟨35244457692803486687538101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23496305128535657791692067 35244457692803486687538101)
                    ·
                      refine ⟨3304167908700326876956697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35244457692803486687538101 3304167908700326876956697)
                      ·
                        rfl

theorem cell23_6434844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_6434844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434844 prefixEnd_6434844 := by exact prefixLift 6434844
  have htrace : WordTrace (prefixWord ++ tailWord_6434844) baseStart_6434844 baseEnd_6434844 := by
    simpa [prefixWord, tailWord_6434844, baseEnd_6434844] using wordTrace_append hprefix tailTrace_6434844
  have hstable : (prefixWord ++ tailWord_6434844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434844).length < 2 ^ (prefixWord ++ tailWord_6434844).sum := by decide
  have hdescent : baseEnd_6434844 < baseStart_6434844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434845 : List Nat := [1, 4, 2, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_6434845 : Nat := 118140960795 + 6434845 * 2 ^ 59
def prefixEnd_6434845 : Nat := 4983230072969 + 3 ^ 40 * 6434845 * 2
def baseEnd_6434845 : Nat := 3304168422180981373044193

theorem tailTrace_6434845 : CollatzResearch.WordTrace tailWord_6434845 prefixEnd_6434845 3304168422180981373044193 := by
  unfold tailWord_6434845
  simp only [CollatzResearch.WordTrace]
  refine ⟨234698078372663023876521989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156465385581775349251014659 234698078372663023876521989)
  ·
    refine ⟨44005889694874316976847873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234698078372663023876521989 44005889694874316976847873)
    ·
      refine ⟨33004417271155737732635905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44005889694874316976847873 33004417271155737732635905)
      ·
        refine ⟨24753312953366803299476929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33004417271155737732635905 24753312953366803299476929)
        ·
          refine ⟨18564984715025102474607697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24753312953366803299476929 18564984715025102474607697)
          ·
            refine ⟨13923738536268826855955773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18564984715025102474607697 13923738536268826855955773)
            ·
              refine ⟨5221401951100810070983415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13923738536268826855955773 5221401951100810070983415)
              ·
                refine ⟨7832102926651215106475123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5221401951100810070983415 7832102926651215106475123)
                ·
                  refine ⟨11748154389976822659712685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7832102926651215106475123 11748154389976822659712685)
                  ·
                    refine ⟨4405557896241308497392257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11748154389976822659712685 4405557896241308497392257)
                    ·
                      refine ⟨3304168422180981373044193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405557896241308497392257 3304168422180981373044193)
                      ·
                        rfl

theorem cell23_6434845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_6434845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434845 prefixEnd_6434845 := by exact prefixLift 6434845
  have htrace : WordTrace (prefixWord ++ tailWord_6434845) baseStart_6434845 baseEnd_6434845 := by
    simpa [prefixWord, tailWord_6434845, baseEnd_6434845] using wordTrace_append hprefix tailTrace_6434845
  have hstable : (prefixWord ++ tailWord_6434845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434845).length < 2 ^ (prefixWord ++ tailWord_6434845).sum := by decide
  have hdescent : baseEnd_6434845 < baseStart_6434845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434894 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_6434894 : Nat := 118140960795 + 6434894 * 2 ^ 59
def prefixEnd_6434894 : Nat := 4983230072969 + 3 ^ 40 * 6434894 * 2
def baseEnd_6434894 : Nat := 1101397860911017227110489

theorem tailTrace_6434894 : CollatzResearch.WordTrace tailWord_6434894 prefixEnd_6434894 1101397860911017227110489 := by
  unfold tailWord_6434894
  simp only [CollatzResearch.WordTrace]
  refine ⟨29337483193685688155631967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156466577032990336830037157 29337483193685688155631967)
  ·
    refine ⟨44006224790528532233447951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29337483193685688155631967 44006224790528532233447951)
    ·
      refine ⟨66009337185792798350171927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44006224790528532233447951 66009337185792798350171927)
      ·
        refine ⟨99014005778689197525257891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66009337185792798350171927 99014005778689197525257891)
        ·
          refine ⟨148521008668033796287886837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99014005778689197525257891 148521008668033796287886837)
          ·
            refine ⟨13923844562628168401989391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148521008668033796287886837 13923844562628168401989391)
            ·
              refine ⟨20885766843942252602984087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13923844562628168401989391 20885766843942252602984087)
              ·
                refine ⟨31328650265913378904476131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20885766843942252602984087 31328650265913378904476131)
                ·
                  refine ⟨46992975398870068356714197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31328650265913378904476131 46992975398870068356714197)
                  ·
                    refine ⟨1101397860911017227110489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46992975398870068356714197 1101397860911017227110489)
                    ·
                      rfl

theorem cell23_6434894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_6434894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434894 prefixEnd_6434894 := by exact prefixLift 6434894
  have htrace : WordTrace (prefixWord ++ tailWord_6434894) baseStart_6434894 baseEnd_6434894 := by
    simpa [prefixWord, tailWord_6434894, baseEnd_6434894] using wordTrace_append hprefix tailTrace_6434894
  have hstable : (prefixWord ++ tailWord_6434894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434894).length < 2 ^ (prefixWord ++ tailWord_6434894).sum := by decide
  have hdescent : baseEnd_6434894 < baseStart_6434894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434898 : List Nat := [3, 2, 2, 1, 4, 1, 2, 3, 5]
def baseStart_6434898 : Nat := 118140960795 + 6434898 * 2 ^ 59
def prefixEnd_6434898 : Nat := 4983230072969 + 3 ^ 40 * 6434898 * 2
def baseEnd_6434898 : Nat := 367132848517296629520161

theorem tailTrace_6434898 : CollatzResearch.WordTrace tailWord_6434898 prefixEnd_6434898 367132848517296629520161 := by
  unfold tailWord_6434898
  simp only [CollatzResearch.WordTrace]
  refine ⟨58675002860367753482050337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156466674294314009285467565 58675002860367753482050337)
  ·
    refine ⟨44006252145275815111537753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58675002860367753482050337 44006252145275815111537753)
    ·
      refine ⟨33004689108956861333653315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44006252145275815111537753 33004689108956861333653315)
      ·
        refine ⟨49507033663435292000479973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33004689108956861333653315 49507033663435292000479973)
        ·
          refine ⟨9282568811894117250089995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49507033663435292000479973 9282568811894117250089995)
          ·
            refine ⟨13923853217841175875134993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9282568811894117250089995 13923853217841175875134993)
            ·
              refine ⟨10442889913380881906351245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13923853217841175875134993 10442889913380881906351245)
              ·
                refine ⟨3916083717517830714881717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10442889913380881906351245 3916083717517830714881717)
                ·
                  refine ⟨367132848517296629520161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3916083717517830714881717 367132848517296629520161)
                  ·
                    rfl

theorem cell23_6434898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_6434898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434898 prefixEnd_6434898 := by exact prefixLift 6434898
  have htrace : WordTrace (prefixWord ++ tailWord_6434898) baseStart_6434898 baseEnd_6434898 := by
    simpa [prefixWord, tailWord_6434898, baseEnd_6434898] using wordTrace_append hprefix tailTrace_6434898
  have hstable : (prefixWord ++ tailWord_6434898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434898).length < 2 ^ (prefixWord ++ tailWord_6434898).sum := by decide
  have hdescent : baseEnd_6434898 < baseStart_6434898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434941 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_6434941 : Nat := 118140960795 + 6434941 * 2 ^ 59
def prefixEnd_6434941 : Nat := 4983230072969 + 3 ^ 40 * 6434941 * 2
def baseEnd_6434941 : Nat := 1101405905441270999147917

theorem tailTrace_6434941 : CollatzResearch.WordTrace tailWord_6434941 prefixEnd_6434941 1101405905441270999147917 := by
  unfold tailWord_6434941
  simp only [CollatzResearch.WordTrace]
  refine ⟨234701579780315232272016677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156467719853543488181344451 234701579780315232272016677)
  ·
    refine ⟨44006546208809106051003127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234701579780315232272016677 44006546208809106051003127)
    ·
      refine ⟨66009819313213659076504691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44006546208809106051003127 66009819313213659076504691)
      ·
        refine ⟨99014728969820488614757037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66009819313213659076504691 99014728969820488614757037)
        ·
          refine ⟨37130523363682683230533889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99014728969820488614757037 37130523363682683230533889)
          ·
            refine ⟨27847892522762012422900417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37130523363682683230533889 27847892522762012422900417)
            ·
              refine ⟨20885919392071509317175313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27847892522762012422900417 20885919392071509317175313)
              ·
                refine ⟨15664439544053631987881485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20885919392071509317175313 15664439544053631987881485)
                ·
                  refine ⟨5874164829020111995455557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15664439544053631987881485 5874164829020111995455557)
                  ·
                    refine ⟨1101405905441270999147917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5874164829020111995455557 1101405905441270999147917)
                    ·
                      rfl

theorem cell23_6434941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_6434941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434941 prefixEnd_6434941 := by exact prefixLift 6434941
  have htrace : WordTrace (prefixWord ++ tailWord_6434941) baseStart_6434941 baseEnd_6434941 := by
    simpa [prefixWord, tailWord_6434941, baseEnd_6434941] using wordTrace_append hprefix tailTrace_6434941
  have hstable : (prefixWord ++ tailWord_6434941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434941).length < 2 ^ (prefixWord ++ tailWord_6434941).sum := by decide
  have hdescent : baseEnd_6434941 < baseStart_6434941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434954 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 8]
def baseStart_6434954 : Nat := 118140960795 + 6434954 * 2 ^ 59
def prefixEnd_6434954 : Nat := 4983230072969 + 3 ^ 40 * 6434954 * 2
def baseEnd_6434954 : Nat := 367136043508035716286799

theorem tailTrace_6434954 : CollatzResearch.WordTrace tailWord_6434954 prefixEnd_6434954 367136043508035716286799 := by
  unfold tailWord_6434954
  simp only [CollatzResearch.WordTrace]
  refine ⟨58675513482317033873059979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156468035952845423661493277 58675513482317033873059979)
  ·
    refine ⟨88013270223475550809589969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58675513482317033873059979 88013270223475550809589969)
    ·
      refine ⟨66009952667606663107192477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88013270223475550809589969 66009952667606663107192477)
      ·
        refine ⟨24753732250352498665197179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66009952667606663107192477 24753732250352498665197179)
        ·
          refine ⟨37130598375528747997795769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24753732250352498665197179 37130598375528747997795769)
          ·
            refine ⟨27847948781646560998346827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37130598375528747997795769 27847948781646560998346827)
            ·
              refine ⟨41771923172469841497520241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27847948781646560998346827 41771923172469841497520241)
              ·
                refine ⟨31328942379352381123140181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41771923172469841497520241 31328942379352381123140181)
                ·
                  refine ⟨367136043508035716286799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31328942379352381123140181 367136043508035716286799)
                  ·
                    rfl

theorem cell23_6434954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_6434954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434954 prefixEnd_6434954 := by exact prefixLift 6434954
  have htrace : WordTrace (prefixWord ++ tailWord_6434954) baseStart_6434954 baseEnd_6434954 := by
    simpa [prefixWord, tailWord_6434954, baseEnd_6434954] using wordTrace_append hprefix tailTrace_6434954
  have hstable : (prefixWord ++ tailWord_6434954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434954).length < 2 ^ (prefixWord ++ tailWord_6434954).sum := by decide
  have hdescent : baseEnd_6434954 < baseStart_6434954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434966 : List Nat := [5, 3, 2, 1, 1, 1, 3, 2, 5]
def baseStart_6434966 : Nat := 118140960795 + 6434966 * 2 ^ 59
def prefixEnd_6434966 : Nat := 4983230072969 + 3 ^ 40 * 6434966 * 2
def baseEnd_6434966 : Nat := 367136728148908377736793

theorem tailTrace_6434966 : CollatzResearch.WordTrace tailWord_6434966 prefixEnd_6434966 367136728148908377736793 := by
  unfold tailWord_6434966
  simp only [CollatzResearch.WordTrace]
  refine ⟨14668905725326541346354797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156468327736816441027784501 14668905725326541346354797)
  ·
    refine ⟨5500839646997453004883049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14668905725326541346354797 5500839646997453004883049)
    ·
      refine ⟨4125629735248089753662287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5500839646997453004883049 4125629735248089753662287)
      ·
        refine ⟨6188444602872134630493431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4125629735248089753662287 6188444602872134630493431)
        ·
          refine ⟨9282666904308201945740147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6188444602872134630493431 9282666904308201945740147)
          ·
            refine ⟨13924000356462302918610221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9282666904308201945740147 13924000356462302918610221)
            ·
              refine ⟨5221500133673363594478833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13924000356462302918610221 5221500133673363594478833)
              ·
                refine ⟨3916125100255022695859125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5221500133673363594478833 3916125100255022695859125)
                ·
                  refine ⟨367136728148908377736793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3916125100255022695859125 367136728148908377736793)
                  ·
                    rfl

theorem cell23_6434966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_6434966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434966 prefixEnd_6434966 := by exact prefixLift 6434966
  have htrace : WordTrace (prefixWord ++ tailWord_6434966) baseStart_6434966 baseEnd_6434966 := by
    simpa [prefixWord, tailWord_6434966, baseEnd_6434966] using wordTrace_append hprefix tailTrace_6434966
  have hstable : (prefixWord ++ tailWord_6434966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434966).length < 2 ^ (prefixWord ++ tailWord_6434966).sum := by decide
  have hdescent : baseEnd_6434966 < baseStart_6434966 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434968 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 2, 2, 3]
def baseStart_6434968 : Nat := 118140960795 + 6434968 * 2 ^ 59
def prefixEnd_6434968 : Nat := 4983230072969 + 3 ^ 40 * 6434968 * 2
def baseEnd_6434968 : Nat := 3304231580301484391806127

theorem tailTrace_6434968 : CollatzResearch.WordTrace tailWord_6434968 prefixEnd_6434968 3304231580301484391806127 := by
  unfold tailWord_6434968
  simp only [CollatzResearch.WordTrace]
  refine ⟨117351282275608707941624779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156468376367478277255499705 117351282275608707941624779)
  ·
    refine ⟨176026923413413061912437169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117351282275608707941624779 176026923413413061912437169)
    ·
      refine ⟨132020192560059796434327877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176026923413413061912437169 132020192560059796434327877)
      ·
        refine ⟨24753786105011211831436477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132020192560059796434327877 24753786105011211831436477)
        ·
          refine ⟨9282669789379204436788679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24753786105011211831436477 9282669789379204436788679)
          ·
            refine ⟨13924004684068806655183019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9282669789379204436788679 13924004684068806655183019)
            ·
              refine ⟨20886007026103209982774529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13924004684068806655183019 20886007026103209982774529)
              ·
                refine ⟨15664505269577407487080897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20886007026103209982774529 15664505269577407487080897)
                ·
                  refine ⟨11748378952183055615310673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15664505269577407487080897 11748378952183055615310673)
                  ·
                    refine ⟨8811284214137291711483005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11748378952183055615310673 8811284214137291711483005)
                    ·
                      refine ⟨3304231580301484391806127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8811284214137291711483005 3304231580301484391806127)
                      ·
                        rfl

theorem cell23_6434968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_6434968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434968 prefixEnd_6434968 := by exact prefixLift 6434968
  have htrace : WordTrace (prefixWord ++ tailWord_6434968) baseStart_6434968 baseEnd_6434968 := by
    simpa [prefixWord, tailWord_6434968, baseEnd_6434968] using wordTrace_append hprefix tailTrace_6434968
  have hstable : (prefixWord ++ tailWord_6434968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434968).length < 2 ^ (prefixWord ++ tailWord_6434968).sum := by decide
  have hdescent : baseEnd_6434968 < baseStart_6434968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6434991 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 6, 3, 2]
def baseStart_6434991 : Nat := 118140960795 + 6434991 * 2 ^ 59
def prefixEnd_6434991 : Nat := 4983230072969 + 3 ^ 40 * 6434991 * 2
def baseEnd_6434991 : Nat := 3304243390356537801818521

theorem tailTrace_6434991 : CollatzResearch.WordTrace tailWord_6434991 prefixEnd_6434991 3304243390356537801818521 := by
  unfold tailWord_6434991
  simp only [CollatzResearch.WordTrace]
  refine ⟨234703403430134090811336827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156468935620089393874224551 234703403430134090811336827)
  ·
    refine ⟨352055105145201136217005241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234703403430134090811336827 352055105145201136217005241)
    ·
      refine ⟨264041328858900852162753931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352055105145201136217005241 264041328858900852162753931)
      ·
        refine ⟨396061993288351278244130897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264041328858900852162753931 396061993288351278244130897)
        ·
          refine ⟨297046494966263458683098173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396061993288351278244130897 297046494966263458683098173)
          ·
            refine ⟨111392435612348797006161815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297046494966263458683098173 111392435612348797006161815)
            ·
              refine ⟨167088653418523195509242723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111392435612348797006161815 167088653418523195509242723)
              ·
                refine ⟨250632980127784793263864085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167088653418523195509242723 250632980127784793263864085)
                ·
                  refine ⟨11748420943489912184243629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 250632980127784793263864085 11748420943489912184243629)
                  ·
                    refine ⟨4405657853808717069091361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11748420943489912184243629 4405657853808717069091361)
                    ·
                      refine ⟨3304243390356537801818521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405657853808717069091361 3304243390356537801818521)
                      ·
                        rfl

theorem cell23_6434991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 3, 2].length) (baseStart_6434991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6434991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6434991 prefixEnd_6434991 := by exact prefixLift 6434991
  have htrace : WordTrace (prefixWord ++ tailWord_6434991) baseStart_6434991 baseEnd_6434991 := by
    simpa [prefixWord, tailWord_6434991, baseEnd_6434991] using wordTrace_append hprefix tailTrace_6434991
  have hstable : (prefixWord ++ tailWord_6434991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6434991).length < 2 ^ (prefixWord ++ tailWord_6434991).sum := by decide
  have hdescent : baseEnd_6434991 < baseStart_6434991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6434991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435008 : List Nat := [2, 1, 1, 2, 5, 1, 1, 3, 2, 3, 2]
def baseStart_6435008 : Nat := 118140960795 + 6435008 * 2 ^ 59
def prefixEnd_6435008 : Nat := 4983230072969 + 3 ^ 40 * 6435008 * 2
def baseEnd_6435008 : Nat := 3304252119527664235305943

theorem tailTrace_6435008 : CollatzResearch.WordTrace tailWord_6435008 prefixEnd_6435008 3304252119527664235305943 := by
  unfold tailWord_6435008
  simp only [CollatzResearch.WordTrace]
  refine ⟨117352011735536251357352839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156469348980715001809803785 117352011735536251357352839)
  ·
    refine ⟨176028017603304377036029259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117352011735536251357352839 176028017603304377036029259)
    ·
      refine ⟨264042026404956565554043889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176028017603304377036029259 264042026404956565554043889)
      ·
        refine ⟨198031519803717424165532917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264042026404956565554043889 198031519803717424165532917)
        ·
          refine ⟨18565454981598508515518711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 198031519803717424165532917 18565454981598508515518711)
          ·
            refine ⟨27848182472397762773278067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18565454981598508515518711 27848182472397762773278067)
            ·
              refine ⟨41772273708596644159917101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27848182472397762773278067 41772273708596644159917101)
              ·
                refine ⟨15664602640723741559968913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41772273708596644159917101 15664602640723741559968913)
                ·
                  refine ⟨11748451980542806169976685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15664602640723741559968913 11748451980542806169976685)
                  ·
                    refine ⟨4405669492703552313741257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11748451980542806169976685 4405669492703552313741257)
                    ·
                      refine ⟨3304252119527664235305943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405669492703552313741257 3304252119527664235305943)
                      ·
                        rfl

theorem cell23_6435008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 2, 3, 2].length) (baseStart_6435008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435008 prefixEnd_6435008 := by exact prefixLift 6435008
  have htrace : WordTrace (prefixWord ++ tailWord_6435008) baseStart_6435008 baseEnd_6435008 := by
    simpa [prefixWord, tailWord_6435008, baseEnd_6435008] using wordTrace_append hprefix tailTrace_6435008
  have hstable : (prefixWord ++ tailWord_6435008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435008).length < 2 ^ (prefixWord ++ tailWord_6435008).sum := by decide
  have hdescent : baseEnd_6435008 < baseStart_6435008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435018 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 1, 5]
def baseStart_6435018 : Nat := 118140960795 + 6435018 * 2 ^ 59
def prefixEnd_6435018 : Nat := 4983230072969 + 3 ^ 40 * 6435018 * 2
def baseEnd_6435018 : Nat := 1101419084778069732060299

theorem tailTrace_6435018 : CollatzResearch.WordTrace tailWord_6435018 prefixEnd_6435018 1101419084778069732060299 := by
  unfold tailWord_6435018
  simp only [CollatzResearch.WordTrace]
  refine ⟨58676097050259068605642427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156469592134024182948379805 58676097050259068605642427)
  ·
    refine ⟨88014145575388602908463641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58676097050259068605642427 88014145575388602908463641)
    ·
      refine ⟨66010609181541452181347731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88014145575388602908463641 66010609181541452181347731)
      ·
        refine ⟨99015913772312178272021597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66010609181541452181347731 99015913772312178272021597)
        ·
          refine ⟨37130967664617066852008099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99015913772312178272021597 37130967664617066852008099)
          ·
            refine ⟨55696451496925600278012149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37130967664617066852008099 55696451496925600278012149)
            ·
              refine ⟨5221542327836775026063639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55696451496925600278012149 5221542327836775026063639)
              ·
                refine ⟨7832313491755162539095459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5221542327836775026063639 7832313491755162539095459)
                ·
                  refine ⟨11748470237632743808643189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7832313491755162539095459 11748470237632743808643189)
                  ·
                    refine ⟨1101419084778069732060299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11748470237632743808643189 1101419084778069732060299)
                    ·
                      rfl

theorem cell23_6435018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_6435018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435018 prefixEnd_6435018 := by exact prefixLift 6435018
  have htrace : WordTrace (prefixWord ++ tailWord_6435018) baseStart_6435018 baseEnd_6435018 := by
    simpa [prefixWord, tailWord_6435018, baseEnd_6435018] using wordTrace_append hprefix tailTrace_6435018
  have hstable : (prefixWord ++ tailWord_6435018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435018).length < 2 ^ (prefixWord ++ tailWord_6435018).sum := by decide
  have hdescent : baseEnd_6435018 < baseStart_6435018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435032 : List Nat := [2, 1, 2, 2, 4, 1, 4, 2, 1, 1, 3]
def baseStart_6435032 : Nat := 118140960795 + 6435032 * 2 ^ 59
def prefixEnd_6435032 : Nat := 4983230072969 + 3 ^ 40 * 6435032 * 2
def baseEnd_6435032 : Nat := 3304264443063372141405833

theorem tailTrace_6435032 : CollatzResearch.WordTrace tailWord_6435032 prefixEnd_6435032 3304264443063372141405833 := by
  unfold tailWord_6435032
  simp only [CollatzResearch.WordTrace]
  refine ⟨117352449411492777406789675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156469932548657036542386233 117352449411492777406789675)
  ·
    refine ⟨176028674117239166110184513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117352449411492777406789675 176028674117239166110184513)
    ·
      refine ⟨132021505587929374582638385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176028674117239166110184513 132021505587929374582638385)
      ·
        refine ⟨99016129190947030936978789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132021505587929374582638385 99016129190947030936978789)
        ·
          refine ⟨18565524223302568300683523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99016129190947030936978789 18565524223302568300683523)
          ·
            refine ⟨27848286334953852451025285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18565524223302568300683523 27848286334953852451025285)
            ·
              refine ⟨5221553687803847334567241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27848286334953852451025285 5221553687803847334567241)
              ·
                refine ⟨3916165265852885500925431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5221553687803847334567241 3916165265852885500925431)
                ·
                  refine ⟨5874247898779328251388147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916165265852885500925431 5874247898779328251388147)
                  ·
                    refine ⟨8811371848168992377082221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5874247898779328251388147 8811371848168992377082221)
                    ·
                      refine ⟨3304264443063372141405833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8811371848168992377082221 3304264443063372141405833)
                      ·
                        rfl

theorem cell23_6435032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_6435032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435032 prefixEnd_6435032 := by exact prefixLift 6435032
  have htrace : WordTrace (prefixWord ++ tailWord_6435032) baseStart_6435032 baseEnd_6435032 := by
    simpa [prefixWord, tailWord_6435032, baseEnd_6435032] using wordTrace_append hprefix tailTrace_6435032
  have hstable : (prefixWord ++ tailWord_6435032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435032).length < 2 ^ (prefixWord ++ tailWord_6435032).sum := by decide
  have hdescent : baseEnd_6435032 < baseStart_6435032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435034 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_6435034 : Nat := 118140960795 + 6435034 * 2 ^ 59
def prefixEnd_6435034 : Nat := 4983230072969 + 3 ^ 40 * 6435034 * 2
def baseEnd_6435034 : Nat := 3304265470024681133580823

theorem tailTrace_6435034 : CollatzResearch.WordTrace tailWord_6435034 prefixEnd_6435034 3304265470024681133580823 := by
  unfold tailWord_6435034
  simp only [CollatzResearch.WordTrace]
  refine ⟨58676242942244577288788039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156469981179318872770101437 58676242942244577288788039)
  ·
    refine ⟨88014364413366865933182059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58676242942244577288788039 88014364413366865933182059)
    ·
      refine ⟨132021546620050298899773089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88014364413366865933182059 132021546620050298899773089)
      ·
        refine ⟨99016159965037724174829817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132021546620050298899773089 99016159965037724174829817)
        ·
          refine ⟨74262119973778293131122363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99016159965037724174829817 74262119973778293131122363)
          ·
            refine ⟨111393179960667439696683545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74262119973778293131122363 111393179960667439696683545)
            ·
              refine ⟨83544884970500579772512659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111393179960667439696683545 83544884970500579772512659)
              ·
                refine ⟨125317327455750869658768989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83544884970500579772512659 125317327455750869658768989)
                ·
                  refine ⟨46993997795906576122038371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125317327455750869658768989 46993997795906576122038371)
                  ·
                    refine ⟨70490996693859864183057557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46993997795906576122038371 70490996693859864183057557)
                    ·
                      refine ⟨3304265470024681133580823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70490996693859864183057557 3304265470024681133580823)
                      ·
                        rfl

theorem cell23_6435034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_6435034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435034 prefixEnd_6435034 := by exact prefixLift 6435034
  have htrace : WordTrace (prefixWord ++ tailWord_6435034) baseStart_6435034 baseEnd_6435034 := by
    simpa [prefixWord, tailWord_6435034, baseEnd_6435034] using wordTrace_append hprefix tailTrace_6435034
  have hstable : (prefixWord ++ tailWord_6435034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435034).length < 2 ^ (prefixWord ++ tailWord_6435034).sum := by decide
  have hdescent : baseEnd_6435034 < baseStart_6435034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435041 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_6435041 : Nat := 118140960795 + 6435041 * 2 ^ 59
def prefixEnd_6435041 : Nat := 4983230072969 + 3 ^ 40 * 6435041 * 2
def baseEnd_6435041 : Nat := 3304269064389262606193291

theorem tailTrace_6435041 : CollatzResearch.WordTrace tailWord_6435041 prefixEnd_6435041 3304269064389262606193291 := by
  unfold tailWord_6435041
  simp only [CollatzResearch.WordTrace]
  refine ⟨234705227079952949350656977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156470151386635299567104651 234705227079952949350656977)
  ·
    refine ⟨176028920309964712012992733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234705227079952949350656977 176028920309964712012992733)
    ·
      refine ⟨66010845116236767004872275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176028920309964712012992733 66010845116236767004872275)
      ·
        refine ⟨99016267674355150507308413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66010845116236767004872275 99016267674355150507308413)
        ·
          refine ⟨37131100377883181440240655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99016267674355150507308413 37131100377883181440240655)
          ·
            refine ⟨55696650566824772160360983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37131100377883181440240655 55696650566824772160360983)
            ·
              refine ⟨83544975850237158240541475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55696650566824772160360983 83544975850237158240541475)
              ·
                refine ⟨125317463775355737360812213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83544975850237158240541475 125317463775355737360812213)
                ·
                  refine ⟨11748512228939600377576145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125317463775355737360812213 11748512228939600377576145)
                  ·
                    refine ⟨8811384171704700283182109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11748512228939600377576145 8811384171704700283182109)
                    ·
                      refine ⟨3304269064389262606193291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8811384171704700283182109 3304269064389262606193291)
                      ·
                        rfl

theorem cell23_6435041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_6435041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435041 prefixEnd_6435041 := by exact prefixLift 6435041
  have htrace : WordTrace (prefixWord ++ tailWord_6435041) baseStart_6435041 baseEnd_6435041 := by
    simpa [prefixWord, tailWord_6435041, baseEnd_6435041] using wordTrace_append hprefix tailTrace_6435041
  have hstable : (prefixWord ++ tailWord_6435041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435041).length < 2 ^ (prefixWord ++ tailWord_6435041).sum := by decide
  have hdescent : baseEnd_6435041 < baseStart_6435041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435048 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 2, 4]
def baseStart_6435048 : Nat := 118140960795 + 6435048 * 2 ^ 59
def prefixEnd_6435048 : Nat := 4983230072969 + 3 ^ 40 * 6435048 * 2
def baseEnd_6435048 : Nat := 1101424219584614692935253

theorem tailTrace_6435048 : CollatzResearch.WordTrace tailWord_6435048 prefixEnd_6435048 1101424219584614692935253 := by
  unfold tailWord_6435048
  simp only [CollatzResearch.WordTrace]
  refine ⟨117352741195463794773080899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156470321593951726364107865 117352741195463794773080899)
  ·
    refine ⟨176029111793195692159621349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117352741195463794773080899 176029111793195692159621349)
    ·
      refine ⟨33005458461224192279929003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176029111793195692159621349 33005458461224192279929003)
      ·
        refine ⟨49508187691836288419893505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33005458461224192279929003 49508187691836288419893505)
        ·
          refine ⟨37131140768877216314920129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49508187691836288419893505 37131140768877216314920129)
          ·
            refine ⟨27848355576657912236190097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37131140768877216314920129 27848355576657912236190097)
            ·
              refine ⟨20886266682493434177142573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27848355576657912236190097 20886266682493434177142573)
              ·
                refine ⟨7832350005935037816428465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20886266682493434177142573 7832350005935037816428465)
                ·
                  refine ⟨5874262504451278362321349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7832350005935037816428465 5874262504451278362321349)
                  ·
                    refine ⟨1101424219584614692935253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5874262504451278362321349 1101424219584614692935253)
                    ·
                      rfl

theorem cell23_6435048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_6435048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435048 prefixEnd_6435048 := by exact prefixLift 6435048
  have htrace : WordTrace (prefixWord ++ tailWord_6435048) baseStart_6435048 baseEnd_6435048 := by
    simpa [prefixWord, tailWord_6435048, baseEnd_6435048] using wordTrace_append hprefix tailTrace_6435048
  have hstable : (prefixWord ++ tailWord_6435048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435048).length < 2 ^ (prefixWord ++ tailWord_6435048).sum := by decide
  have hdescent : baseEnd_6435048 < baseStart_6435048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435051 : List Nat := [1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 4]
def baseStart_6435051 : Nat := 118140960795 + 6435051 * 2 ^ 59
def prefixEnd_6435051 : Nat := 4983230072969 + 3 ^ 40 * 6435051 * 2
def baseEnd_6435051 : Nat := 3304274199195807567068245

theorem tailTrace_6435051 : CollatzResearch.WordTrace tailWord_6435051 prefixEnd_6435051 3304274199195807567068245 := by
  unfold tailWord_6435051
  simp only [CollatzResearch.WordTrace]
  refine ⟨234705591809916721058521007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156470394539944480705680671 234705591809916721058521007)
  ·
    refine ⟨352058387714875081587781511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234705591809916721058521007 352058387714875081587781511)
    ·
      refine ⟨528087581572312622381672267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352058387714875081587781511 528087581572312622381672267)
      ·
        refine ⟨792131372358468933572508401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528087581572312622381672267 792131372358468933572508401)
        ·
          refine ⟨594098529268851700179381301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792131372358468933572508401 594098529268851700179381301)
          ·
            refine ⟨55696737118954846891816997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 594098529268851700179381301 55696737118954846891816997)
            ·
              refine ⟨10443138209804033792215687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55696737118954846891816997 10443138209804033792215687)
              ·
                refine ⟨15664707314706050688323531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10443138209804033792215687 15664707314706050688323531)
                ·
                  refine ⟨23497060972059076032485297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15664707314706050688323531 23497060972059076032485297)
                  ·
                    refine ⟨17622795729044307024363973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23497060972059076032485297 17622795729044307024363973)
                    ·
                      refine ⟨3304274199195807567068245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17622795729044307024363973 3304274199195807567068245)
                      ·
                        rfl

theorem cell23_6435051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 4].length) (baseStart_6435051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435051 prefixEnd_6435051 := by exact prefixLift 6435051
  have htrace : WordTrace (prefixWord ++ tailWord_6435051) baseStart_6435051 baseEnd_6435051 := by
    simpa [prefixWord, tailWord_6435051, baseEnd_6435051] using wordTrace_append hprefix tailTrace_6435051
  have hstable : (prefixWord ++ tailWord_6435051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435051).length < 2 ^ (prefixWord ++ tailWord_6435051).sum := by decide
  have hdescent : baseEnd_6435051 < baseStart_6435051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435055 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 3, 2, 2]
def baseStart_6435055 : Nat := 118140960795 + 6435055 * 2 ^ 59
def prefixEnd_6435055 : Nat := 4983230072969 + 3 ^ 40 * 6435055 * 2
def baseEnd_6435055 : Nat := 3304276253118425551418227

theorem tailTrace_6435055 : CollatzResearch.WordTrace tailWord_6435055 prefixEnd_6435055 3304276253118425551418227 := by
  unfold tailWord_6435055
  simp only [CollatzResearch.WordTrace]
  refine ⟨234705737701902229741666619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156470491801268153161111079 234705737701902229741666619)
  ·
    refine ⟨352058606552853344612499929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234705737701902229741666619 352058606552853344612499929)
    ·
      refine ⟨264043954914640008459374947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352058606552853344612499929 264043954914640008459374947)
      ·
        refine ⟨396065932371960012689062421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264043954914640008459374947 396065932371960012689062421)
        ·
          refine ⟨18565590579935625594799801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 396065932371960012689062421 18565590579935625594799801)
          ·
            refine ⟨13924192934951719196099851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18565590579935625594799801 13924192934951719196099851)
            ·
              refine ⟨20886289402427578794149777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13924192934951719196099851 20886289402427578794149777)
              ·
                refine ⟨15664717051820684095612333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20886289402427578794149777 15664717051820684095612333)
                ·
                  refine ⟨5874268894432756535854625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15664717051820684095612333 5874268894432756535854625)
                  ·
                    refine ⟨4405701670824567401890969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5874268894432756535854625 4405701670824567401890969)
                    ·
                      refine ⟨3304276253118425551418227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405701670824567401890969 3304276253118425551418227)
                      ·
                        rfl

theorem cell23_6435055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 2, 2].length) (baseStart_6435055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435055 prefixEnd_6435055 := by exact prefixLift 6435055
  have htrace : WordTrace (prefixWord ++ tailWord_6435055) baseStart_6435055 baseEnd_6435055 := by
    simpa [prefixWord, tailWord_6435055, baseEnd_6435055] using wordTrace_append hprefix tailTrace_6435055
  have hstable : (prefixWord ++ tailWord_6435055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435055).length < 2 ^ (prefixWord ++ tailWord_6435055).sum := by decide
  have hdescent : baseEnd_6435055 < baseStart_6435055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435058 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_6435058 : Nat := 118140960795 + 6435058 * 2 ^ 59
def prefixEnd_6435058 : Nat := 4983230072969 + 3 ^ 40 * 6435058 * 2
def baseEnd_6435058 : Nat := 3304277793560389039680713

theorem tailTrace_6435058 : CollatzResearch.WordTrace tailWord_6435058 prefixEnd_6435058 3304277793560389039680713 := by
  unfold tailWord_6435058
  simp only [CollatzResearch.WordTrace]
  refine ⟨58676461780222840313506457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156470564747260907502683885 58676461780222840313506457)
  ·
    refine ⟨44007346335167130235129843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58676461780222840313506457 44007346335167130235129843)
    ·
      refine ⟨66011019502750695352694765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44007346335167130235129843 66011019502750695352694765)
      ·
        refine ⟨24754132313531510757260537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66011019502750695352694765 24754132313531510757260537)
        ·
          refine ⟨18565599235148633067945403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24754132313531510757260537 18565599235148633067945403)
          ·
            refine ⟨27848398852722949601918105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18565599235148633067945403 27848398852722949601918105)
            ·
              refine ⟨20886299139542212201438579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27848398852722949601918105 20886299139542212201438579)
              ·
                refine ⟨31329448709313318302157869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20886299139542212201438579 31329448709313318302157869)
                ·
                  refine ⟨11748543265992494363309201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31329448709313318302157869 11748543265992494363309201)
                  ·
                    refine ⟨8811407449494370772481901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11748543265992494363309201 8811407449494370772481901)
                    ·
                      refine ⟨3304277793560389039680713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8811407449494370772481901 3304277793560389039680713)
                      ·
                        rfl

theorem cell23_6435058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_6435058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435058 prefixEnd_6435058 := by exact prefixLift 6435058
  have htrace : WordTrace (prefixWord ++ tailWord_6435058) baseStart_6435058 baseEnd_6435058 := by
    simpa [prefixWord, tailWord_6435058, baseEnd_6435058] using wordTrace_append hprefix tailTrace_6435058
  have hstable : (prefixWord ++ tailWord_6435058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435058).length < 2 ^ (prefixWord ++ tailWord_6435058).sum := by decide
  have hdescent : baseEnd_6435058 < baseStart_6435058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435071 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 3]
def baseStart_6435071 : Nat := 118140960795 + 6435071 * 2 ^ 59
def prefixEnd_6435071 : Nat := 4983230072969 + 3 ^ 40 * 6435071 * 2
def baseEnd_6435071 : Nat := 3304284468808897488818153

theorem tailTrace_6435071 : CollatzResearch.WordTrace tailWord_6435071 prefixEnd_6435071 3304284468808897488818153 := by
  unfold tailWord_6435071
  simp only [CollatzResearch.WordTrace]
  refine ⟨234706321269844264474249067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156470880846562842982832711 234706321269844264474249067)
  ·
    refine ⟨352059481904766396711373601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234706321269844264474249067 352059481904766396711373601)
    ·
      refine ⟨264044611428574797533530201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352059481904766396711373601 264044611428574797533530201)
      ·
        refine ⟨198033458571431098150147651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264044611428574797533530201 198033458571431098150147651)
        ·
          refine ⟨297050187857146647225221477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198033458571431098150147651 297050187857146647225221477)
          ·
            refine ⟨55696910223214996354729027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 297050187857146647225221477 55696910223214996354729027)
            ·
              refine ⟨83545365334822494532093541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55696910223214996354729027 83545365334822494532093541)
              ·
                refine ⟨15664756000279217724767539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83545365334822494532093541 15664756000279217724767539)
                ·
                  refine ⟨23497134000418826587151309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15664756000279217724767539 23497134000418826587151309)
                  ·
                    refine ⟨8811425250157059970181741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23497134000418826587151309 8811425250157059970181741)
                    ·
                      refine ⟨3304284468808897488818153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8811425250157059970181741 3304284468808897488818153)
                      ·
                        rfl

theorem cell23_6435071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_6435071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435071 prefixEnd_6435071 := by exact prefixLift 6435071
  have htrace : WordTrace (prefixWord ++ tailWord_6435071) baseStart_6435071 baseEnd_6435071 := by
    simpa [prefixWord, tailWord_6435071, baseEnd_6435071] using wordTrace_append hprefix tailTrace_6435071
  have hstable : (prefixWord ++ tailWord_6435071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435071).length < 2 ^ (prefixWord ++ tailWord_6435071).sum := by decide
  have hdescent : baseEnd_6435071 < baseStart_6435071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435102 : List Nat := [4, 3, 2, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_6435102 : Nat := 118140960795 + 6435102 * 2 ^ 59
def prefixEnd_6435102 : Nat := 4983230072969 + 3 ^ 40 * 6435102 * 2
def baseEnd_6435102 : Nat := 3304300386709186867530511

theorem tailTrace_6435102 : CollatzResearch.WordTrace tailWord_6435102 prefixEnd_6435102 3304300386709186867530511 := by
  unfold tailWord_6435102
  simp only [CollatzResearch.WordTrace]
  refine ⟨29338431491591494596078445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156471634621821304512418373 29338431491591494596078445)
  ·
    refine ⟨11001911809346810473529417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29338431491591494596078445 11001911809346810473529417)
    ·
      refine ⟨8251433857010107855147063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11001911809346810473529417 8251433857010107855147063)
      ·
        refine ⟨12377150785515161782720595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8251433857010107855147063 12377150785515161782720595)
        ·
          refine ⟨18565726178272742674080893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12377150785515161782720595 18565726178272742674080893)
          ·
            refine ⟨6962147316852278502780335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18565726178272742674080893 6962147316852278502780335)
            ·
              refine ⟨10443220975278417754170503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962147316852278502780335 10443220975278417754170503)
              ·
                refine ⟨15664831462917626631255755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10443220975278417754170503 15664831462917626631255755)
                ·
                  refine ⟨23497247194376439946883633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15664831462917626631255755 23497247194376439946883633)
                  ·
                    refine ⟨17622935395782329960162725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23497247194376439946883633 17622935395782329960162725)
                    ·
                      refine ⟨3304300386709186867530511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17622935395782329960162725 3304300386709186867530511)
                      ·
                        rfl

theorem cell23_6435102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_6435102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435102 prefixEnd_6435102 := by exact prefixLift 6435102
  have htrace : WordTrace (prefixWord ++ tailWord_6435102) baseStart_6435102 baseEnd_6435102 := by
    simpa [prefixWord, tailWord_6435102, baseEnd_6435102] using wordTrace_append hprefix tailTrace_6435102
  have hstable : (prefixWord ++ tailWord_6435102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435102).length < 2 ^ (prefixWord ++ tailWord_6435102).sum := by decide
  have hdescent : baseEnd_6435102 < baseStart_6435102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435128 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 1, 4, 2]
def baseStart_6435128 : Nat := 118140960795 + 6435128 * 2 ^ 59
def prefixEnd_6435128 : Nat := 4983230072969 + 3 ^ 40 * 6435128 * 2
def baseEnd_6435128 : Nat := 3304313737206203765805391

theorem tailTrace_6435128 : CollatzResearch.WordTrace tailWord_6435128 prefixEnd_6435128 3304313737206203765805391 := by
  unfold tailWord_6435128
  simp only [CollatzResearch.WordTrace]
  refine ⟨117354200115318881604537019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156472266820425175472716025 117354200115318881604537019)
  ·
    refine ⟨176031300172978322406805529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117354200115318881604537019 176031300172978322406805529)
    ·
      refine ⟨132023475129733741805104147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176031300172978322406805529 132023475129733741805104147)
      ·
        refine ⟨198035212694600612707656221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132023475129733741805104147 198035212694600612707656221)
        ·
          refine ⟨74263204760475229765371083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 198035212694600612707656221 74263204760475229765371083)
          ·
            refine ⟨111394807140712844648056625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74263204760475229765371083 111394807140712844648056625)
            ·
              refine ⟨83546105355534633486042469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111394807140712844648056625 83546105355534633486042469)
              ·
                refine ⟨15664894754162743778632963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83546105355534633486042469 15664894754162743778632963)
                ·
                  refine ⟨23497342131244115667949445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15664894754162743778632963 23497342131244115667949445)
                  ·
                    refine ⟨4405751649608271687740521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23497342131244115667949445 4405751649608271687740521)
                    ·
                      refine ⟨3304313737206203765805391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405751649608271687740521 3304313737206203765805391)
                      ·
                        rfl

theorem cell23_6435128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 1, 4, 2].length) (baseStart_6435128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435128 prefixEnd_6435128 := by exact prefixLift 6435128
  have htrace : WordTrace (prefixWord ++ tailWord_6435128) baseStart_6435128 baseEnd_6435128 := by
    simpa [prefixWord, tailWord_6435128, baseEnd_6435128] using wordTrace_append hprefix tailTrace_6435128
  have hstable : (prefixWord ++ tailWord_6435128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435128).length < 2 ^ (prefixWord ++ tailWord_6435128).sum := by decide
  have hdescent : baseEnd_6435128 < baseStart_6435128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435145 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 2, 2, 2]
def baseStart_6435145 : Nat := 118140960795 + 6435145 * 2 ^ 59
def prefixEnd_6435145 : Nat := 4983230072969 + 3 ^ 40 * 6435145 * 2
def baseEnd_6435145 : Nat := 3304322466377330199292813

theorem tailTrace_6435145 : CollatzResearch.WordTrace tailWord_6435145 prefixEnd_6435145 3304322466377330199292813 := by
  unfold tailWord_6435145
  simp only [CollatzResearch.WordTrace]
  refine ⟨234709020271576175112442889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156472680181050783408295259 234709020271576175112442889)
  ·
    refine ⟨176031765203682131334332167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234709020271576175112442889 176031765203682131334332167)
    ·
      refine ⟨264047647805523197001498251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176031765203682131334332167 264047647805523197001498251)
      ·
        refine ⟨396071471708284795502247377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264047647805523197001498251 396071471708284795502247377)
        ·
          refine ⟨297053603781213596626685533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396071471708284795502247377 297053603781213596626685533)
          ·
            refine ⟨111395101417955098735007075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297053603781213596626685533 111395101417955098735007075)
            ·
              refine ⟨167092652126932648102510613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111395101417955098735007075 167092652126932648102510613)
              ·
                refine ⟨7832468068449967879805185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167092652126932648102510613 7832468068449967879805185)
                ·
                  refine ⟨5874351051337475909853889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7832468068449967879805185 5874351051337475909853889)
                  ·
                    refine ⟨4405763288503106932390417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5874351051337475909853889 4405763288503106932390417)
                    ·
                      refine ⟨3304322466377330199292813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405763288503106932390417 3304322466377330199292813)
                      ·
                        rfl

theorem cell23_6435145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 2, 2].length) (baseStart_6435145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435145 prefixEnd_6435145 := by exact prefixLift 6435145
  have htrace : WordTrace (prefixWord ++ tailWord_6435145) baseStart_6435145 baseEnd_6435145 := by
    simpa [prefixWord, tailWord_6435145, baseEnd_6435145] using wordTrace_append hprefix tailTrace_6435145
  have hstable : (prefixWord ++ tailWord_6435145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435145).length < 2 ^ (prefixWord ++ tailWord_6435145).sum := by decide
  have hdescent : baseEnd_6435145 < baseStart_6435145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435161 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 1, 5, 3]
def baseStart_6435161 : Nat := 118140960795 + 6435161 * 2 ^ 59
def prefixEnd_6435161 : Nat := 4983230072969 + 3 ^ 40 * 6435161 * 2
def baseEnd_6435161 : Nat := 3304330682067802136692739

theorem tailTrace_6435161 : CollatzResearch.WordTrace tailWord_6435161 prefixEnd_6435161 3304330682067802136692739 := by
  unfold tailWord_6435161
  simp only [CollatzResearch.WordTrace]
  refine ⟨234709603839518209845025337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156473069226345473230016891 234709603839518209845025337)
  ·
    refine ⟨176032202879638657383769003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234709603839518209845025337 176032202879638657383769003)
    ·
      refine ⟨264048304319457986075653505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176032202879638657383769003 264048304319457986075653505)
      ·
        refine ⟨198036228239593489556740129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264048304319457986075653505 198036228239593489556740129)
        ·
          refine ⟨148527171179695117167555097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198036228239593489556740129 148527171179695117167555097)
          ·
            refine ⟨111395378384771337875666323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148527171179695117167555097 111395378384771337875666323)
            ·
              refine ⟨167093067577157006813499485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111395378384771337875666323 167093067577157006813499485)
              ·
                refine ⟨62659900341433877555062307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 167093067577157006813499485 62659900341433877555062307)
                ·
                  refine ⟨93989850512150816332593461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62659900341433877555062307 93989850512150816332593461)
                  ·
                    refine ⟨8811548485514139031180637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93989850512150816332593461 8811548485514139031180637)
                    ·
                      refine ⟨3304330682067802136692739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8811548485514139031180637 3304330682067802136692739)
                      ·
                        rfl

theorem cell23_6435161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_6435161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435161 prefixEnd_6435161 := by exact prefixLift 6435161
  have htrace : WordTrace (prefixWord ++ tailWord_6435161) baseStart_6435161 baseEnd_6435161 := by
    simpa [prefixWord, tailWord_6435161, baseEnd_6435161] using wordTrace_append hprefix tailTrace_6435161
  have hstable : (prefixWord ++ tailWord_6435161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435161).length < 2 ^ (prefixWord ++ tailWord_6435161).sum := by decide
  have hdescent : baseEnd_6435161 < baseStart_6435161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435235 : List Nat := [1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 4]
def baseStart_6435235 : Nat := 118140960795 + 6435235 * 2 ^ 59
def prefixEnd_6435235 : Nat := 4983230072969 + 3 ^ 40 * 6435235 * 2
def baseEnd_6435235 : Nat := 3304368679636234847167399

theorem tailTrace_6435235 : CollatzResearch.WordTrace tailWord_6435235 prefixEnd_6435235 3304368679636234847167399 := by
  unfold tailWord_6435235
  simp only [CollatzResearch.WordTrace]
  refine ⟨234712302841250120483219159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156474868560833413655479439 234712302841250120483219159)
  ·
    refine ⟨352068454261875180724828739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234712302841250120483219159 352068454261875180724828739)
    ·
      refine ⟨528102681392812771087243109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352068454261875180724828739 528102681392812771087243109)
      ·
        refine ⟨99019252761152394578858083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 528102681392812771087243109 99019252761152394578858083)
        ·
          refine ⟨148528879141728591868287125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99019252761152394578858083 148528879141728591868287125)
          ·
            refine ⟨6962291209768527743825959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 148528879141728591868287125 6962291209768527743825959)
            ·
              refine ⟨10443436814652791615738939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962291209768527743825959 10443436814652791615738939)
              ·
                refine ⟨15665155221979187423608409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10443436814652791615738939 15665155221979187423608409)
                ·
                  refine ⟨11748866416484390567706307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15665155221979187423608409 11748866416484390567706307)
                  ·
                    refine ⟨17623299624726585851559461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11748866416484390567706307 17623299624726585851559461)
                    ·
                      refine ⟨3304368679636234847167399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17623299624726585851559461 3304368679636234847167399)
                      ·
                        rfl

theorem cell23_6435235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_6435235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435235 prefixEnd_6435235 := by exact prefixLift 6435235
  have htrace : WordTrace (prefixWord ++ tailWord_6435235) baseStart_6435235 baseEnd_6435235 := by
    simpa [prefixWord, tailWord_6435235, baseEnd_6435235] using wordTrace_append hprefix tailTrace_6435235
  have hstable : (prefixWord ++ tailWord_6435235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435235).length < 2 ^ (prefixWord ++ tailWord_6435235).sum := by decide
  have hdescent : baseEnd_6435235 < baseStart_6435235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435262 : List Nat := [4, 2, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_6435262 : Nat := 118140960795 + 6435262 * 2 ^ 59
def prefixEnd_6435262 : Nat := 4983230072969 + 3 ^ 40 * 6435262 * 2
def baseEnd_6435262 : Nat := 1101460847871302080509925

theorem tailTrace_6435262 : CollatzResearch.WordTrace tailWord_6435262 prefixEnd_6435262 1101460847871302080509925 := by
  unfold tailWord_6435262
  simp only [CollatzResearch.WordTrace]
  refine ⟨29339160951519038011806505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156475525074768202729634693 29339160951519038011806505)
  ·
    refine ⟨22004370713639278508854879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29339160951519038011806505 22004370713639278508854879)
    ·
      refine ⟨33006556070458917763282319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22004370713639278508854879 33006556070458917763282319)
      ·
        refine ⟨49509834105688376644923479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33006556070458917763282319 49509834105688376644923479)
        ·
          refine ⟨74264751158532564967385219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49509834105688376644923479 74264751158532564967385219)
          ·
            refine ⟨111397126737798847451077829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74264751158532564967385219 111397126737798847451077829)
            ·
              refine ⟨20886961263337283897077093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111397126737798847451077829 20886961263337283897077093)
              ·
                refine ⟨3916305236875740730701955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20886961263337283897077093 3916305236875740730701955)
                ·
                  refine ⟨5874457855313611096052933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916305236875740730701955 5874457855313611096052933)
                  ·
                    refine ⟨1101460847871302080509925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5874457855313611096052933 1101460847871302080509925)
                    ·
                      rfl

theorem cell23_6435262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_6435262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435262 prefixEnd_6435262 := by exact prefixLift 6435262
  have htrace : WordTrace (prefixWord ++ tailWord_6435262) baseStart_6435262 baseEnd_6435262 := by
    simpa [prefixWord, tailWord_6435262, baseEnd_6435262] using wordTrace_append hprefix tailTrace_6435262
  have hstable : (prefixWord ++ tailWord_6435262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435262).length < 2 ^ (prefixWord ++ tailWord_6435262).sum := by decide
  have hdescent : baseEnd_6435262 < baseStart_6435262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435281 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_6435281 : Nat := 118140960795 + 6435281 * 2 ^ 59
def prefixEnd_6435281 : Nat := 4983230072969 + 3 ^ 40 * 6435281 * 2
def baseEnd_6435281 : Nat := 3304392299746341667192187

theorem tailTrace_6435281 : CollatzResearch.WordTrace tailWord_6435281 prefixEnd_6435281 3304392299746341667192187 := by
  unfold tailWord_6435281
  simp only [CollatzResearch.WordTrace]
  refine ⟨234713980599083470339393697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156475987066055646892929131 234713980599083470339393697)
  ·
    refine ⟨176035485449312602754545273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234713980599083470339393697 176035485449312602754545273)
    ·
      refine ⟨132026614086984452065908955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176035485449312602754545273 132026614086984452065908955)
      ·
        refine ⟨198039921130476678098863433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132026614086984452065908955 198039921130476678098863433)
        ·
          refine ⟨148529940847857508574147575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198039921130476678098863433 148529940847857508574147575)
          ·
            refine ⟨222794911271786262861221363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148529940847857508574147575 222794911271786262861221363)
            ·
              refine ⟨334192366907679394291832045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222794911271786262861221363 334192366907679394291832045)
              ·
                refine ⟨125322137590379772859437017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334192366907679394291832045 125322137590379772859437017)
                ·
                  refine ⟨93991603192784829644577763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125322137590379772859437017 93991603192784829644577763)
                  ·
                    refine ⟨140987404789177244466866645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93991603192784829644577763 140987404789177244466866645)
                    ·
                      refine ⟨3304392299746341667192187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140987404789177244466866645 3304392299746341667192187)
                      ·
                        rfl

theorem cell23_6435281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_6435281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435281 prefixEnd_6435281 := by exact prefixLift 6435281
  have htrace : WordTrace (prefixWord ++ tailWord_6435281) baseStart_6435281 baseEnd_6435281 := by
    simpa [prefixWord, tailWord_6435281, baseEnd_6435281] using wordTrace_append hprefix tailTrace_6435281
  have hstable : (prefixWord ++ tailWord_6435281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435281).length < 2 ^ (prefixWord ++ tailWord_6435281).sum := by decide
  have hdescent : baseEnd_6435281 < baseStart_6435281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435295 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 1, 5, 2]
def baseStart_6435295 : Nat := 118140960795 + 6435295 * 2 ^ 59
def prefixEnd_6435295 : Nat := 4983230072969 + 3 ^ 40 * 6435295 * 2
def baseEnd_6435295 : Nat := 3304399488475504612417123

theorem tailTrace_6435295 : CollatzResearch.WordTrace tailWord_6435295 prefixEnd_6435295 3304399488475504612417123 := by
  unfold tailWord_6435295
  simp only [CollatzResearch.WordTrace]
  refine ⟨234714491221032750730403339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156476327480688500486935559 234714491221032750730403339)
  ·
    refine ⟨352071736831549126095605009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234714491221032750730403339 352071736831549126095605009)
    ·
      refine ⟨264053802623661844571703757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352071736831549126095605009 264053802623661844571703757)
      ·
        refine ⟨99020175983873191714388909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264053802623661844571703757 99020175983873191714388909)
        ·
          refine ⟨37132565993952446892895841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99020175983873191714388909 37132565993952446892895841)
          ·
            refine ⟨27849424495464335169671881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37132565993952446892895841 27849424495464335169671881)
            ·
              refine ⟨20887068371598251377253911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27849424495464335169671881 20887068371598251377253911)
              ·
                refine ⟨31330602557397377065880867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20887068371598251377253911 31330602557397377065880867)
                ·
                  refine ⟨46995903836096065598821301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31330602557397377065880867 46995903836096065598821301)
                  ·
                    refine ⟨4405865984634006149889497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46995903836096065598821301 4405865984634006149889497)
                    ·
                      refine ⟨3304399488475504612417123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405865984634006149889497 3304399488475504612417123)
                      ·
                        rfl

theorem cell23_6435295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 5, 2].length) (baseStart_6435295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435295 prefixEnd_6435295 := by exact prefixLift 6435295
  have htrace : WordTrace (prefixWord ++ tailWord_6435295) baseStart_6435295 baseEnd_6435295 := by
    simpa [prefixWord, tailWord_6435295, baseEnd_6435295] using wordTrace_append hprefix tailTrace_6435295
  have hstable : (prefixWord ++ tailWord_6435295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435295).length < 2 ^ (prefixWord ++ tailWord_6435295).sum := by decide
  have hdescent : baseEnd_6435295 < baseStart_6435295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435338 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_6435338 : Nat := 118140960795 + 6435338 * 2 ^ 59
def prefixEnd_6435338 : Nat := 4983230072969 + 3 ^ 40 * 6435338 * 2
def baseEnd_6435338 : Nat := 3304421568143647944179425

theorem tailTrace_6435338 : CollatzResearch.WordTrace tailWord_6435338 prefixEnd_6435338 3304421568143647944179425 := by
  unfold tailWord_6435338
  simp only [CollatzResearch.WordTrace]
  refine ⟨58679014889969242268554667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156477373039917979382812445 58679014889969242268554667)
  ·
    refine ⟨88018522334953863402832001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58679014889969242268554667 88018522334953863402832001)
    ·
      refine ⟨66013891751215397552124001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88018522334953863402832001 66013891751215397552124001)
      ·
        refine ⟨49510418813411548164093001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66013891751215397552124001 49510418813411548164093001)
        ·
          refine ⟨37132814110058661123069751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49510418813411548164093001 37132814110058661123069751)
          ·
            refine ⟨55699221165087991684604627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37132814110058661123069751 55699221165087991684604627)
            ·
              refine ⟨83548831747631987526906941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55699221165087991684604627 83548831747631987526906941)
              ·
                refine ⟨31330811905361995322590103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83548831747631987526906941 31330811905361995322590103)
                ·
                  refine ⟨46996217858042992983885155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31330811905361995322590103 46996217858042992983885155)
                  ·
                    refine ⟨70494326787064489475827733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46996217858042992983885155 70494326787064489475827733)
                    ·
                      refine ⟨3304421568143647944179425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70494326787064489475827733 3304421568143647944179425)
                      ·
                        rfl

theorem cell23_6435338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_6435338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435338 prefixEnd_6435338 := by exact prefixLift 6435338
  have htrace : WordTrace (prefixWord ++ tailWord_6435338) baseStart_6435338 baseEnd_6435338 := by
    simpa [prefixWord, tailWord_6435338, baseEnd_6435338] using wordTrace_append hprefix tailTrace_6435338
  have hstable : (prefixWord ++ tailWord_6435338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435338).length < 2 ^ (prefixWord ++ tailWord_6435338).sum := by decide
  have hdescent : baseEnd_6435338 < baseStart_6435338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435342 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_6435342 : Nat := 118140960795 + 6435342 * 2 ^ 59
def prefixEnd_6435342 : Nat := 4983230072969 + 3 ^ 40 * 6435342 * 2
def baseEnd_6435342 : Nat := 3304423622066265928529407

theorem tailTrace_6435342 : CollatzResearch.WordTrace tailWord_6435342 prefixEnd_6435342 3304423622066265928529407 := by
  unfold tailWord_6435342
  simp only [CollatzResearch.WordTrace]
  refine ⟨29339525681482809719670535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156477470301241651838242853 29339525681482809719670535)
  ·
    refine ⟨44009288522224214579505803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29339525681482809719670535 44009288522224214579505803)
    ·
      refine ⟨66013932783336321869258705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44009288522224214579505803 66013932783336321869258705)
      ·
        refine ⟨49510449587502241401944029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66013932783336321869258705 49510449587502241401944029)
        ·
          refine ⟨18566418595313340525729011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49510449587502241401944029 18566418595313340525729011)
          ·
            refine ⟨27849627892970010788593517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18566418595313340525729011 27849627892970010788593517)
            ·
              refine ⟨10443610459863754045722569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27849627892970010788593517 10443610459863754045722569)
              ·
                refine ⟨7832707844897815534291927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10443610459863754045722569 7832707844897815534291927)
                ·
                  refine ⟨11749061767346723301437891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7832707844897815534291927 11749061767346723301437891)
                  ·
                    refine ⟨17623592651020084952156837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11749061767346723301437891 17623592651020084952156837)
                    ·
                      refine ⟨3304423622066265928529407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17623592651020084952156837 3304423622066265928529407)
                      ·
                        rfl

theorem cell23_6435342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_6435342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435342 prefixEnd_6435342 := by exact prefixLift 6435342
  have htrace : WordTrace (prefixWord ++ tailWord_6435342) baseStart_6435342 baseEnd_6435342 := by
    simpa [prefixWord, tailWord_6435342, baseEnd_6435342] using wordTrace_append hprefix tailTrace_6435342
  have hstable : (prefixWord ++ tailWord_6435342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435342).length < 2 ^ (prefixWord ++ tailWord_6435342).sum := by decide
  have hdescent : baseEnd_6435342 < baseStart_6435342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435345 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 3]
def baseStart_6435345 : Nat := 118140960795 + 6435345 * 2 ^ 59
def prefixEnd_6435345 : Nat := 4983230072969 + 3 ^ 40 * 6435345 * 2
def baseEnd_6435345 : Nat := 3304425162508229416791893

theorem tailTrace_6435345 : CollatzResearch.WordTrace tailWord_6435345 prefixEnd_6435345 3304425162508229416791893 := by
  unfold tailWord_6435345
  simp only [CollatzResearch.WordTrace]
  refine ⟨234716314870851609269723489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156477543247234406179815659 234716314870851609269723489)
  ·
    refine ⟨176037236153138706952292617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234716314870851609269723489 176037236153138706952292617)
    ·
      refine ⟨132027927114854030214219463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 176037236153138706952292617 132027927114854030214219463)
      ·
        refine ⟨198041890672281045321329195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132027927114854030214219463 198041890672281045321329195)
        ·
          refine ⟨297062836008421567981993793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198041890672281045321329195 297062836008421567981993793)
          ·
            refine ⟨222797127006316175986495345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297062836008421567981993793 222797127006316175986495345)
            ·
              refine ⟨167097845254737131989871509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222797127006316175986495345 167097845254737131989871509)
              ·
                refine ⟨7832711496315803062025227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 167097845254737131989871509 7832711496315803062025227)
                ·
                  refine ⟨11749067244473704593037841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7832711496315803062025227 11749067244473704593037841)
                  ·
                    refine ⟨8811800433355278444778381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11749067244473704593037841 8811800433355278444778381)
                    ·
                      refine ⟨3304425162508229416791893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8811800433355278444778381 3304425162508229416791893)
                      ·
                        rfl

theorem cell23_6435345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 3].length) (baseStart_6435345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435345 prefixEnd_6435345 := by exact prefixLift 6435345
  have htrace : WordTrace (prefixWord ++ tailWord_6435345) baseStart_6435345 baseEnd_6435345 := by
    simpa [prefixWord, tailWord_6435345, baseEnd_6435345] using wordTrace_append hprefix tailTrace_6435345
  have hstable : (prefixWord ++ tailWord_6435345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435345).length < 2 ^ (prefixWord ++ tailWord_6435345).sum := by decide
  have hdescent : baseEnd_6435345 < baseStart_6435345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435359 : List Nat := [1, 1, 2, 4, 1, 1, 1, 7, 1, 2, 2]
def baseStart_6435359 : Nat := 118140960795 + 6435359 * 2 ^ 59
def prefixEnd_6435359 : Nat := 4983230072969 + 3 ^ 40 * 6435359 * 2
def baseEnd_6435359 : Nat := 3304432351237392362016829

theorem tailTrace_6435359 : CollatzResearch.WordTrace tailWord_6435359 prefixEnd_6435359 3304432351237392362016829 := by
  unfold tailWord_6435359
  simp only [CollatzResearch.WordTrace]
  refine ⟨234716825492800889660733131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156477883661867259773822087 234716825492800889660733131)
  ·
    refine ⟨352075238239201334491099697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234716825492800889660733131 352075238239201334491099697)
    ·
      refine ⟨264056428679401000868324773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 352075238239201334491099697 264056428679401000868324773)
      ·
        refine ⟨49510580377387687662810895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264056428679401000868324773 49510580377387687662810895)
        ·
          refine ⟨74265870566081531494216343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49510580377387687662810895 74265870566081531494216343)
          ·
            refine ⟨111398805849122297241324515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74265870566081531494216343 111398805849122297241324515)
            ·
              refine ⟨167098208773683445861986773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111398805849122297241324515 167098208773683445861986773)
              ·
                refine ⟨3916364268133205762390315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 167098208773683445861986773 3916364268133205762390315)
                ·
                  refine ⟨5874546402199808643585473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916364268133205762390315 5874546402199808643585473)
                  ·
                    refine ⟨4405909801649856482689105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5874546402199808643585473 4405909801649856482689105)
                    ·
                      refine ⟨3304432351237392362016829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405909801649856482689105 3304432351237392362016829)
                      ·
                        rfl

theorem cell23_6435359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 1, 2, 2].length) (baseStart_6435359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435359 prefixEnd_6435359 := by exact prefixLift 6435359
  have htrace : WordTrace (prefixWord ++ tailWord_6435359) baseStart_6435359 baseEnd_6435359 := by
    simpa [prefixWord, tailWord_6435359, baseEnd_6435359] using wordTrace_append hprefix tailTrace_6435359
  have hstable : (prefixWord ++ tailWord_6435359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435359).length < 2 ^ (prefixWord ++ tailWord_6435359).sum := by decide
  have hdescent : baseEnd_6435359 < baseStart_6435359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435376 : List Nat := [2, 1, 1, 1, 2, 3, 6, 2, 1, 2, 2]
def baseStart_6435376 : Nat := 118140960795 + 6435376 * 2 ^ 59
def prefixEnd_6435376 : Nat := 4983230072969 + 3 ^ 40 * 6435376 * 2
def baseEnd_6435376 : Nat := 3304441080408518795504251

theorem tailTrace_6435376 : CollatzResearch.WordTrace tailWord_6435376 prefixEnd_6435376 3304441080408518795504251 := by
  unfold tailWord_6435376
  simp only [CollatzResearch.WordTrace]
  refine ⟨117358722766869650782050991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156478297022492867709401321 117358722766869650782050991)
  ·
    refine ⟨176038084150304476173076487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117358722766869650782050991 176038084150304476173076487)
    ·
      refine ⟨264057126225456714259614731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176038084150304476173076487 264057126225456714259614731)
      ·
        refine ⟨396085689338185071389422097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264057126225456714259614731 396085689338185071389422097)
        ·
          refine ⟨297064267003638803542066573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396085689338185071389422097 297064267003638803542066573)
          ·
            refine ⟨111399100126364551328274965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297064267003638803542066573 111399100126364551328274965)
            ·
              refine ⟨5221832818423338343512889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111399100126364551328274965 5221832818423338343512889)
              ·
                refine ⟨3916374613817503757634667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5221832818423338343512889 3916374613817503757634667)
                ·
                  refine ⟨5874561920726255636452001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916374613817503757634667 5874561920726255636452001)
                  ·
                    refine ⟨4405921440544691727339001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5874561920726255636452001 4405921440544691727339001)
                    ·
                      refine ⟨3304441080408518795504251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405921440544691727339001 3304441080408518795504251)
                      ·
                        rfl

theorem cell23_6435376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 1, 2, 2].length) (baseStart_6435376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435376 prefixEnd_6435376 := by exact prefixLift 6435376
  have htrace : WordTrace (prefixWord ++ tailWord_6435376) baseStart_6435376 baseEnd_6435376 := by
    simpa [prefixWord, tailWord_6435376, baseEnd_6435376] using wordTrace_append hprefix tailTrace_6435376
  have hstable : (prefixWord ++ tailWord_6435376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435376).length < 2 ^ (prefixWord ++ tailWord_6435376).sum := by decide
  have hdescent : baseEnd_6435376 < baseStart_6435376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435378 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_6435378 : Nat := 118140960795 + 6435378 * 2 ^ 59
def prefixEnd_6435378 : Nat := 4983230072969 + 3 ^ 40 * 6435378 * 2
def baseEnd_6435378 : Nat := 1101480702456609262559747

theorem tailTrace_6435378 : CollatzResearch.WordTrace tailWord_6435378 prefixEnd_6435378 1101480702456609262559747 := by
  unfold tailWord_6435378
  simp only [CollatzResearch.WordTrace]
  refine ⟨58679379619933013976418697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156478345653154703937116525 58679379619933013976418697)
  ·
    refine ⟨44009534714949760482314023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58679379619933013976418697 44009534714949760482314023)
    ·
      refine ⟨66014302072424640723471035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44009534714949760482314023 66014302072424640723471035)
      ·
        refine ⟨99021453108636961085206553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66014302072424640723471035 99021453108636961085206553)
        ·
          refine ⟨74266089831477720813904915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99021453108636961085206553 74266089831477720813904915)
          ·
            refine ⟨111399134747216581220857373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74266089831477720813904915 111399134747216581220857373)
            ·
              refine ⟨41774675530206217957821515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111399134747216581220857373 41774675530206217957821515)
              ·
                refine ⟨62662013295309326936732273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41774675530206217957821515 62662013295309326936732273)
                ·
                  refine ⟨46996509971481995202549205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62662013295309326936732273 46996509971481995202549205)
                  ·
                    refine ⟨1101480702456609262559747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46996509971481995202549205 1101480702456609262559747)
                    ·
                      rfl

theorem cell23_6435378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_6435378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435378 prefixEnd_6435378 := by exact prefixLift 6435378
  have htrace : WordTrace (prefixWord ++ tailWord_6435378) baseStart_6435378 baseEnd_6435378 := by
    simpa [prefixWord, tailWord_6435378, baseEnd_6435378] using wordTrace_append hprefix tailTrace_6435378
  have hstable : (prefixWord ++ tailWord_6435378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435378).length < 2 ^ (prefixWord ++ tailWord_6435378).sum := by decide
  have hdescent : baseEnd_6435378 < baseStart_6435378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435382 : List Nat := [5, 1, 2, 1, 2, 3, 1, 8]
def baseStart_6435382 : Nat := 118140960795 + 6435382 * 2 ^ 59
def prefixEnd_6435382 : Nat := 4983230072969 + 3 ^ 40 * 6435382 * 2
def baseEnd_6435382 : Nat := 122386820788609102667749

theorem tailTrace_6435382 : CollatzResearch.WordTrace tailWord_6435382 prefixEnd_6435382 122386820788609102667749 := by
  unfold tailWord_6435382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14669854023232347786801275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156478442914478376392546933 14669854023232347786801275)
  ·
    refine ⟨22004781034848521680201913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14669854023232347786801275 22004781034848521680201913)
    ·
      refine ⟨16503585776136391260151435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22004781034848521680201913 16503585776136391260151435)
      ·
        refine ⟨24755378664204586890227153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16503585776136391260151435 24755378664204586890227153)
        ·
          refine ⟨18566533998153440167670365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24755378664204586890227153 18566533998153440167670365)
          ·
            refine ⟨6962450249307540062876387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18566533998153440167670365 6962450249307540062876387)
            ·
              refine ⟨10443675373961310094314581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962450249307540062876387 10443675373961310094314581)
              ·
                refine ⟨122386820788609102667749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10443675373961310094314581 122386820788609102667749)
                ·
                  rfl

theorem cell23_6435382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_6435382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435382 prefixEnd_6435382 := by exact prefixLift 6435382
  have htrace : WordTrace (prefixWord ++ tailWord_6435382) baseStart_6435382 baseEnd_6435382 := by
    simpa [prefixWord, tailWord_6435382, baseEnd_6435382] using wordTrace_append hprefix tailTrace_6435382
  have hstable : (prefixWord ++ tailWord_6435382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435382).length < 2 ^ (prefixWord ++ tailWord_6435382).sum := by decide
  have hdescent : baseEnd_6435382 < baseStart_6435382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435392 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 2, 1, 3]
def baseStart_6435392 : Nat := 118140960795 + 6435392 * 2 ^ 59
def prefixEnd_6435392 : Nat := 4983230072969 + 3 ^ 40 * 6435392 * 2
def baseEnd_6435392 : Nat := 3304449296098990732904177

theorem tailTrace_6435392 : CollatzResearch.WordTrace tailWord_6435392 prefixEnd_6435392 3304449296098990732904177 := by
  unfold tailWord_6435392
  simp only [CollatzResearch.WordTrace]
  refine ⟨117359014550840668148342215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156478686067787557531122953 117359014550840668148342215)
  ·
    refine ⟨176038521826261002222513323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117359014550840668148342215 176038521826261002222513323)
    ·
      refine ⟨264057782739391503333769985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176038521826261002222513323 264057782739391503333769985)
      ·
        refine ⟨198043337054543627500327489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 264057782739391503333769985 198043337054543627500327489)
        ·
          refine ⟨148532502790907720625245617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 198043337054543627500327489 148532502790907720625245617)
          ·
            refine ⟨111399377093180790468934213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148532502790907720625245617 111399377093180790468934213)
            ·
              refine ⟨20887383204971398212925165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111399377093180790468934213 20887383204971398212925165)
              ·
                refine ⟨7832768701864274329846937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20887383204971398212925165 7832768701864274329846937)
                ·
                  refine ⟨5874576526398205747385203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7832768701864274329846937 5874576526398205747385203)
                  ·
                    refine ⟨8811864789597308621077805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5874576526398205747385203 8811864789597308621077805)
                    ·
                      refine ⟨3304449296098990732904177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8811864789597308621077805 3304449296098990732904177)
                      ·
                        rfl

theorem cell23_6435392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2, 1, 3].length) (baseStart_6435392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435392 prefixEnd_6435392 := by exact prefixLift 6435392
  have htrace : WordTrace (prefixWord ++ tailWord_6435392) baseStart_6435392 baseEnd_6435392 := by
    simpa [prefixWord, tailWord_6435392, baseEnd_6435392] using wordTrace_append hprefix tailTrace_6435392
  have hstable : (prefixWord ++ tailWord_6435392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435392).length < 2 ^ (prefixWord ++ tailWord_6435392).sum := by decide
  have hdescent : baseEnd_6435392 < baseStart_6435392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435402 : List Nat := [3, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2]
def baseStart_6435402 : Nat := 118140960795 + 6435402 * 2 ^ 59
def prefixEnd_6435402 : Nat := 4983230072969 + 3 ^ 40 * 6435402 * 2
def baseEnd_6435402 : Nat := 3304454430905535693779131

theorem tailTrace_6435402 : CollatzResearch.WordTrace tailWord_6435402 prefixEnd_6435402 3304454430905535693779131 := by
  unfold tailWord_6435402
  simp only [CollatzResearch.WordTrace]
  refine ⟨58679598457911277001137115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156478929221096738669698973 58679598457911277001137115)
  ·
    refine ⟨88019397686866915501705673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58679598457911277001137115 88019397686866915501705673)
    ·
      refine ⟨66014548265150186626279255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88019397686866915501705673 66014548265150186626279255)
      ·
        refine ⟨99021822397725279939418883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66014548265150186626279255 99021822397725279939418883)
        ·
          refine ⟨148532733596587919909128325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99021822397725279939418883 148532733596587919909128325)
          ·
            refine ⟨27849887549360234982961561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148532733596587919909128325 27849887549360234982961561)
            ·
              refine ⟨20887415662020176237221171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27849887549360234982961561 20887415662020176237221171)
              ·
                refine ⟨31331123493030264355831757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20887415662020176237221171 31331123493030264355831757)
                ·
                  refine ⟨11749171309886349133436909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31331123493030264355831757 11749171309886349133436909)
                  ·
                    refine ⟨4405939241207380925038841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11749171309886349133436909 4405939241207380925038841)
                    ·
                      refine ⟨3304454430905535693779131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405939241207380925038841 3304454430905535693779131)
                      ·
                        rfl

theorem cell23_6435402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_6435402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435402 prefixEnd_6435402 := by exact prefixLift 6435402
  have htrace : WordTrace (prefixWord ++ tailWord_6435402) baseStart_6435402 baseEnd_6435402 := by
    simpa [prefixWord, tailWord_6435402, baseEnd_6435402] using wordTrace_append hprefix tailTrace_6435402
  have hstable : (prefixWord ++ tailWord_6435402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435402).length < 2 ^ (prefixWord ++ tailWord_6435402).sum := by decide
  have hdescent : baseEnd_6435402 < baseStart_6435402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435426 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6435426 : Nat := 118140960795 + 6435426 * 2 ^ 59
def prefixEnd_6435426 : Nat := 4983230072969 + 3 ^ 40 * 6435426 * 2
def baseEnd_6435426 : Nat := 3304466754441243599879021

theorem tailTrace_6435426 : CollatzResearch.WordTrace tailWord_6435426 prefixEnd_6435426 3304466754441243599879021 := by
  unfold tailWord_6435426
  simp only [CollatzResearch.WordTrace]
  refine ⟨58679817295889540025855533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156479512789038773402281421 58679817295889540025855533)
  ·
    refine ⟨22004931485958577509695825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58679817295889540025855533 22004931485958577509695825)
    ·
      refine ⟨16503698614468933132271869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22004931485958577509695825 16503698614468933132271869)
      ·
        refine ⟨6188886980425849924601951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16503698614468933132271869 6188886980425849924601951)
        ·
          refine ⟨9283330470638774886902927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6188886980425849924601951 9283330470638774886902927)
          ·
            refine ⟨13924995705958162330354391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9283330470638774886902927 13924995705958162330354391)
            ·
              refine ⟨20887493558937243495531587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13924995705958162330354391 20887493558937243495531587)
              ·
                refine ⟨31331240338405865243297381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20887493558937243495531587 31331240338405865243297381)
                ·
                  refine ⟨5874607563451099733118259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31331240338405865243297381 5874607563451099733118259)
                  ·
                    refine ⟨8811911345176649599677389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5874607563451099733118259 8811911345176649599677389)
                    ·
                      refine ⟨3304466754441243599879021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8811911345176649599677389 3304466754441243599879021)
                      ·
                        rfl

theorem cell23_6435426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6435426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435426 prefixEnd_6435426 := by exact prefixLift 6435426
  have htrace : WordTrace (prefixWord ++ tailWord_6435426) baseStart_6435426 baseEnd_6435426 := by
    simpa [prefixWord, tailWord_6435426, baseEnd_6435426] using wordTrace_append hprefix tailTrace_6435426
  have hstable : (prefixWord ++ tailWord_6435426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435426).length < 2 ^ (prefixWord ++ tailWord_6435426).sum := by decide
  have hdescent : baseEnd_6435426 < baseStart_6435426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435449 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 1, 4, 2]
def baseStart_6435449 : Nat := 118140960795 + 6435449 * 2 ^ 59
def prefixEnd_6435449 : Nat := 4983230072969 + 3 ^ 40 * 6435449 * 2
def baseEnd_6435449 : Nat := 3304478564496297009891415

theorem tailTrace_6435449 : CollatzResearch.WordTrace tailWord_6435449 prefixEnd_6435449 3304478564496297009891415 := by
  unfold tailWord_6435449
  simp only [CollatzResearch.WordTrace]
  refine ⟨234720108062474835031509401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156480072041649890021006267 234720108062474835031509401)
  ·
    refine ⟨176040081046856126273632051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234720108062474835031509401 176040081046856126273632051)
    ·
      refine ⟨264060121570284189410448077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176040081046856126273632051 264060121570284189410448077)
      ·
        refine ⟨99022545588856571028918029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 264060121570284189410448077 99022545588856571028918029)
        ·
          refine ⟨37133454595821214135844261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99022545588856571028918029 37133454595821214135844261)
          ·
            refine ⟨6962522736716477650470799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37133454595821214135844261 6962522736716477650470799)
            ·
              refine ⟨10443784105074716475706199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962522736716477650470799 10443784105074716475706199)
              ·
                refine ⟨15665676157612074713559299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10443784105074716475706199 15665676157612074713559299)
                ·
                  refine ⟨23498514236418112070338949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15665676157612074713559299 23498514236418112070338949)
                  ·
                    refine ⟨4405971419328396013188553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23498514236418112070338949 4405971419328396013188553)
                    ·
                      refine ⟨3304478564496297009891415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4405971419328396013188553 3304478564496297009891415)
                      ·
                        rfl

theorem cell23_6435449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_6435449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435449 prefixEnd_6435449 := by exact prefixLift 6435449
  have htrace : WordTrace (prefixWord ++ tailWord_6435449) baseStart_6435449 baseEnd_6435449 := by
    simpa [prefixWord, tailWord_6435449, baseEnd_6435449] using wordTrace_append hprefix tailTrace_6435449
  have hstable : (prefixWord ++ tailWord_6435449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435449).length < 2 ^ (prefixWord ++ tailWord_6435449).sum := by decide
  have hdescent : baseEnd_6435449 < baseStart_6435449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435485 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_6435485 : Nat := 118140960795 + 6435485 * 2 ^ 59
def prefixEnd_6435485 : Nat := 4983230072969 + 3 ^ 40 * 6435485 * 2
def baseEnd_6435485 : Nat := 1101499016599952956347083

theorem tailTrace_6435485 : CollatzResearch.WordTrace tailWord_6435485 prefixEnd_6435485 1101499016599952956347083 := by
  unfold tailWord_6435485
  simp only [CollatzResearch.WordTrace]
  refine ⟨234721421090344413179819909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156480947393562942119879939 234721421090344413179819909)
  ·
    refine ⟨44010266454439577471216233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234721421090344413179819909 44010266454439577471216233)
    ·
      refine ⟨33007699840829683103412175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44010266454439577471216233 33007699840829683103412175)
      ·
        refine ⟨49511549761244524655118263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33007699840829683103412175 49511549761244524655118263)
        ·
          refine ⟨74267324641866786982677395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49511549761244524655118263 74267324641866786982677395)
          ·
            refine ⟨111400986962800180474016093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74267324641866786982677395 111400986962800180474016093)
            ·
              refine ⟨41775370111050067677756035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111400986962800180474016093 41775370111050067677756035)
              ·
                refine ⟨62663055166575101516634053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41775370111050067677756035 62663055166575101516634053)
                ·
                  refine ⟨11749322843732831534368885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62663055166575101516634053 11749322843732831534368885)
                  ·
                    refine ⟨1101499016599952956347083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11749322843732831534368885 1101499016599952956347083)
                    ·
                      rfl

theorem cell23_6435485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_6435485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435485 prefixEnd_6435485 := by exact prefixLift 6435485
  have htrace : WordTrace (prefixWord ++ tailWord_6435485) baseStart_6435485 baseEnd_6435485 := by
    simpa [prefixWord, tailWord_6435485, baseEnd_6435485] using wordTrace_append hprefix tailTrace_6435485
  have hstable : (prefixWord ++ tailWord_6435485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435485).length < 2 ^ (prefixWord ++ tailWord_6435485).sum := by decide
  have hdescent : baseEnd_6435485 < baseStart_6435485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435489 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 7]
def baseStart_6435489 : Nat := 118140960795 + 6435489 * 2 ^ 59
def prefixEnd_6435489 : Nat := 4983230072969 + 3 ^ 40 * 6435489 * 2
def baseEnd_6435489 : Nat := 367166567080275205932359

theorem tailTrace_6435489 : CollatzResearch.WordTrace tailWord_6435489 prefixEnd_6435489 367166567080275205932359 := by
  unfold tailWord_6435489
  simp only [CollatzResearch.WordTrace]
  refine ⟨234721566982329921862965521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156481044654886614575310347 234721566982329921862965521)
  ·
    refine ⟨176041175236747441397224141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234721566982329921862965521 176041175236747441397224141)
    ·
      refine ⟨66015440713780290523959053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176041175236747441397224141 66015440713780290523959053)
      ·
        refine ⟨24755790267667608946484645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66015440713780290523959053 24755790267667608946484645)
        ·
          refine ⟨4641710675187676677465871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24755790267667608946484645 4641710675187676677465871)
          ·
            refine ⟨6962566012781515016198807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4641710675187676677465871 6962566012781515016198807)
            ·
              refine ⟨10443849019172272524298211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962566012781515016198807 10443849019172272524298211)
              ·
                refine ⟨15665773528758408786447317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10443849019172272524298211 15665773528758408786447317)
                ·
                  refine ⟨367166567080275205932359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15665773528758408786447317 367166567080275205932359)
                  ·
                    rfl

theorem cell23_6435489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 7].length) (baseStart_6435489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435489 prefixEnd_6435489 := by exact prefixLift 6435489
  have htrace : WordTrace (prefixWord ++ tailWord_6435489) baseStart_6435489 baseEnd_6435489 := by
    simpa [prefixWord, tailWord_6435489, baseEnd_6435489] using wordTrace_append hprefix tailTrace_6435489
  have hstable : (prefixWord ++ tailWord_6435489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435489).length < 2 ^ (prefixWord ++ tailWord_6435489).sum := by decide
  have hdescent : baseEnd_6435489 < baseStart_6435489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435492 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 2, 5, 2]
def baseStart_6435492 : Nat := 118140960795 + 6435492 * 2 ^ 59
def prefixEnd_6435492 : Nat := 4983230072969 + 3 ^ 40 * 6435492 * 2
def baseEnd_6435492 : Nat := 3304500644164440341653717

theorem tailTrace_6435492 : CollatzResearch.WordTrace tailWord_6435492 prefixEnd_6435492 3304500644164440341653717 := by
  unfold tailWord_6435492
  simp only [CollatzResearch.WordTrace]
  refine ⟨117360838200659526687662365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156481117600879368916883153 117360838200659526687662365)
  ·
    refine ⟨44010314325247322507873387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117360838200659526687662365 44010314325247322507873387)
    ·
      refine ⟨66015471487870983761810081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44010314325247322507873387 66015471487870983761810081)
      ·
        refine ⟨49511603615903237821357561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66015471487870983761810081 49511603615903237821357561)
        ·
          refine ⟨37133702711927428366018171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49511603615903237821357561 37133702711927428366018171)
          ·
            refine ⟨55700554067891142549027257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37133702711927428366018171 55700554067891142549027257)
            ·
              refine ⟨41775415550918356911770443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55700554067891142549027257 41775415550918356911770443)
              ·
                refine ⟨62663123326377535367655665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41775415550918356911770443 62663123326377535367655665)
                ·
                  refine ⟨46997342494783151525741749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62663123326377535367655665 46997342494783151525741749)
                  ·
                    refine ⟨4406000858885920455538289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46997342494783151525741749 4406000858885920455538289)
                    ·
                      refine ⟨3304500644164440341653717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406000858885920455538289 3304500644164440341653717)
                      ·
                        rfl

theorem cell23_6435492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_6435492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435492 prefixEnd_6435492 := by exact prefixLift 6435492
  have htrace : WordTrace (prefixWord ++ tailWord_6435492) baseStart_6435492 baseEnd_6435492 := by
    simpa [prefixWord, tailWord_6435492, baseEnd_6435492] using wordTrace_append hprefix tailTrace_6435492
  have hstable : (prefixWord ++ tailWord_6435492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435492).length < 2 ^ (prefixWord ++ tailWord_6435492).sum := by decide
  have hdescent : baseEnd_6435492 < baseStart_6435492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435585 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_6435585 : Nat := 118140960795 + 6435585 * 2 ^ 59
def prefixEnd_6435585 : Nat := 4983230072969 + 3 ^ 40 * 6435585 * 2
def baseEnd_6435585 : Nat := 3304548397865308477790789

theorem tailTrace_6435585 : CollatzResearch.WordTrace tailWord_6435585 prefixEnd_6435585 3304548397865308477790789 := by
  unfold tailWord_6435585
  simp only [CollatzResearch.WordTrace]
  refine ⟨234725068389982130258460209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156483378926654753505640139 234725068389982130258460209)
  ·
    refine ⟨176043801292486597693845157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234725068389982130258460209 176043801292486597693845157)
    ·
      refine ⟨33008212742341237067595967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 176043801292486597693845157 33008212742341237067595967)
      ·
        refine ⟨49512319113511855601393951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33008212742341237067595967 49512319113511855601393951)
        ·
          refine ⟨74268478670267783402090927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49512319113511855601393951 74268478670267783402090927)
          ·
            refine ⟨111402718005401675103136391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74268478670267783402090927 111402718005401675103136391)
            ·
              refine ⟨167104077008102512654704587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111402718005401675103136391 167104077008102512654704587)
              ·
                refine ⟨250656115512153768982056881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167104077008102512654704587 250656115512153768982056881)
                ·
                  refine ⟨187992086634115326736542661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250656115512153768982056881 187992086634115326736542661)
                  ·
                    refine ⟨35248516243896623763101749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187992086634115326736542661 35248516243896623763101749)
                    ·
                      refine ⟨3304548397865308477790789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35248516243896623763101749 3304548397865308477790789)
                      ·
                        rfl

theorem cell23_6435585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_6435585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435585 prefixEnd_6435585 := by exact prefixLift 6435585
  have htrace : WordTrace (prefixWord ++ tailWord_6435585) baseStart_6435585 baseEnd_6435585 := by
    simpa [prefixWord, tailWord_6435585, baseEnd_6435585] using wordTrace_append hprefix tailTrace_6435585
  have hstable : (prefixWord ++ tailWord_6435585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435585).length < 2 ^ (prefixWord ++ tailWord_6435585).sum := by decide
  have hdescent : baseEnd_6435585 < baseStart_6435585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435625 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 6]
def baseStart_6435625 : Nat := 118140960795 + 6435625 * 2 ^ 59
def prefixEnd_6435625 : Nat := 4983230072969 + 3 ^ 40 * 6435625 * 2
def baseEnd_6435625 : Nat := 3304568937091488321290605

theorem tailTrace_6435625 : CollatzResearch.WordTrace tailWord_6435625 prefixEnd_6435625 3304568937091488321290605 := by
  unfold tailWord_6435625
  simp only [CollatzResearch.WordTrace]
  refine ⟨234726527309837217089916329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156484351539891478059944219 234726527309837217089916329)
  ·
    refine ⟨176044895482377912817437247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234726527309837217089916329 176044895482377912817437247)
    ·
      refine ⟨264067343223566869226155871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176044895482377912817437247 264067343223566869226155871)
      ·
        refine ⟨396101014835350303839233807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264067343223566869226155871 396101014835350303839233807)
        ·
          refine ⟨594151522253025455758850711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396101014835350303839233807 594151522253025455758850711)
          ·
            refine ⟨891227283379538183638276067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594151522253025455758850711 891227283379538183638276067)
            ·
              refine ⟨1336840925069307275457414101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891227283379538183638276067 1336840925069307275457414101)
              ·
                refine ⟨31332209181311889268533143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1336840925069307275457414101 31332209181311889268533143)
                ·
                  refine ⟨46998313771967833902799715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31332209181311889268533143 46998313771967833902799715)
                  ·
                    refine ⟨70497470657951750854199573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46998313771967833902799715 70497470657951750854199573)
                    ·
                      refine ⟨3304568937091488321290605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70497470657951750854199573 3304568937091488321290605)
                      ·
                        rfl

theorem cell23_6435625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_6435625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435625 prefixEnd_6435625 := by exact prefixLift 6435625
  have htrace : WordTrace (prefixWord ++ tailWord_6435625) baseStart_6435625 baseEnd_6435625 := by
    simpa [prefixWord, tailWord_6435625, baseEnd_6435625] using wordTrace_append hprefix tailTrace_6435625
  have hstable : (prefixWord ++ tailWord_6435625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435625).length < 2 ^ (prefixWord ++ tailWord_6435625).sum := by decide
  have hdescent : baseEnd_6435625 < baseStart_6435625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435632 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 3]
def baseStart_6435632 : Nat := 118140960795 + 6435632 * 2 ^ 59
def prefixEnd_6435632 : Nat := 4983230072969 + 3 ^ 40 * 6435632 * 2
def baseEnd_6435632 : Nat := 3304572531456069793903073

theorem tailTrace_6435632 : CollatzResearch.WordTrace tailWord_6435632 prefixEnd_6435632 3304572531456069793903073 := by
  unfold tailWord_6435632
  simp only [CollatzResearch.WordTrace]
  refine ⟨117363391310405928642710575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156484521747207904856947433 117363391310405928642710575)
  ·
    refine ⟨176045086965608892964065863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117363391310405928642710575 176045086965608892964065863)
    ·
      refine ⟨264067630448413339446098795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176045086965608892964065863 264067630448413339446098795)
      ·
        refine ⟨396101445672620009169148193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264067630448413339446098795 396101445672620009169148193)
        ·
          refine ⟨297076084254465006876861145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396101445672620009169148193 297076084254465006876861145)
          ·
            refine ⟨222807063190848755157645859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 297076084254465006876861145 222807063190848755157645859)
            ·
              refine ⟨334210594786273132736468789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222807063190848755157645859 334210594786273132736468789)
              ·
                refine ⟨31332243261213106194043949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 334210594786273132736468789 31332243261213106194043949)
                ·
                  refine ⟨11749591222954914822766481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31332243261213106194043949 11749591222954914822766481)
                  ·
                    refine ⟨8812193417216186117074861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11749591222954914822766481 8812193417216186117074861)
                    ·
                      refine ⟨3304572531456069793903073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8812193417216186117074861 3304572531456069793903073)
                      ·
                        rfl

theorem cell23_6435632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 3].length) (baseStart_6435632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435632 prefixEnd_6435632 := by exact prefixLift 6435632
  have htrace : WordTrace (prefixWord ++ tailWord_6435632) baseStart_6435632 baseEnd_6435632 := by
    simpa [prefixWord, tailWord_6435632, baseEnd_6435632] using wordTrace_append hprefix tailTrace_6435632
  have hstable : (prefixWord ++ tailWord_6435632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435632).length < 2 ^ (prefixWord ++ tailWord_6435632).sum := by decide
  have hdescent : baseEnd_6435632 < baseStart_6435632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435714 : List Nat := [3, 4, 2, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_6435714 : Nat := 118140960795 + 6435714 * 2 ^ 59
def prefixEnd_6435714 : Nat := 4983230072969 + 3 ^ 40 * 6435714 * 2
def baseEnd_6435714 : Nat := 3304614636869738473077697

theorem tailTrace_6435714 : CollatzResearch.WordTrace tailWord_6435714 prefixEnd_6435714 3304614636869738473077697 := by
  unfold tailWord_6435714
  simp only [CollatzResearch.WordTrace]
  refine ⟨58682443351628696322476549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156486515604343190193270797 58682443351628696322476549)
  ·
    refine ⟨11002958128430380560464353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58682443351628696322476549 11002958128430380560464353)
    ·
      refine ⟨8252218596322785420348265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11002958128430380560464353 8252218596322785420348265)
      ·
        refine ⟨6189163947242089065261199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8252218596322785420348265 6189163947242089065261199)
        ·
          refine ⟨9283745920863133597891799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6189163947242089065261199 9283745920863133597891799)
          ·
            refine ⟨13925618881294700396837699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9283745920863133597891799 13925618881294700396837699)
            ·
              refine ⟨20888428321942050595256549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13925618881294700396837699 20888428321942050595256549)
              ·
                refine ⟨3916580310364134486610603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20888428321942050595256549 3916580310364134486610603)
                ·
                  refine ⟨5874870465546201729915905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916580310364134486610603 5874870465546201729915905)
                  ·
                    refine ⟨4406152849159651297436929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5874870465546201729915905 4406152849159651297436929)
                    ·
                      refine ⟨3304614636869738473077697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4406152849159651297436929 3304614636869738473077697)
                      ·
                        rfl

theorem cell23_6435714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_6435714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435714 prefixEnd_6435714 := by exact prefixLift 6435714
  have htrace : WordTrace (prefixWord ++ tailWord_6435714) baseStart_6435714 baseEnd_6435714 := by
    simpa [prefixWord, tailWord_6435714, baseEnd_6435714] using wordTrace_append hprefix tailTrace_6435714
  have hstable : (prefixWord ++ tailWord_6435714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435714).length < 2 ^ (prefixWord ++ tailWord_6435714).sum := by decide
  have hdescent : baseEnd_6435714 < baseStart_6435714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435769 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 2, 3, 3]
def baseStart_6435769 : Nat := 118140960795 + 6435769 * 2 ^ 59
def prefixEnd_6435769 : Nat := 4983230072969 + 3 ^ 40 * 6435769 * 2
def baseEnd_6435769 : Nat := 3304642878305735757889943

theorem tailTrace_6435769 : CollatzResearch.WordTrace tailWord_6435769 prefixEnd_6435769 3304642878305735757889943 := by
  unfold tailWord_6435769
  simp only [CollatzResearch.WordTrace]
  refine ⟨234731779421315529683158361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156487852947543686455438907 234731779421315529683158361)
  ·
    refine ⟨176048834565986647262368771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234731779421315529683158361 176048834565986647262368771)
    ·
      refine ⟨264073251848979970893553157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176048834565986647262368771 264073251848979970893553157)
      ·
        refine ⟨49513734721683744542541217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 264073251848979970893553157 49513734721683744542541217)
        ·
          refine ⟨37135301041262808406905913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49513734721683744542541217 37135301041262808406905913)
          ·
            refine ⟨27851475780947106305179435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37135301041262808406905913 27851475780947106305179435)
            ·
              refine ⟨41777213671420659457769153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27851475780947106305179435 41777213671420659457769153)
              ·
                refine ⟨31332910253565494593326865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41777213671420659457769153 31332910253565494593326865)
                ·
                  refine ⟨23499682690174120944995149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31332910253565494593326865 23499682690174120944995149)
                  ·
                    refine ⟨8812381008815295354373181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23499682690174120944995149 8812381008815295354373181)
                    ·
                      refine ⟨3304642878305735757889943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8812381008815295354373181 3304642878305735757889943)
                      ·
                        rfl

theorem cell23_6435769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_6435769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435769 prefixEnd_6435769 := by exact prefixLift 6435769
  have htrace : WordTrace (prefixWord ++ tailWord_6435769) baseStart_6435769 baseEnd_6435769 := by
    simpa [prefixWord, tailWord_6435769, baseEnd_6435769] using wordTrace_append hprefix tailTrace_6435769
  have hstable : (prefixWord ++ tailWord_6435769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435769).length < 2 ^ (prefixWord ++ tailWord_6435769).sum := by decide
  have hdescent : baseEnd_6435769 < baseStart_6435769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435809 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_6435809 : Nat := 118140960795 + 6435809 * 2 ^ 59
def prefixEnd_6435809 : Nat := 4983230072969 + 3 ^ 40 * 6435809 * 2
def baseEnd_6435809 : Nat := 3304663417531915601389759

theorem tailTrace_6435809 : CollatzResearch.WordTrace tailWord_6435809 prefixEnd_6435809 3304663417531915601389759 := by
  unfold tailWord_6435809
  simp only [CollatzResearch.WordTrace]
  refine ⟨234733238341170616514614481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156488825560780411009742987 234733238341170616514614481)
  ·
    refine ⟨176049928755877962385960861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234733238341170616514614481 176049928755877962385960861)
    ·
      refine ⟨66018723283454235894735323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 176049928755877962385960861 66018723283454235894735323)
      ·
        refine ⟨99028084925181353842102985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66018723283454235894735323 99028084925181353842102985)
        ·
          refine ⟨74271063693886015381577239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99028084925181353842102985 74271063693886015381577239)
          ·
            refine ⟨111406595540829023072365859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74271063693886015381577239 111406595540829023072365859)
            ·
              refine ⟨167109893311243534608548789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111406595540829023072365859 167109893311243534608548789)
              ·
                refine ⟨15666552497929081369551449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 167109893311243534608548789 15666552497929081369551449)
                ·
                  refine ⟨11749914373446811027163587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15666552497929081369551449 11749914373446811027163587)
                  ·
                    refine ⟨17624871560170216540745381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11749914373446811027163587 17624871560170216540745381)
                    ·
                      refine ⟨3304663417531915601389759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17624871560170216540745381 3304663417531915601389759)
                      ·
                        rfl

theorem cell23_6435809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_6435809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435809 prefixEnd_6435809 := by exact prefixLift 6435809
  have htrace : WordTrace (prefixWord ++ tailWord_6435809) baseStart_6435809 baseEnd_6435809 := by
    simpa [prefixWord, tailWord_6435809, baseEnd_6435809] using wordTrace_append hprefix tailTrace_6435809
  have hstable : (prefixWord ++ tailWord_6435809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435809).length < 2 ^ (prefixWord ++ tailWord_6435809).sum := by decide
  have hdescent : baseEnd_6435809 < baseStart_6435809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435810 : List Nat := [3, 3, 3, 1, 1, 3, 1, 3, 5]
def baseStart_6435810 : Nat := 118140960795 + 6435810 * 2 ^ 59
def prefixEnd_6435810 : Nat := 4983230072969 + 3 ^ 40 * 6435810 * 2
def baseEnd_6435810 : Nat := 367184881223618899719695

theorem tailTrace_6435810 : CollatzResearch.WordTrace tailWord_6435810 prefixEnd_6435810 367184881223618899719695 := by
  unfold tailWord_6435810
  simp only [CollatzResearch.WordTrace]
  refine ⟨58683318703541748421350221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156488849876111329123600589 58683318703541748421350221)
  ·
    refine ⟨22006244513828155658006333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58683318703541748421350221 22006244513828155658006333)
    ·
      refine ⟨8252341692685558371752375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22006244513828155658006333 8252341692685558371752375)
      ·
        refine ⟨12378512539028337557628563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8252341692685558371752375 12378512539028337557628563)
        ·
          refine ⟨18567768808542506336442845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12378512539028337557628563 18567768808542506336442845)
          ·
            refine ⟨6962913303203439876166067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18567768808542506336442845 6962913303203439876166067)
            ·
              refine ⟨10444369954805159814249101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6962913303203439876166067 10444369954805159814249101)
              ·
                refine ⟨3916638733051934930343413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10444369954805159814249101 3916638733051934930343413)
                ·
                  refine ⟨367184881223618899719695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3916638733051934930343413 367184881223618899719695)
                  ·
                    rfl

theorem cell23_6435810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_6435810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435810 prefixEnd_6435810 := by exact prefixLift 6435810
  have htrace : WordTrace (prefixWord ++ tailWord_6435810) baseStart_6435810 baseEnd_6435810 := by
    simpa [prefixWord, tailWord_6435810, baseEnd_6435810] using wordTrace_append hprefix tailTrace_6435810
  have hstable : (prefixWord ++ tailWord_6435810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435810).length < 2 ^ (prefixWord ++ tailWord_6435810).sum := by decide
  have hdescent : baseEnd_6435810 < baseStart_6435810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6435836 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 3, 4]
def baseStart_6435836 : Nat := 118140960795 + 6435836 * 2 ^ 59
def prefixEnd_6435836 : Nat := 4983230072969 + 3 ^ 40 * 6435836 * 2
def baseEnd_6435836 : Nat := 1101559093836528998584045

theorem tailTrace_6435836 : CollatzResearch.WordTrace tailWord_6435836 prefixEnd_6435836 1101559093836528998584045 := by
  unfold tailWord_6435836
  simp only [CollatzResearch.WordTrace]
  refine ⟨117367111556036400062923681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156489482074715200083898241 117367111556036400062923681)
  ·
    refine ⟨88025333667027300047192761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117367111556036400062923681 88025333667027300047192761)
    ·
      refine ⟨66019000250270475035394571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88025333667027300047192761 66019000250270475035394571)
      ·
        refine ⟨99028500375405712553091857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66019000250270475035394571 99028500375405712553091857)
        ·
          refine ⟨74271375281554284414818893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99028500375405712553091857 74271375281554284414818893)
          ·
            refine ⟨27851765730582856655557085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74271375281554284414818893 27851765730582856655557085)
            ·
              refine ⟨10444412148968571245833907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27851765730582856655557085 10444412148968571245833907)
              ·
                refine ⟨15666618223452856868750861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10444412148968571245833907 15666618223452856868750861)
                ·
                  refine ⟨5874981833794821325781573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15666618223452856868750861 5874981833794821325781573)
                  ·
                    refine ⟨1101559093836528998584045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5874981833794821325781573 1101559093836528998584045)
                    ·
                      rfl

theorem cell23_6435836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_6435836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6435836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6435836 prefixEnd_6435836 := by exact prefixLift 6435836
  have htrace : WordTrace (prefixWord ++ tailWord_6435836) baseStart_6435836 baseEnd_6435836 := by
    simpa [prefixWord, tailWord_6435836, baseEnd_6435836] using wordTrace_append hprefix tailTrace_6435836
  have hstable : (prefixWord ++ tailWord_6435836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6435836).length < 2 ^ (prefixWord ++ tailWord_6435836).sum := by decide
  have hdescent : baseEnd_6435836 < baseStart_6435836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6435836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
