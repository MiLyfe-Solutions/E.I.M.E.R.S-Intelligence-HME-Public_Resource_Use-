import V185TrunkScan23Chunk0398

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2359386 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_2359386 : Nat := 118140960795 + 2359386 * 2 ^ 59
def prefixEnd_2359386 : Nat := 4983230072969 + 3 ^ 40 * 2359386 * 2
def baseEnd_2359386 : Nat := 403833022496337041708129

theorem tailTrace_2359386 : CollatzResearch.WordTrace tailWord_2359386 prefixEnd_2359386 403833022496337041708129 := by
  unfold tailWord_2359386
  simp only [CollatzResearch.WordTrace]
  refine ⟨21513469257588736973334503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57369251353569965262225341 21513469257588736973334503)
  ·
    refine ⟨32270203886383105460001755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21513469257588736973334503 32270203886383105460001755)
    ·
      refine ⟨48405305829574658190002633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32270203886383105460001755 48405305829574658190002633)
      ·
        refine ⟨36303979372180993642501975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48405305829574658190002633 36303979372180993642501975)
        ·
          refine ⟨54455969058271490463752963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36303979372180993642501975 54455969058271490463752963)
          ·
            refine ⟨81683953587407235695629445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54455969058271490463752963 81683953587407235695629445)
            ·
              refine ⟨15315741297638856692930521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81683953587407235695629445 15315741297638856692930521)
              ·
                refine ⟨11486805973229142519697891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15315741297638856692930521 11486805973229142519697891)
                ·
                  refine ⟨17230208959843713779546837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11486805973229142519697891 17230208959843713779546837)
                  ·
                    refine ⟨403833022496337041708129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17230208959843713779546837 403833022496337041708129)
                    ·
                      rfl

theorem cell23_2359386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_2359386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359386 prefixEnd_2359386 := by exact prefixLift 2359386
  have htrace : WordTrace (prefixWord ++ tailWord_2359386) baseStart_2359386 baseEnd_2359386 := by
    simpa [prefixWord, tailWord_2359386, baseEnd_2359386] using wordTrace_append hprefix tailTrace_2359386
  have hstable : (prefixWord ++ tailWord_2359386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359386).length < 2 ^ (prefixWord ++ tailWord_2359386).sum := by decide
  have hdescent : baseEnd_2359386 < baseStart_2359386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359393 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 4, 5, 2]
def baseStart_2359393 : Nat := 118140960795 + 2359393 * 2 ^ 59
def prefixEnd_2359393 : Nat := 4983230072969 + 3 ^ 40 * 2359393 * 2
def baseEnd_2359393 : Nat := 1211502661853592597736855

theorem tailTrace_2359393 : CollatzResearch.WordTrace tailWord_2359393 prefixEnd_2359393 1211502661853592597736855 := by
  unfold tailWord_2359393
  simp only [CollatzResearch.WordTrace]
  refine ⟨86054132341329588088842833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57369421560886392059228555 86054132341329588088842833)
  ·
    refine ⟨64540599255997191066632125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86054132341329588088842833 64540599255997191066632125)
    ·
      refine ⟨24202724720998946649987047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64540599255997191066632125 24202724720998946649987047)
      ·
        refine ⟨36304087081498419974980571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24202724720998946649987047 36304087081498419974980571)
        ·
          refine ⟨54456130622247629962470857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36304087081498419974980571 54456130622247629962470857)
          ·
            refine ⟨40842097966685722471853143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54456130622247629962470857 40842097966685722471853143)
            ·
              refine ⟨61263146950028583707779715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40842097966685722471853143 61263146950028583707779715)
              ·
                refine ⟨91894720425042875561669573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61263146950028583707779715 91894720425042875561669573)
                ·
                  refine ⟨17230260079695539167813045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91894720425042875561669573 17230260079695539167813045)
                  ·
                    refine ⟨1615336882471456796982473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17230260079695539167813045 1615336882471456796982473)
                    ·
                      refine ⟨1211502661853592597736855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615336882471456796982473 1211502661853592597736855)
                      ·
                        rfl

theorem cell23_2359393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_2359393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359393 prefixEnd_2359393 := by exact prefixLift 2359393
  have htrace : WordTrace (prefixWord ++ tailWord_2359393) baseStart_2359393 baseEnd_2359393 := by
    simpa [prefixWord, tailWord_2359393, baseEnd_2359393] using wordTrace_append hprefix tailTrace_2359393
  have hstable : (prefixWord ++ tailWord_2359393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359393).length < 2 ^ (prefixWord ++ tailWord_2359393).sum := by decide
  have hdescent : baseEnd_2359393 < baseStart_2359393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359396 : List Nat := [2, 3, 1, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_2359396 : Nat := 118140960795 + 2359396 * 2 ^ 59
def prefixEnd_2359396 : Nat := 4983230072969 + 3 ^ 40 * 2359396 * 2
def baseEnd_2359396 : Nat := 1211504202295556085999341

theorem tailTrace_2359396 : CollatzResearch.WordTrace tailWord_2359396 prefixEnd_2359396 1211504202295556085999341 := by
  unfold tailWord_2359396
  simp only [CollatzResearch.WordTrace]
  refine ⟨43027120880159359800601021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57369494506879146400801361 43027120880159359800601021)
  ·
    refine ⟨16135170330059759925225383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43027120880159359800601021 16135170330059759925225383)
    ·
      refine ⟨24202755495089639887838075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16135170330059759925225383 24202755495089639887838075)
      ·
        refine ⟨36304133242634459831757113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24202755495089639887838075 36304133242634459831757113)
        ·
          refine ⟨27228099931975844873817835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36304133242634459831757113 27228099931975844873817835)
          ·
            refine ⟨40842149897963767310726753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27228099931975844873817835 40842149897963767310726753)
            ·
              refine ⟨30631612423472825483045065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40842149897963767310726753 30631612423472825483045065)
              ·
                refine ⟨22973709317604619112283799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30631612423472825483045065 22973709317604619112283799)
                ·
                  refine ⟨34460563976406928668425699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22973709317604619112283799 34460563976406928668425699)
                  ·
                    refine ⟨51690845964610393002638549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34460563976406928668425699 51690845964610393002638549)
                    ·
                      refine ⟨1211504202295556085999341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51690845964610393002638549 1211504202295556085999341)
                      ·
                        rfl

theorem cell23_2359396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_2359396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359396 prefixEnd_2359396 := by exact prefixLift 2359396
  have htrace : WordTrace (prefixWord ++ tailWord_2359396) baseStart_2359396 baseEnd_2359396 := by
    simpa [prefixWord, tailWord_2359396, baseEnd_2359396] using wordTrace_append hprefix tailTrace_2359396
  have hstable : (prefixWord ++ tailWord_2359396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359396).length < 2 ^ (prefixWord ++ tailWord_2359396).sum := by decide
  have hdescent : baseEnd_2359396 < baseStart_2359396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359484 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 3, 4]
def baseStart_2359484 : Nat := 118140960795 + 2359484 * 2 ^ 59
def prefixEnd_2359484 : Nat := 4983230072969 + 3 ^ 40 * 2359484 * 2
def baseEnd_2359484 : Nat := 403849796197717247232979

theorem tailTrace_2359484 : CollatzResearch.WordTrace tailWord_2359484 prefixEnd_2359484 403849796197717247232979 := by
  unfold tailWord_2359484
  simp only [CollatzResearch.WordTrace]
  refine ⟨43028725691999955315202753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57371634255999940420270337 43028725691999955315202753)
  ·
    refine ⟨32271544268999966486402065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43028725691999955315202753 32271544268999966486402065)
    ·
      refine ⟨24203658201749974864801549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32271544268999966486402065 24203658201749974864801549)
      ·
        refine ⟨9076371825656240574300581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24203658201749974864801549 9076371825656240574300581)
        ·
          refine ⟨1701819717310545107681359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9076371825656240574300581 1701819717310545107681359)
          ·
            refine ⟨2552729575965817661522039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701819717310545107681359 2552729575965817661522039)
            ·
              refine ⟨3829094363948726492283059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552729575965817661522039 3829094363948726492283059)
              ·
                refine ⟨5743641545923089738424589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3829094363948726492283059 5743641545923089738424589)
                ·
                  refine ⟨2153865579721158651909221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5743641545923089738424589 2153865579721158651909221)
                  ·
                    refine ⟨403849796197717247232979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2153865579721158651909221 403849796197717247232979)
                    ·
                      rfl

theorem cell23_2359484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_2359484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359484 prefixEnd_2359484 := by exact prefixLift 2359484
  have htrace : WordTrace (prefixWord ++ tailWord_2359484) baseStart_2359484 baseEnd_2359484 := by
    simpa [prefixWord, tailWord_2359484, baseEnd_2359484] using wordTrace_append hprefix tailTrace_2359484
  have hstable : (prefixWord ++ tailWord_2359484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359484).length < 2 ^ (prefixWord ++ tailWord_2359484).sum := by decide
  have hdescent : baseEnd_2359484 < baseStart_2359484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359550 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2359550 : Nat := 118140960795 + 2359550 * 2 ^ 59
def prefixEnd_2359550 : Nat := 4983230072969 + 3 ^ 40 * 2359550 * 2
def baseEnd_2359550 : Nat := 1211583278316348483473633

theorem tailTrace_2359550 : CollatzResearch.WordTrace tailWord_2359550 prefixEnd_2359550 1211583278316348483473633 := by
  unfold tailWord_2359550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10757482325220100487788513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57373239067840535934872069 10757482325220100487788513)
  ·
    refine ⟨8068111743915075365841385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10757482325220100487788513 8068111743915075365841385)
    ·
      refine ⟨6051083807936306524381039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8068111743915075365841385 6051083807936306524381039)
      ·
        refine ⟨9076625711904459786571559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6051083807936306524381039 9076625711904459786571559)
        ·
          refine ⟨13614938567856689679857339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9076625711904459786571559 13614938567856689679857339)
          ·
            refine ⟨20422407851785034519786009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13614938567856689679857339 20422407851785034519786009)
            ·
              refine ⟨15316805888838775889839507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20422407851785034519786009 15316805888838775889839507)
              ·
                refine ⟨22975208833258163834759261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15316805888838775889839507 22975208833258163834759261)
                ·
                  refine ⟨8615703312471811438034723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22975208833258163834759261 8615703312471811438034723)
                  ·
                    refine ⟨12923554968707717157052085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8615703312471811438034723 12923554968707717157052085)
                    ·
                      refine ⟨1211583278316348483473633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12923554968707717157052085 1211583278316348483473633)
                      ·
                        rfl

theorem cell23_2359550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2359550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359550 prefixEnd_2359550 := by exact prefixLift 2359550
  have htrace : WordTrace (prefixWord ++ tailWord_2359550) baseStart_2359550 baseEnd_2359550 := by
    simpa [prefixWord, tailWord_2359550, baseEnd_2359550] using wordTrace_append hprefix tailTrace_2359550
  have hstable : (prefixWord ++ tailWord_2359550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359550).length < 2 ^ (prefixWord ++ tailWord_2359550).sum := by decide
  have hdescent : baseEnd_2359550 < baseStart_2359550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359560 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_2359560 : Nat := 118140960795 + 2359560 * 2 ^ 59
def prefixEnd_2359560 : Nat := 4983230072969 + 3 ^ 40 * 2359560 * 2
def baseEnd_2359560 : Nat := 1211588413122893444348587

theorem tailTrace_2359560 : CollatzResearch.WordTrace tailWord_2359560 prefixEnd_2359560 1211588413122893444348587 := by
  unfold tailWord_2359560
  simp only [CollatzResearch.WordTrace]
  refine ⟨43030111665862287805086067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57373482221149717073448089 43030111665862287805086067)
  ·
    refine ⟨64545167498793431707629101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43030111665862287805086067 64545167498793431707629101)
    ·
      refine ⟨24204437812047536890360913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64545167498793431707629101 24204437812047536890360913)
      ·
        refine ⟨18153328359035652667770685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24204437812047536890360913 18153328359035652667770685)
        ·
          refine ⟨6807498134638369750414007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18153328359035652667770685 6807498134638369750414007)
          ·
            refine ⟨10211247201957554625621011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6807498134638369750414007 10211247201957554625621011)
            ·
              refine ⟨15316870802936331938431517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10211247201957554625621011 15316870802936331938431517)
              ·
                refine ⟨5743826551101124476911819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15316870802936331938431517 5743826551101124476911819)
                ·
                  refine ⟨8615739826651686715367729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5743826551101124476911819 8615739826651686715367729)
                  ·
                    refine ⟨6461804869988765036525797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8615739826651686715367729 6461804869988765036525797)
                    ·
                      refine ⟨1211588413122893444348587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6461804869988765036525797 1211588413122893444348587)
                      ·
                        rfl

theorem cell23_2359560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_2359560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359560 prefixEnd_2359560 := by exact prefixLift 2359560
  have htrace : WordTrace (prefixWord ++ tailWord_2359560) baseStart_2359560 baseEnd_2359560 := by
    simpa [prefixWord, tailWord_2359560, baseEnd_2359560] using wordTrace_append hprefix tailTrace_2359560
  have hstable : (prefixWord ++ tailWord_2359560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359560).length < 2 ^ (prefixWord ++ tailWord_2359560).sum := by decide
  have hdescent : baseEnd_2359560 < baseStart_2359560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359581 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 1, 1, 4]
def baseStart_2359581 : Nat := 118140960795 + 2359581 * 2 ^ 59
def prefixEnd_2359581 : Nat := 4983230072969 + 3 ^ 40 * 2359581 * 2
def baseEnd_2359581 : Nat := 1211599196216637862185991

theorem tailTrace_2359581 : CollatzResearch.WordTrace tailWord_2359581 prefixEnd_2359581 1211599196216637862185991 := by
  unfold tailWord_2359581
  simp only [CollatzResearch.WordTrace]
  refine ⟨86060989264648496196686597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57373992843098997464457731 86060989264648496196686597)
  ·
    refine ⟨16136435487121593036878737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86060989264648496196686597 16136435487121593036878737)
    ·
      refine ⟨12102326615341194777659053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16136435487121593036878737 12102326615341194777659053)
      ·
        refine ⟨4538372480752948041622145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12102326615341194777659053 4538372480752948041622145)
        ·
          refine ⟨3403779360564711031216609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4538372480752948041622145 3403779360564711031216609)
          ·
            refine ⟨2552834520423533273412457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3403779360564711031216609 2552834520423533273412457)
            ·
              refine ⟨1914625890317649955059343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552834520423533273412457 1914625890317649955059343)
              ·
                refine ⟨2871938835476474932589015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914625890317649955059343 2871938835476474932589015)
                ·
                  refine ⟨4307908253214712398883523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871938835476474932589015 4307908253214712398883523)
                  ·
                    refine ⟨6461862379822068598325285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4307908253214712398883523 6461862379822068598325285)
                    ·
                      refine ⟨1211599196216637862185991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6461862379822068598325285 1211599196216637862185991)
                      ·
                        rfl

theorem cell23_2359581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_2359581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359581 prefixEnd_2359581 := by exact prefixLift 2359581
  have htrace : WordTrace (prefixWord ++ tailWord_2359581) baseStart_2359581 baseEnd_2359581 := by
    simpa [prefixWord, tailWord_2359581, baseEnd_2359581] using wordTrace_append hprefix tailTrace_2359581
  have hstable : (prefixWord ++ tailWord_2359581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359581).length < 2 ^ (prefixWord ++ tailWord_2359581).sum := by decide
  have hdescent : baseEnd_2359581 < baseStart_2359581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359584 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 1, 2, 3]
def baseStart_2359584 : Nat := 118140960795 + 2359584 * 2 ^ 59
def prefixEnd_2359584 : Nat := 4983230072969 + 3 ^ 40 * 2359584 * 2
def baseEnd_2359584 : Nat := 1211600736658601350448477

theorem tailTrace_2359584 : CollatzResearch.WordTrace tailWord_2359584 prefixEnd_2359584 1211600736658601350448477 := by
  unfold tailWord_2359584
  simp only [CollatzResearch.WordTrace]
  refine ⟨43030549341818813854522903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57374065789091751806030537 43030549341818813854522903)
  ·
    refine ⟨64545824012728220781784355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43030549341818813854522903 64545824012728220781784355)
    ·
      refine ⟨96818736019092331172676533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64545824012728220781784355 96818736019092331172676533)
      ·
        refine ⟨9076756501789906047438425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96818736019092331172676533 9076756501789906047438425)
        ·
          refine ⟨6807567376342429535578819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9076756501789906047438425 6807567376342429535578819)
          ·
            refine ⟨10211351064513644303368229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6807567376342429535578819 10211351064513644303368229)
            ·
              refine ⟨1914628324596308306881543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10211351064513644303368229 1914628324596308306881543)
              ·
                refine ⟨2871942486894462460322315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914628324596308306881543 2871942486894462460322315)
                ·
                  refine ⟨4307913730341693690483473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2871942486894462460322315 4307913730341693690483473)
                  ·
                    refine ⟨3230935297756270267862605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4307913730341693690483473 3230935297756270267862605)
                    ·
                      refine ⟨1211600736658601350448477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3230935297756270267862605 1211600736658601350448477)
                      ·
                        rfl

theorem cell23_2359584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_2359584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359584 prefixEnd_2359584 := by exact prefixLift 2359584
  have htrace : WordTrace (prefixWord ++ tailWord_2359584) baseStart_2359584 baseEnd_2359584 := by
    simpa [prefixWord, tailWord_2359584, baseEnd_2359584] using wordTrace_append hprefix tailTrace_2359584
  have hstable : (prefixWord ++ tailWord_2359584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359584).length < 2 ^ (prefixWord ++ tailWord_2359584).sum := by decide
  have hdescent : baseEnd_2359584 < baseStart_2359584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359591 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 4, 4]
def baseStart_2359591 : Nat := 118140960795 + 2359591 * 2 ^ 59
def prefixEnd_2359591 : Nat := 4983230072969 + 3 ^ 40 * 2359591 * 2
def baseEnd_2359591 : Nat := 403868110341060941020315

theorem tailTrace_2359591 : CollatzResearch.WordTrace tailWord_2359591 prefixEnd_2359591 403868110341060941020315 := by
  unfold tailWord_2359591
  simp only [CollatzResearch.WordTrace]
  refine ⟨86061353994612267904550627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57374235996408178603033751 86061353994612267904550627)
  ·
    refine ⟨129092030991918401856825941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86061353994612267904550627 129092030991918401856825941)
    ·
      refine ⟨1512797238186543771759679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 129092030991918401856825941 1512797238186543771759679)
      ·
        refine ⟨2269195857279815657639519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512797238186543771759679 2269195857279815657639519)
        ·
          refine ⟨3403793785919723486459279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269195857279815657639519 3403793785919723486459279)
          ·
            refine ⟨5105690678879585229688919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3403793785919723486459279 5105690678879585229688919)
            ·
              refine ⟨7658536018319377844533379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5105690678879585229688919 7658536018319377844533379)
              ·
                refine ⟨11487804027479066766800069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7658536018319377844533379 11487804027479066766800069)
                ·
                  refine ⟨2153963255152325018775013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11487804027479066766800069 2153963255152325018775013)
                  ·
                    refine ⟨403868110341060941020315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2153963255152325018775013 403868110341060941020315)
                    ·
                      rfl

theorem cell23_2359591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_2359591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359591 prefixEnd_2359591 := by exact prefixLift 2359591
  have htrace : WordTrace (prefixWord ++ tailWord_2359591) baseStart_2359591 baseEnd_2359591 := by
    simpa [prefixWord, tailWord_2359591, baseEnd_2359591] using wordTrace_append hprefix tailTrace_2359591
  have hstable : (prefixWord ++ tailWord_2359591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359591).length < 2 ^ (prefixWord ++ tailWord_2359591).sum := by decide
  have hdescent : baseEnd_2359591 < baseStart_2359591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359598 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_2359598 : Nat := 118140960795 + 2359598 * 2 ^ 59
def prefixEnd_2359598 : Nat := 4983230072969 + 3 ^ 40 * 2359598 * 2
def baseEnd_2359598 : Nat := 1211607925387764295673413

theorem tailTrace_2359598 : CollatzResearch.WordTrace tailWord_2359598 prefixEnd_2359598 1211607925387764295673413 := by
  unfold tailWord_2359598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10757701163198363512506931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57374406203724605400036965 10757701163198363512506931)
  ·
    refine ⟨16136551744797545268760397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10757701163198363512506931 16136551744797545268760397)
    ·
      refine ⟨6051206904299079475785149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16136551744797545268760397 6051206904299079475785149)
      ·
        refine ⟨2269202589112154803419431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6051206904299079475785149 2269202589112154803419431)
        ·
          refine ⟨3403803883668232205129147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269202589112154803419431 3403803883668232205129147)
          ·
            refine ⟨5105705825502348307693721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3403803883668232205129147 5105705825502348307693721)
            ·
              refine ⟨3829279369126761230770291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5105705825502348307693721 3829279369126761230770291)
              ·
                refine ⟨5743919053690141846155437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3829279369126761230770291 5743919053690141846155437)
                ·
                  refine ⟨2153969645133803192308289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5743919053690141846155437 2153969645133803192308289)
                  ·
                    refine ⟨1615477233850352394231217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2153969645133803192308289 1615477233850352394231217)
                    ·
                      refine ⟨1211607925387764295673413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615477233850352394231217 1211607925387764295673413)
                      ·
                        rfl

theorem cell23_2359598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_2359598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359598 prefixEnd_2359598 := by exact prefixLift 2359598
  have htrace : WordTrace (prefixWord ++ tailWord_2359598) baseStart_2359598 baseEnd_2359598 := by
    simpa [prefixWord, tailWord_2359598, baseEnd_2359598] using wordTrace_append hprefix tailTrace_2359598
  have hstable : (prefixWord ++ tailWord_2359598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359598).length < 2 ^ (prefixWord ++ tailWord_2359598).sum := by decide
  have hdescent : baseEnd_2359598 < baseStart_2359598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359614 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_2359614 : Nat := 118140960795 + 2359614 * 2 ^ 59
def prefixEnd_2359614 : Nat := 4983230072969 + 3 ^ 40 * 2359614 * 2
def baseEnd_2359614 : Nat := 1211616141078236233073339

theorem tailTrace_2359614 : CollatzResearch.WordTrace tailWord_2359614 prefixEnd_2359614 1211616141078236233073339 := by
  unfold tailWord_2359614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10757774109191117854079737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57374795249019295221758597 10757774109191117854079737)
  ·
    refine ⟨8068330581893338390559803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10757774109191117854079737 8068330581893338390559803)
    ·
      refine ⟨12102495872840007585839705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8068330581893338390559803 12102495872840007585839705)
      ·
        refine ⟨9076871904630005689379779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12102495872840007585839705 9076871904630005689379779)
        ·
          refine ⟨13615307856945008534069669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9076871904630005689379779 13615307856945008534069669)
          ·
            refine ⟨2552870223177189100138063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13615307856945008534069669 2552870223177189100138063)
            ·
              refine ⟨3829305334765783650207095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552870223177189100138063 3829305334765783650207095)
              ·
                refine ⟨5743958002148675475310643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3829305334765783650207095 5743958002148675475310643)
                ·
                  refine ⟨8615937003223013212965965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5743958002148675475310643 8615937003223013212965965)
                  ·
                    refine ⟨3230976376208629954862237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8615937003223013212965965 3230976376208629954862237)
                    ·
                      refine ⟨1211616141078236233073339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3230976376208629954862237 1211616141078236233073339)
                      ·
                        rfl

theorem cell23_2359614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_2359614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359614 prefixEnd_2359614 := by exact prefixLift 2359614
  have htrace : WordTrace (prefixWord ++ tailWord_2359614) baseStart_2359614 baseEnd_2359614 := by
    simpa [prefixWord, tailWord_2359614, baseEnd_2359614] using wordTrace_append hprefix tailTrace_2359614
  have hstable : (prefixWord ++ tailWord_2359614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359614).length < 2 ^ (prefixWord ++ tailWord_2359614).sum := by decide
  have hdescent : baseEnd_2359614 < baseStart_2359614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359663 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_2359663 : Nat := 118140960795 + 2359663 * 2 ^ 59
def prefixEnd_2359663 : Nat := 4983230072969 + 3 ^ 40 * 2359663 * 2
def baseEnd_2359663 : Nat := 1211641301630306541360613

theorem tailTrace_2359663 : CollatzResearch.WordTrace tailWord_2359663 prefixEnd_2359663 1211641301630306541360613 := by
  unfold tailWord_2359663
  simp only [CollatzResearch.WordTrace]
  refine ⟨86063980050351424201171643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57375986700234282800781095 86063980050351424201171643)
  ·
    refine ⟨129095970075527136301757465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86063980050351424201171643 129095970075527136301757465)
    ·
      refine ⟨96821977556645352226318099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129095970075527136301757465 96821977556645352226318099)
      ·
        refine ⟨145232966334968028339477149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96821977556645352226318099 145232966334968028339477149)
        ·
          refine ⟨54462362375613010627303931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145232966334968028339477149 54462362375613010627303931)
          ·
            refine ⟨81693543563419515940955897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54462362375613010627303931 81693543563419515940955897)
            ·
              refine ⟨61270157672564636955716923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81693543563419515940955897 61270157672564636955716923)
              ·
                refine ⟨91905236508846955433575385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61270157672564636955716923 91905236508846955433575385)
                ·
                  refine ⟨68928927381635216575181539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 91905236508846955433575385 68928927381635216575181539)
                  ·
                    refine ⟨103393391072452824862772309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68928927381635216575181539 103393391072452824862772309)
                    ·
                      refine ⟨1211641301630306541360613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 103393391072452824862772309 1211641301630306541360613)
                      ·
                        rfl

theorem cell23_2359663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_2359663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359663 prefixEnd_2359663 := by exact prefixLift 2359663
  have htrace : WordTrace (prefixWord ++ tailWord_2359663) baseStart_2359663 baseEnd_2359663 := by
    simpa [prefixWord, tailWord_2359663, baseEnd_2359663] using wordTrace_append hprefix tailTrace_2359663
  have hstable : (prefixWord ++ tailWord_2359663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359663).length < 2 ^ (prefixWord ++ tailWord_2359663).sum := by decide
  have hdescent : baseEnd_2359663 < baseStart_2359663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359737 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 5, 4]
def baseStart_2359737 : Nat := 118140960795 + 2359737 * 2 ^ 59
def prefixEnd_2359737 : Nat := 4983230072969 + 3 ^ 40 * 2359737 * 2
def baseEnd_2359737 : Nat := 403893099732913083945091

theorem tailTrace_2359737 : CollatzResearch.WordTrace tailWord_2359737 prefixEnd_2359737 403893099732913083945091 := by
  unfold tailWord_2359737
  simp only [CollatzResearch.WordTrace]
  refine ⟨86066679052083334839365465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57377786034722223226243643 86066679052083334839365465)
  ·
    refine ⟨64550009289062501129524099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86066679052083334839365465 64550009289062501129524099)
    ·
      refine ⟨96825013933593751694286149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64550009289062501129524099 96825013933593751694286149)
      ·
        refine ⟨18154690112548828442678653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96825013933593751694286149 18154690112548828442678653)
        ·
          refine ⟨6808008792205810666004495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18154690112548828442678653 6808008792205810666004495)
          ·
            refine ⟨10212013188308715999006743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808008792205810666004495 10212013188308715999006743)
            ·
              refine ⟨15318019782463073998510115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10212013188308715999006743 15318019782463073998510115)
              ·
                refine ⟨22977029673694610997765173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15318019782463073998510115 22977029673694610997765173)
                ·
                  refine ⟨2154096531908869781040485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22977029673694610997765173 2154096531908869781040485)
                  ·
                    refine ⟨403893099732913083945091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2154096531908869781040485 403893099732913083945091)
                    ·
                      rfl

theorem cell23_2359737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 5, 4].length) (baseStart_2359737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359737 prefixEnd_2359737 := by exact prefixLift 2359737
  have htrace : WordTrace (prefixWord ++ tailWord_2359737) baseStart_2359737 baseEnd_2359737 := by
    simpa [prefixWord, tailWord_2359737, baseEnd_2359737] using wordTrace_append hprefix tailTrace_2359737
  have hstable : (prefixWord ++ tailWord_2359737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359737).length < 2 ^ (prefixWord ++ tailWord_2359737).sum := by decide
  have hdescent : baseEnd_2359737 < baseStart_2359737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359770 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8]
def baseStart_2359770 : Nat := 118140960795 + 2359770 * 2 ^ 59
def prefixEnd_2359770 : Nat := 4983230072969 + 3 ^ 40 * 2359770 * 2
def baseEnd_2359770 : Nat := 1211696244060337622722621

theorem tailTrace_2359770 : CollatzResearch.WordTrace tailWord_2359770 prefixEnd_2359770 1211696244060337622722621 := by
  unfold tailWord_2359770
  simp only [CollatzResearch.WordTrace]
  refine ⟨21516970665240945368829191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57378588440642520983544509 21516970665240945368829191)
  ·
    refine ⟨32275455997861418053243787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21516970665240945368829191 32275455997861418053243787)
    ·
      refine ⟨48413183996792127079865681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32275455997861418053243787 48413183996792127079865681)
      ·
        refine ⟨36309887997594095309899261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48413183996792127079865681 36309887997594095309899261)
        ·
          refine ⟨13616207999097785741212223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36309887997594095309899261 13616207999097785741212223)
          ·
            refine ⟨20424311998646678611818335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13616207999097785741212223 20424311998646678611818335)
            ·
              refine ⟨30636467997970017917727503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20424311998646678611818335 30636467997970017917727503)
              ·
                refine ⟨45954701996955026876591255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30636467997970017917727503 45954701996955026876591255)
                ·
                  refine ⟨68932052995432540314886883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45954701996955026876591255 68932052995432540314886883)
                  ·
                    refine ⟨103398079493148810472330325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68932052995432540314886883 103398079493148810472330325)
                    ·
                      refine ⟨1211696244060337622722621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 103398079493148810472330325 1211696244060337622722621)
                      ·
                        rfl

theorem cell23_2359770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_2359770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359770 prefixEnd_2359770 := by exact prefixLift 2359770
  have htrace : WordTrace (prefixWord ++ tailWord_2359770) baseStart_2359770 baseEnd_2359770 := by
    simpa [prefixWord, tailWord_2359770, baseEnd_2359770] using wordTrace_append hprefix tailTrace_2359770
  have hstable : (prefixWord ++ tailWord_2359770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359770).length < 2 ^ (prefixWord ++ tailWord_2359770).sum := by decide
  have hdescent : baseEnd_2359770 < baseStart_2359770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359784 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 6]
def baseStart_2359784 : Nat := 118140960795 + 2359784 * 2 ^ 59
def prefixEnd_2359784 : Nat := 4983230072969 + 3 ^ 40 * 2359784 * 2
def baseEnd_2359784 : Nat := 134633714754388951994173

theorem tailTrace_2359784 : CollatzResearch.WordTrace tailWord_2359784 prefixEnd_2359784 134633714754388951994173 := by
  unfold tailWord_2359784
  simp only [CollatzResearch.WordTrace]
  refine ⟨43034196641456530933163203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57378928855275374577550937 43034196641456530933163203)
  ·
    refine ⟨64551294962184796399744805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43034196641456530933163203 64551294962184796399744805)
    ·
      refine ⟨12103367805409649324952151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64551294962184796399744805 12103367805409649324952151)
      ·
        refine ⟨18155051708114473987428227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12103367805409649324952151 18155051708114473987428227)
        ·
          refine ⟨27232577562171710981142341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18155051708114473987428227 27232577562171710981142341)
          ·
            refine ⟨5106108292907195808964189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27232577562171710981142341 5106108292907195808964189)
            ·
              refine ⟨1914790609840198428361571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5106108292907195808964189 1914790609840198428361571)
              ·
                refine ⟨2872185914760297642542357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914790609840198428361571 2872185914760297642542357)
                ·
                  refine ⟨134633714754388951994173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2872185914760297642542357 134633714754388951994173)
                  ·
                    rfl

theorem cell23_2359784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 6].length) (baseStart_2359784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359784 prefixEnd_2359784 := by exact prefixLift 2359784
  have htrace : WordTrace (prefixWord ++ tailWord_2359784) baseStart_2359784 baseEnd_2359784 := by
    simpa [prefixWord, tailWord_2359784, baseEnd_2359784] using wordTrace_append hprefix tailTrace_2359784
  have hstable : (prefixWord ++ tailWord_2359784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359784).length < 2 ^ (prefixWord ++ tailWord_2359784).sum := by decide
  have hdescent : baseEnd_2359784 < baseStart_2359784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359787 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 3, 5, 2]
def baseStart_2359787 : Nat := 118140960795 + 2359787 * 2 ^ 59
def prefixEnd_2359787 : Nat := 4983230072969 + 3 ^ 40 * 2359787 * 2
def baseEnd_2359787 : Nat := 1211704973231464056210043

theorem tailTrace_2359787 : CollatzResearch.WordTrace tailWord_2359787 prefixEnd_2359787 1211704973231464056210043 := by
  unfold tailWord_2359787
  simp only [CollatzResearch.WordTrace]
  refine ⟨86068502701902193378685615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57379001801268128919123743 86068502701902193378685615)
  ·
    refine ⟨129102754052853290068028423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86068502701902193378685615 129102754052853290068028423)
    ·
      refine ⟨193654131079279935102042635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129102754052853290068028423 193654131079279935102042635)
      ·
        refine ⟨290481196618919902653063953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193654131079279935102042635 290481196618919902653063953)
        ·
          refine ⟨217860897464189926989797965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290481196618919902653063953 217860897464189926989797965)
          ·
            refine ⟨81697836549071222621174237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217860897464189926989797965 81697836549071222621174237)
            ·
              refine ⟨30636688705901708482940339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81697836549071222621174237 30636688705901708482940339)
              ·
                refine ⟨45955033058852562724410509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30636688705901708482940339 45955033058852562724410509)
                ·
                  refine ⟨17233137397069711021653941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45955033058852562724410509 17233137397069711021653941)
                  ·
                    refine ⟨1615606630975285408280057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17233137397069711021653941 1615606630975285408280057)
                    ·
                      refine ⟨1211704973231464056210043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615606630975285408280057 1211704973231464056210043)
                      ·
                        rfl

theorem cell23_2359787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 5, 2].length) (baseStart_2359787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359787 prefixEnd_2359787 := by exact prefixLift 2359787
  have htrace : WordTrace (prefixWord ++ tailWord_2359787) baseStart_2359787 baseEnd_2359787 := by
    simpa [prefixWord, tailWord_2359787, baseEnd_2359787] using wordTrace_append hprefix tailTrace_2359787
  have hstable : (prefixWord ++ tailWord_2359787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359787).length < 2 ^ (prefixWord ++ tailWord_2359787).sum := by decide
  have hdescent : baseEnd_2359787 < baseStart_2359787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359804 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 2, 3, 2]
def baseStart_2359804 : Nat := 118140960795 + 2359804 * 2 ^ 59
def prefixEnd_2359804 : Nat := 4983230072969 + 3 ^ 40 * 2359804 * 2
def baseEnd_2359804 : Nat := 1211713702402590489697465

theorem tailTrace_2359804 : CollatzResearch.WordTrace tailWord_2359804 prefixEnd_2359804 1211713702402590489697465 := by
  unfold tailWord_2359804
  simp only [CollatzResearch.WordTrace]
  refine ⟨43034561371420302641027233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57379415161893736854702977 43034561371420302641027233)
  ·
    refine ⟨32275921028565226980770425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43034561371420302641027233 32275921028565226980770425)
    ·
      refine ⟨24206940771423920235577819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32275921028565226980770425 24206940771423920235577819)
      ·
        refine ⟨36310411157135880353366729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24206940771423920235577819 36310411157135880353366729)
        ·
          refine ⟨27232808367851910265025047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36310411157135880353366729 27232808367851910265025047)
          ·
            refine ⟨40849212551777865397537571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27232808367851910265025047 40849212551777865397537571)
            ·
              refine ⟨61273818827666798096306357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40849212551777865397537571 61273818827666798096306357)
              ·
                refine ⟨5744420515093762321528721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61273818827666798096306357 5744420515093762321528721)
                ·
                  refine ⟨4308315386320321741146541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5744420515093762321528721 4308315386320321741146541)
                  ·
                    refine ⟨1615618269870120652929953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4308315386320321741146541 1615618269870120652929953)
                    ·
                      refine ⟨1211713702402590489697465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615618269870120652929953 1211713702402590489697465)
                      ·
                        rfl

theorem cell23_2359804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_2359804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359804 prefixEnd_2359804 := by exact prefixLift 2359804
  have htrace : WordTrace (prefixWord ++ tailWord_2359804) baseStart_2359804 baseEnd_2359804 := by
    simpa [prefixWord, tailWord_2359804, baseEnd_2359804] using wordTrace_append hprefix tailTrace_2359804
  have hstable : (prefixWord ++ tailWord_2359804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359804).length < 2 ^ (prefixWord ++ tailWord_2359804).sum := by decide
  have hdescent : baseEnd_2359804 < baseStart_2359804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359827 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 4, 4]
def baseStart_2359827 : Nat := 118140960795 + 2359827 * 2 ^ 59
def prefixEnd_2359827 : Nat := 4983230072969 + 3 ^ 40 * 2359827 * 2
def baseEnd_2359827 : Nat := 403908504152547966569953

theorem tailTrace_2359827 : CollatzResearch.WordTrace tailWord_2359827 prefixEnd_2359827 403908504152547966569953 := by
  unfold tailWord_2359827
  simp only [CollatzResearch.WordTrace]
  refine ⟨86069961621757280210141735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57379974414504853473427823 86069961621757280210141735)
  ·
    refine ⟨129104942432635920315212603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86069961621757280210141735 129104942432635920315212603)
    ·
      refine ⟨193657413648953880472818905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129104942432635920315212603 193657413648953880472818905)
      ·
        refine ⟨145243060236715410354614179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193657413648953880472818905 145243060236715410354614179)
        ·
          refine ⟨217864590355073115531921269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145243060236715410354614179 217864590355073115531921269)
          ·
            refine ⟨20424805345788104581117619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 217864590355073115531921269 20424805345788104581117619)
            ·
              refine ⟨30637208018682156871676429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20424805345788104581117619 30637208018682156871676429)
              ·
                refine ⟨11488953007005808826878661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30637208018682156871676429 11488953007005808826878661)
                ·
                  refine ⟨2154178688813589155039749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11488953007005808826878661 2154178688813589155039749)
                  ·
                    refine ⟨403908504152547966569953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2154178688813589155039749 403908504152547966569953)
                    ·
                      rfl

theorem cell23_2359827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 4].length) (baseStart_2359827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359827 prefixEnd_2359827 := by exact prefixLift 2359827
  have htrace : WordTrace (prefixWord ++ tailWord_2359827) baseStart_2359827 baseEnd_2359827 := by
    simpa [prefixWord, tailWord_2359827, baseEnd_2359827] using wordTrace_append hprefix tailTrace_2359827
  have hstable : (prefixWord ++ tailWord_2359827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359827).length < 2 ^ (prefixWord ++ tailWord_2359827).sum := by decide
  have hdescent : baseEnd_2359827 < baseStart_2359827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359828 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2359828 : Nat := 118140960795 + 2359828 * 2 ^ 59
def prefixEnd_2359828 : Nat := 4983230072969 + 3 ^ 40 * 2359828 * 2
def baseEnd_2359828 : Nat := 1211726025938298395797355

theorem tailTrace_2359828 : CollatzResearch.WordTrace tailWord_2359828 prefixEnd_2359828 1211726025938298395797355 := by
  unfold tailWord_2359828
  simp only [CollatzResearch.WordTrace]
  refine ⟨43034999047376828690464069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57379998729835771587285425 43034999047376828690464069)
  ·
    refine ⟨8069062321383155379462013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43034999047376828690464069 8069062321383155379462013)
    ·
      refine ⟨3025898370518683267298255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8069062321383155379462013 3025898370518683267298255)
      ·
        refine ⟨4538847555778024900947383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3025898370518683267298255 4538847555778024900947383)
        ·
          refine ⟨6808271333667037351421075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4538847555778024900947383 6808271333667037351421075)
          ·
            refine ⟨10212407000500556027131613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808271333667037351421075 10212407000500556027131613)
            ·
              refine ⟨3829652625187708510174355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10212407000500556027131613 3829652625187708510174355)
              ·
                refine ⟨5744478937781562765261533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3829652625187708510174355 5744478937781562765261533)
                ·
                  refine ⟨2154179601668086036973075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5744478937781562765261533 2154179601668086036973075)
                  ·
                    refine ⟨3231269402502129055459613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2154179601668086036973075 3231269402502129055459613)
                    ·
                      refine ⟨1211726025938298395797355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3231269402502129055459613 1211726025938298395797355)
                      ·
                        rfl

theorem cell23_2359828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2359828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359828 prefixEnd_2359828 := by exact prefixLift 2359828
  have htrace : WordTrace (prefixWord ++ tailWord_2359828) baseStart_2359828 baseEnd_2359828 := by
    simpa [prefixWord, tailWord_2359828, baseEnd_2359828] using wordTrace_append hprefix tailTrace_2359828
  have hstable : (prefixWord ++ tailWord_2359828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359828).length < 2 ^ (prefixWord ++ tailWord_2359828).sum := by decide
  have hdescent : baseEnd_2359828 < baseStart_2359828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359871 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 1, 2, 3]
def baseStart_2359871 : Nat := 118140960795 + 2359871 * 2 ^ 59
def prefixEnd_2359871 : Nat := 4983230072969 + 3 ^ 40 * 2359871 * 2
def baseEnd_2359871 : Nat := 1211748105606441727559657

theorem tailTrace_2359871 : CollatzResearch.WordTrace tailWord_2359871 prefixEnd_2359871 1211748105606441727559657 := by
  unfold tailWord_2359871
  simp only [CollatzResearch.WordTrace]
  refine ⟨86071566433597875724743467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57381044289065250483162311 86071566433597875724743467)
  ·
    refine ⟨129107349650396813587115201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86071566433597875724743467 129107349650396813587115201)
    ·
      refine ⟨96830512237797610190336401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129107349650396813587115201 96830512237797610190336401)
      ·
        refine ⟨72622884178348207642752301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96830512237797610190336401 72622884178348207642752301)
        ·
          refine ⟨27233581566880577866032113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72622884178348207642752301 27233581566880577866032113)
          ·
            refine ⟨20425186175160433399524085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27233581566880577866032113 20425186175160433399524085)
            ·
              refine ⟨1914861203921290631205383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20425186175160433399524085 1914861203921290631205383)
              ·
                refine ⟨2872291805881935946808075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914861203921290631205383 2872291805881935946808075)
                ·
                  refine ⟨4308437708822903920212113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2872291805881935946808075 4308437708822903920212113)
                  ·
                    refine ⟨3231328281617177940159085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4308437708822903920212113 3231328281617177940159085)
                    ·
                      refine ⟨1211748105606441727559657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3231328281617177940159085 1211748105606441727559657)
                      ·
                        rfl

theorem cell23_2359871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 1, 2, 3].length) (baseStart_2359871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359871 prefixEnd_2359871 := by exact prefixLift 2359871
  have htrace : WordTrace (prefixWord ++ tailWord_2359871) baseStart_2359871 baseEnd_2359871 := by
    simpa [prefixWord, tailWord_2359871, baseEnd_2359871] using wordTrace_append hprefix tailTrace_2359871
  have hstable : (prefixWord ++ tailWord_2359871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359871).length < 2 ^ (prefixWord ++ tailWord_2359871).sum := by decide
  have hdescent : baseEnd_2359871 < baseStart_2359871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359878 : List Nat := [6, 1, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_2359878 : Nat := 118140960795 + 2359878 * 2 ^ 59
def prefixEnd_2359878 : Nat := 4983230072969 + 3 ^ 40 * 2359878 * 2
def baseEnd_2359878 : Nat := 403917233323674400057375

theorem tailTrace_2359878 : CollatzResearch.WordTrace tailWord_2359878 prefixEnd_2359878 403917233323674400057375 := by
  unfold tailWord_2359878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689744429517891122507759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57381214496381677280165525 2689744429517891122507759)
  ·
    refine ⟨4034616644276836683761639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2689744429517891122507759 4034616644276836683761639)
    ·
      refine ⟨6051924966415255025642459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4034616644276836683761639 6051924966415255025642459)
      ·
        refine ⟨9077887449622882538463689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6051924966415255025642459 9077887449622882538463689)
        ·
          refine ⟨6808415587217161903847767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9077887449622882538463689 6808415587217161903847767)
          ·
            refine ⟨10212623380825742855771651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808415587217161903847767 10212623380825742855771651)
            ·
              refine ⟨15318935071238614283657477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10212623380825742855771651 15318935071238614283657477)
              ·
                refine ⟨2872300325857240178185777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15318935071238614283657477 2872300325857240178185777)
                ·
                  refine ⟨2154225244392930133639333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2872300325857240178185777 2154225244392930133639333)
                  ·
                    refine ⟨403917233323674400057375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2154225244392930133639333 403917233323674400057375)
                    ·
                      rfl

theorem cell23_2359878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_2359878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359878 prefixEnd_2359878 := by exact prefixLift 2359878
  have htrace : WordTrace (prefixWord ++ tailWord_2359878) baseStart_2359878 baseEnd_2359878 := by
    simpa [prefixWord, tailWord_2359878, baseEnd_2359878] using wordTrace_append hprefix tailTrace_2359878
  have hstable : (prefixWord ++ tailWord_2359878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359878).length < 2 ^ (prefixWord ++ tailWord_2359878).sum := by decide
  have hdescent : baseEnd_2359878 < baseStart_2359878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359907 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 4]
def baseStart_2359907 : Nat := 118140960795 + 2359907 * 2 ^ 59
def prefixEnd_2359907 : Nat := 4983230072969 + 3 ^ 40 * 2359907 * 2
def baseEnd_2359907 : Nat := 1211766590910003586709491

theorem tailTrace_2359907 : CollatzResearch.WordTrace tailWord_2359907 prefixEnd_2359907 1211766590910003586709491 := by
  unfold tailWord_2359907
  simp only [CollatzResearch.WordTrace]
  refine ⟨86072879461467453873053975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57381919640978302582035983 86072879461467453873053975)
  ·
    refine ⟨129109319192201180809580963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86072879461467453873053975 129109319192201180809580963)
    ·
      refine ⟨193663978788301771214371445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129109319192201180809580963 193663978788301771214371445)
      ·
        refine ⟨18155998011403291051347323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 193663978788301771214371445 18155998011403291051347323)
        ·
          refine ⟨27233997017104936577020985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18155998011403291051347323 27233997017104936577020985)
          ·
            refine ⟨20425497762828702432765739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27233997017104936577020985 20425497762828702432765739)
            ·
              refine ⟨30638246644243053649148609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20425497762828702432765739 30638246644243053649148609)
              ·
                refine ⟨22978684983182290236861457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30638246644243053649148609 22978684983182290236861457)
                ·
                  refine ⟨17234013737386717677646093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22978684983182290236861457 17234013737386717677646093)
                  ·
                    refine ⟨6462755151520019129117285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17234013737386717677646093 6462755151520019129117285)
                    ·
                      refine ⟨1211766590910003586709491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6462755151520019129117285 1211766590910003586709491)
                      ·
                        rfl

theorem cell23_2359907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_2359907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359907 prefixEnd_2359907 := by exact prefixLift 2359907
  have htrace : WordTrace (prefixWord ++ tailWord_2359907) baseStart_2359907 baseEnd_2359907 := by
    simpa [prefixWord, tailWord_2359907, baseEnd_2359907] using wordTrace_append hprefix tailTrace_2359907
  have hstable : (prefixWord ++ tailWord_2359907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359907).length < 2 ^ (prefixWord ++ tailWord_2359907).sum := by decide
  have hdescent : baseEnd_2359907 < baseStart_2359907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359911 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_2359911 : Nat := 118140960795 + 2359911 * 2 ^ 59
def prefixEnd_2359911 : Nat := 4983230072969 + 3 ^ 40 * 2359911 * 2
def baseEnd_2359911 : Nat := 1211768644832621571059473

theorem tailTrace_2359911 : CollatzResearch.WordTrace tailWord_2359911 prefixEnd_2359911 1211768644832621571059473 := by
  unfold tailWord_2359911
  simp only [CollatzResearch.WordTrace]
  refine ⟨86073025353452962556199587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57382016902301975037466391 86073025353452962556199587)
  ·
    refine ⟨129109538030179443834299381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86073025353452962556199587 129109538030179443834299381)
    ·
      refine ⟨12104019190329322859465567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129109538030179443834299381 12104019190329322859465567)
      ·
        refine ⟨18156028785493984289198351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12104019190329322859465567 18156028785493984289198351)
        ·
          refine ⟨27234043178240976433797527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18156028785493984289198351 27234043178240976433797527)
          ·
            refine ⟨40851064767361464650696291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27234043178240976433797527 40851064767361464650696291)
            ·
              refine ⟨61276597151042196976044437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40851064767361464650696291 61276597151042196976044437)
              ·
                refine ⟨2872340491455102983252083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61276597151042196976044437 2872340491455102983252083)
                ·
                  refine ⟨4308510737182654474878125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2872340491455102983252083 4308510737182654474878125)
                  ·
                    refine ⟨1615691526443495428079297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4308510737182654474878125 1615691526443495428079297)
                    ·
                      refine ⟨1211768644832621571059473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615691526443495428079297 1211768644832621571059473)
                      ·
                        rfl

theorem cell23_2359911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_2359911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359911 prefixEnd_2359911 := by exact prefixLift 2359911
  have htrace : WordTrace (prefixWord ++ tailWord_2359911) baseStart_2359911 baseEnd_2359911 := by
    simpa [prefixWord, tailWord_2359911, baseEnd_2359911] using wordTrace_append hprefix tailTrace_2359911
  have hstable : (prefixWord ++ tailWord_2359911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359911).length < 2 ^ (prefixWord ++ tailWord_2359911).sum := by decide
  have hdescent : baseEnd_2359911 < baseStart_2359911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359927 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_2359927 : Nat := 118140960795 + 2359927 * 2 ^ 59
def prefixEnd_2359927 : Nat := 4983230072969 + 3 ^ 40 * 2359927 * 2
def baseEnd_2359927 : Nat := 1211776860523093508459399

theorem tailTrace_2359927 : CollatzResearch.WordTrace tailWord_2359927 prefixEnd_2359927 1211776860523093508459399 := by
  unfold tailWord_2359927
  simp only [CollatzResearch.WordTrace]
  refine ⟨86073608921394997288782035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57382405947596664859188023 86073608921394997288782035)
  ·
    refine ⟨129110413382092495933173053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86073608921394997288782035 129110413382092495933173053)
    ·
      refine ⟨48416405018284685974939895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129110413382092495933173053 48416405018284685974939895)
      ·
        refine ⟨72624607527427028962409843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48416405018284685974939895 72624607527427028962409843)
        ·
          refine ⟨108936911291140543443614765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72624607527427028962409843 108936911291140543443614765)
          ·
            refine ⟨40851341734177703791355537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108936911291140543443614765 40851341734177703791355537)
            ·
              refine ⟨30638506300633277843516653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40851341734177703791355537 30638506300633277843516653)
              ·
                refine ⟨11489439862737479191318745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30638506300633277843516653 11489439862737479191318745)
                ·
                  refine ⟨8617079897053109393489059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11489439862737479191318745 8617079897053109393489059)
                  ·
                    refine ⟨12925619845579664090233589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8617079897053109393489059 12925619845579664090233589)
                    ·
                      refine ⟨1211776860523093508459399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12925619845579664090233589 1211776860523093508459399)
                      ·
                        rfl

theorem cell23_2359927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_2359927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359927 prefixEnd_2359927 := by exact prefixLift 2359927
  have htrace : WordTrace (prefixWord ++ tailWord_2359927) baseStart_2359927 baseEnd_2359927 := by
    simpa [prefixWord, tailWord_2359927, baseEnd_2359927] using wordTrace_append hprefix tailTrace_2359927
  have hstable : (prefixWord ++ tailWord_2359927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359927).length < 2 ^ (prefixWord ++ tailWord_2359927).sum := by decide
  have hdescent : baseEnd_2359927 < baseStart_2359927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359964 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 7]
def baseStart_2359964 : Nat := 118140960795 + 2359964 * 2 ^ 59
def prefixEnd_2359964 : Nat := 4983230072969 + 3 ^ 40 * 2359964 * 2
def baseEnd_2359964 : Nat := 134643984367478873744081

theorem tailTrace_2359964 : CollatzResearch.WordTrace tailWord_2359964 prefixEnd_2359964 134643984367478873744081 := by
  unfold tailWord_2359964
  simp only [CollatzResearch.WordTrace]
  refine ⟨43037479211130476303939473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57383305614840635071919297 43037479211130476303939473)
  ·
    refine ⟨32278109408347857227954605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43037479211130476303939473 32278109408347857227954605)
    ·
      refine ⟨12104291028130446460482977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32278109408347857227954605 12104291028130446460482977)
      ·
        refine ⟨9078218271097834845362233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12104291028130446460482977 9078218271097834845362233)
        ·
          refine ⟨6808663703323376134021675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9078218271097834845362233 6808663703323376134021675)
          ·
            refine ⟨10212995554985064201032513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808663703323376134021675 10212995554985064201032513)
            ·
              refine ⟨7659746666238798150774385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10212995554985064201032513 7659746666238798150774385)
              ·
                refine ⟨5744809999679098613080789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7659746666238798150774385 5744809999679098613080789)
                ·
                  refine ⟨134643984367478873744081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5744809999679098613080789 134643984367478873744081)
                  ·
                    rfl

theorem cell23_2359964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_2359964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359964 prefixEnd_2359964 := by exact prefixLift 2359964
  have htrace : WordTrace (prefixWord ++ tailWord_2359964) baseStart_2359964 baseEnd_2359964 := by
    simpa [prefixWord, tailWord_2359964, baseEnd_2359964] using wordTrace_append hprefix tailTrace_2359964
  have hstable : (prefixWord ++ tailWord_2359964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359964).length < 2 ^ (prefixWord ++ tailWord_2359964).sum := by decide
  have hdescent : baseEnd_2359964 < baseStart_2359964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359978 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2359978 : Nat := 118140960795 + 2359978 * 2 ^ 59
def prefixEnd_2359978 : Nat := 4983230072969 + 3 ^ 40 * 2359978 * 2
def baseEnd_2359978 : Nat := 1211803048036472808921665

theorem tailTrace_2359978 : CollatzResearch.WordTrace tailWord_2359978 prefixEnd_2359978 1211803048036472808921665 := by
  unfold tailWord_2359978
  simp only [CollatzResearch.WordTrace]
  refine ⟨21518867261052558249722147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57383646029473488665925725 21518867261052558249722147)
  ·
    refine ⟨32278300891578837374583221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21518867261052558249722147 32278300891578837374583221)
    ·
      refine ⟨3026090708585516003867177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32278300891578837374583221 3026090708585516003867177)
      ·
        refine ⟨2269568031439137002900383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3026090708585516003867177 2269568031439137002900383)
        ·
          refine ⟨3404352047158705504350575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2269568031439137002900383 3404352047158705504350575)
          ·
            refine ⟨5106528070738058256525863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3404352047158705504350575 5106528070738058256525863)
            ·
              refine ⟨7659792106107087384788795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5106528070738058256525863 7659792106107087384788795)
              ·
                refine ⟨11489688159160631077183193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7659792106107087384788795 11489688159160631077183193)
                ·
                  refine ⟨8617266119370473307887395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11489688159160631077183193 8617266119370473307887395)
                  ·
                    refine ⟨12925899179055709961831093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8617266119370473307887395 12925899179055709961831093)
                    ·
                      refine ⟨1211803048036472808921665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12925899179055709961831093 1211803048036472808921665)
                      ·
                        rfl

theorem cell23_2359978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2359978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359978 prefixEnd_2359978 := by exact prefixLift 2359978
  have htrace : WordTrace (prefixWord ++ tailWord_2359978) baseStart_2359978 baseEnd_2359978 := by
    simpa [prefixWord, tailWord_2359978, baseEnd_2359978] using wordTrace_append hprefix tailTrace_2359978
  have hstable : (prefixWord ++ tailWord_2359978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359978).length < 2 ^ (prefixWord ++ tailWord_2359978).sum := by decide
  have hdescent : baseEnd_2359978 < baseStart_2359978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359984 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 1, 7, 2]
def baseStart_2359984 : Nat := 118140960795 + 2359984 * 2 ^ 59
def prefixEnd_2359984 : Nat := 4983230072969 + 3 ^ 40 * 2359984 * 2
def baseEnd_2359984 : Nat := 1211806128920399785446637

theorem tailTrace_2359984 : CollatzResearch.WordTrace tailWord_2359984 prefixEnd_2359984 1211806128920399785446637 := by
  unfold tailWord_2359984
  simp only [CollatzResearch.WordTrace]
  refine ⟨43037843941094248011803503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57383791921458997349071337 43037843941094248011803503)
  ·
    refine ⟨64556765911641372017705255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43037843941094248011803503 64556765911641372017705255)
    ·
      refine ⟨96835148867462058026557883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64556765911641372017705255 96835148867462058026557883)
      ·
        refine ⟨145252723301193087039836825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96835148867462058026557883 145252723301193087039836825)
        ·
          refine ⟨108939542475894815279877619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145252723301193087039836825 108939542475894815279877619)
          ·
            refine ⟨163409313713842222919816429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108939542475894815279877619 163409313713842222919816429)
            ·
              refine ⟨61278492642690833594931161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163409313713842222919816429 61278492642690833594931161)
              ·
                refine ⟨45958869482018125196198371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61278492642690833594931161 45958869482018125196198371)
                ·
                  refine ⟨68938304223027187794297557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45958869482018125196198371 68938304223027187794297557)
                  ·
                    refine ⟨1615741505227199713928849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 68938304223027187794297557 1615741505227199713928849)
                    ·
                      refine ⟨1211806128920399785446637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615741505227199713928849 1211806128920399785446637)
                      ·
                        rfl

theorem cell23_2359984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 7, 2].length) (baseStart_2359984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359984 prefixEnd_2359984 := by exact prefixLift 2359984
  have htrace : WordTrace (prefixWord ++ tailWord_2359984) baseStart_2359984 baseEnd_2359984 := by
    simpa [prefixWord, tailWord_2359984, baseEnd_2359984] using wordTrace_append hprefix tailTrace_2359984
  have hstable : (prefixWord ++ tailWord_2359984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359984).length < 2 ^ (prefixWord ++ tailWord_2359984).sum := by decide
  have hdescent : baseEnd_2359984 < baseStart_2359984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359994 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 2, 5]
def baseStart_2359994 : Nat := 118140960795 + 2359994 * 2 ^ 59
def prefixEnd_2359994 : Nat := 4983230072969 + 3 ^ 40 * 2359994 * 2
def baseEnd_2359994 : Nat := 403937087908981582107197

theorem tailTrace_2359994 : CollatzResearch.WordTrace tailWord_2359994 prefixEnd_2359994 403937087908981582107197 := by
  unfold tailWord_2359994
  simp only [CollatzResearch.WordTrace]
  refine ⟨21519013153038066932867759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57384035074768178487647357 21519013153038066932867759)
  ·
    refine ⟨32278519729557100399301639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21519013153038066932867759 32278519729557100399301639)
    ·
      refine ⟨48417779594335650598952459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32278519729557100399301639 48417779594335650598952459)
      ·
        refine ⟨72626669391503475898428689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48417779594335650598952459 72626669391503475898428689)
        ·
          refine ⟨54470002043627606923821517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72626669391503475898428689 54470002043627606923821517)
          ·
            refine ⟨20426250766360352596433069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54470002043627606923821517 20426250766360352596433069)
            ·
              refine ⟨7659844037385132223662401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20426250766360352596433069 7659844037385132223662401)
              ·
                refine ⟨5744883028038849167746801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7659844037385132223662401 5744883028038849167746801)
                ·
                  refine ⟨4308662271029136875810101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5744883028038849167746801 4308662271029136875810101)
                  ·
                    refine ⟨403937087908981582107197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4308662271029136875810101 403937087908981582107197)
                    ·
                      rfl

theorem cell23_2359994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_2359994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359994 prefixEnd_2359994 := by exact prefixLift 2359994
  have htrace : WordTrace (prefixWord ++ tailWord_2359994) baseStart_2359994 baseEnd_2359994 := by
    simpa [prefixWord, tailWord_2359994, baseEnd_2359994] using wordTrace_append hprefix tailTrace_2359994
  have hstable : (prefixWord ++ tailWord_2359994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359994).length < 2 ^ (prefixWord ++ tailWord_2359994).sum := by decide
  have hdescent : baseEnd_2359994 < baseStart_2359994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2359998 : List Nat := [4, 2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_2359998 : Nat := 118140960795 + 2359998 * 2 ^ 59
def prefixEnd_2359998 : Nat := 4983230072969 + 3 ^ 40 * 2359998 * 2
def baseEnd_2359998 : Nat := 134645924183284747852397

theorem tailTrace_2359998 : CollatzResearch.WordTrace tailWord_2359998 prefixEnd_2359998 134645924183284747852397 := by
  unfold tailWord_2359998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10759524813017222051827081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57384132336091850943077765 10759524813017222051827081)
  ·
    refine ⟨8069643609762916538870311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10759524813017222051827081 8069643609762916538870311)
    ·
      refine ⟨12104465414644374808305467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8069643609762916538870311 12104465414644374808305467)
      ·
        refine ⟨18156698121966562212458201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12104465414644374808305467 18156698121966562212458201)
        ·
          refine ⟨13617523591474921659343651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18156698121966562212458201 13617523591474921659343651)
          ·
            refine ⟨20426285387212382489015477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13617523591474921659343651 20426285387212382489015477)
            ·
              refine ⟨1914964255051160858345201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20426285387212382489015477 1914964255051160858345201)
              ·
                refine ⟨1436223191288370643758901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1914964255051160858345201 1436223191288370643758901)
                ·
                  refine ⟨134645924183284747852397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1436223191288370643758901 134645924183284747852397)
                  ·
                    rfl

theorem cell23_2359998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_2359998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2359998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2359998 prefixEnd_2359998 := by exact prefixLift 2359998
  have htrace : WordTrace (prefixWord ++ tailWord_2359998) baseStart_2359998 baseEnd_2359998 := by
    simpa [prefixWord, tailWord_2359998, baseEnd_2359998] using wordTrace_append hprefix tailTrace_2359998
  have hstable : (prefixWord ++ tailWord_2359998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2359998).length < 2 ^ (prefixWord ++ tailWord_2359998).sum := by decide
  have hdescent : baseEnd_2359998 < baseStart_2359998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2359998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360004 : List Nat := [2, 3, 3, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2360004 : Nat := 118140960795 + 2360004 * 2 ^ 59
def prefixEnd_2360004 : Nat := 4983230072969 + 3 ^ 40 * 2360004 * 2
def baseEnd_2360004 : Nat := 1211816398533489707196545

theorem tailTrace_2360004 : CollatzResearch.WordTrace tailWord_2360004 prefixEnd_2360004 1211816398533489707196545 := by
  unfold tailWord_2360004
  simp only [CollatzResearch.WordTrace]
  refine ⟨43038208671058019719667533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57384278228077359626223377 43038208671058019719667533)
  ·
    refine ⟨16139328251646757394875325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43038208671058019719667533 16139328251646757394875325)
    ·
      refine ⟨6052248094367534023078247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16139328251646757394875325 6052248094367534023078247)
      ·
        refine ⟨9078372141551301034617371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6052248094367534023078247 9078372141551301034617371)
        ·
          refine ⟨13617558212326951551926057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9078372141551301034617371 13617558212326951551926057)
          ·
            refine ⟨10213168659245213663944543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13617558212326951551926057 10213168659245213663944543)
            ·
              refine ⟨15319752988867820495916815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10213168659245213663944543 15319752988867820495916815)
              ·
                refine ⟨22979629483301730743875223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15319752988867820495916815 22979629483301730743875223)
                ·
                  refine ⟨34469444224952596115812835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22979629483301730743875223 34469444224952596115812835)
                  ·
                    refine ⟨51704166337428894173719253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34469444224952596115812835 51704166337428894173719253)
                    ·
                      refine ⟨1211816398533489707196545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51704166337428894173719253 1211816398533489707196545)
                      ·
                        rfl

theorem cell23_2360004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2360004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360004 prefixEnd_2360004 := by exact prefixLift 2360004
  have htrace : WordTrace (prefixWord ++ tailWord_2360004) baseStart_2360004 baseEnd_2360004 := by
    simpa [prefixWord, tailWord_2360004, baseEnd_2360004] using wordTrace_append hprefix tailTrace_2360004
  have hstable : (prefixWord ++ tailWord_2360004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360004).length < 2 ^ (prefixWord ++ tailWord_2360004).sum := by decide
  have hdescent : baseEnd_2360004 < baseStart_2360004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360007 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 2, 8]
def baseStart_2360007 : Nat := 118140960795 + 2360007 * 2 ^ 59
def prefixEnd_2360007 : Nat := 4983230072969 + 3 ^ 40 * 2360007 * 2
def baseEnd_2360007 : Nat := 403939312991817731819677

theorem tailTrace_2360007 : CollatzResearch.WordTrace tailWord_2360007 prefixEnd_2360007 403939312991817731819677 := by
  unfold tailWord_2360007
  simp only [CollatzResearch.WordTrace]
  refine ⟨86076526761105170951694275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57384351174070113967796183 86076526761105170951694275)
  ·
    refine ⟨129114790141657756427541413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86076526761105170951694275 129114790141657756427541413)
    ·
      refine ⟨24209023151560829330164015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129114790141657756427541413 24209023151560829330164015)
      ·
        refine ⟨36313534727341243995246023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24209023151560829330164015 36313534727341243995246023)
        ·
          refine ⟨54470302091011865992869035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36313534727341243995246023 54470302091011865992869035)
          ·
            refine ⟨81705453136517798989303553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54470302091011865992869035 81705453136517798989303553)
            ·
              refine ⟨61279089852388349241977665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81705453136517798989303553 61279089852388349241977665)
              ·
                refine ⟨45959317389291261931483249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61279089852388349241977665 45959317389291261931483249)
                ·
                  refine ⟨34469488041968446448612437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45959317389291261931483249 34469488041968446448612437)
                  ·
                    refine ⟨403939312991817731819677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34469488041968446448612437 403939312991817731819677)
                    ·
                      rfl

theorem cell23_2360007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_2360007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360007 prefixEnd_2360007 := by exact prefixLift 2360007
  have htrace : WordTrace (prefixWord ++ tailWord_2360007) baseStart_2360007 baseEnd_2360007 := by
    simpa [prefixWord, tailWord_2360007, baseEnd_2360007] using wordTrace_append hprefix tailTrace_2360007
  have hstable : (prefixWord ++ tailWord_2360007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360007).length < 2 ^ (prefixWord ++ tailWord_2360007).sum := by decide
  have hdescent : baseEnd_2360007 < baseStart_2360007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360027 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 6]
def baseStart_2360027 : Nat := 118140960795 + 2360027 * 2 ^ 59
def prefixEnd_2360027 : Nat := 4983230072969 + 3 ^ 40 * 2360027 * 2
def baseEnd_2360027 : Nat := 1211828208588543117208939

theorem tailTrace_2360027 : CollatzResearch.WordTrace tailWord_2360027 prefixEnd_2360027 1211828208588543117208939 := by
  unfold tailWord_2360027
  simp only [CollatzResearch.WordTrace]
  refine ⟨86077256221032714367422335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57384837480688476244948223 86077256221032714367422335)
  ·
    refine ⟨129115884331549071551133503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86077256221032714367422335 129115884331549071551133503)
    ·
      refine ⟨193673826497323607326700255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129115884331549071551133503 193673826497323607326700255)
      ·
        refine ⟨290510739745985410990050383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193673826497323607326700255 290510739745985410990050383)
        ·
          refine ⟨435766109618978116485075575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290510739745985410990050383 435766109618978116485075575)
          ·
            refine ⟨653649164428467174727613363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435766109618978116485075575 653649164428467174727613363)
            ·
              refine ⟨980473746642700762091420045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653649164428467174727613363 980473746642700762091420045)
              ·
                refine ⟨367677654991012785784282517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 980473746642700762091420045 367677654991012785784282517)
                ·
                  refine ⟨17234890077703724333638243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 367677654991012785784282517 17234890077703724333638243)
                  ·
                    refine ⟨25852335116555586500457365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17234890077703724333638243 25852335116555586500457365)
                    ·
                      refine ⟨1211828208588543117208939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25852335116555586500457365 1211828208588543117208939)
                      ·
                        rfl

theorem cell23_2360027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 6].length) (baseStart_2360027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360027 prefixEnd_2360027 := by exact prefixLift 2360027
  have htrace : WordTrace (prefixWord ++ tailWord_2360027) baseStart_2360027 baseEnd_2360027 := by
    simpa [prefixWord, tailWord_2360027, baseEnd_2360027] using wordTrace_append hprefix tailTrace_2360027
  have hstable : (prefixWord ++ tailWord_2360027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360027).length < 2 ^ (prefixWord ++ tailWord_2360027).sum := by decide
  have hdescent : baseEnd_2360027 < baseStart_2360027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360028 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2360028 : Nat := 118140960795 + 2360028 * 2 ^ 59
def prefixEnd_2360028 : Nat := 4983230072969 + 3 ^ 40 * 2360028 * 2
def baseEnd_2360028 : Nat := 403942907356399204432145

theorem tailTrace_2360028 : CollatzResearch.WordTrace tailWord_2360028 prefixEnd_2360028 403942907356399204432145 := by
  unfold tailWord_2360028
  simp only [CollatzResearch.WordTrace]
  refine ⟨43038646347014545769104369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57384861796019394358805825 43038646347014545769104369)
  ·
    refine ⟨32278984760260909326828277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43038646347014545769104369 32278984760260909326828277)
    ·
      refine ⟨3026154821274460249390151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32278984760260909326828277 3026154821274460249390151)
      ·
        refine ⟨4539232231911690374085227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3026154821274460249390151 4539232231911690374085227)
        ·
          refine ⟨6808848347867535561127841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539232231911690374085227 6808848347867535561127841)
          ·
            refine ⟨5106636260900651670845881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6808848347867535561127841 5106636260900651670845881)
            ·
              refine ⟨3829977195675488753134411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5106636260900651670845881 3829977195675488753134411)
              ·
                refine ⟨5744965793513233129701617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3829977195675488753134411 5744965793513233129701617)
                ·
                  refine ⟨4308724345134924847276213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5744965793513233129701617 4308724345134924847276213)
                  ·
                    refine ⟨403942907356399204432145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4308724345134924847276213 403942907356399204432145)
                    ·
                      rfl

theorem cell23_2360028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2360028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360028 prefixEnd_2360028 := by exact prefixLift 2360028
  have htrace : WordTrace (prefixWord ++ tailWord_2360028) baseStart_2360028 baseEnd_2360028 := by
    simpa [prefixWord, tailWord_2360028, baseEnd_2360028] using wordTrace_append hprefix tailTrace_2360028
  have hstable : (prefixWord ++ tailWord_2360028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360028).length < 2 ^ (prefixWord ++ tailWord_2360028).sum := by decide
  have hdescent : baseEnd_2360028 < baseStart_2360028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360031 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 4]
def baseStart_2360031 : Nat := 118140960795 + 2360031 * 2 ^ 59
def prefixEnd_2360031 : Nat := 4983230072969 + 3 ^ 40 * 2360031 * 2
def baseEnd_2360031 : Nat := 1211830262511161101558921

theorem tailTrace_2360031 : CollatzResearch.WordTrace tailWord_2360031 prefixEnd_2360031 1211830262511161101558921 := by
  unfold tailWord_2360031
  simp only [CollatzResearch.WordTrace]
  refine ⟨86077402113018223050567947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57384934742012148700378631 86077402113018223050567947)
  ·
    refine ⟨129116103169527334575851921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86077402113018223050567947 129116103169527334575851921)
    ·
      refine ⟨96837077377145500931888941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129116103169527334575851921 96837077377145500931888941)
      ·
        refine ⟨36313904016429562849458353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96837077377145500931888941 36313904016429562849458353)
        ·
          refine ⟨27235428012322172137093765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36313904016429562849458353 27235428012322172137093765)
          ·
            refine ⟨5106642752310407275705081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27235428012322172137093765 5106642752310407275705081)
            ·
              refine ⟨3829982064232805456778811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5106642752310407275705081 3829982064232805456778811)
              ·
                refine ⟨5744973096349208185168217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3829982064232805456778811 5744973096349208185168217)
                ·
                  refine ⟨4308729822261906138876163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5744973096349208185168217 4308729822261906138876163)
                  ·
                    refine ⟨6463094733392859208314245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4308729822261906138876163 6463094733392859208314245)
                    ·
                      refine ⟨1211830262511161101558921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6463094733392859208314245 1211830262511161101558921)
                      ·
                        rfl

theorem cell23_2360031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_2360031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360031 prefixEnd_2360031 := by exact prefixLift 2360031
  have htrace : WordTrace (prefixWord ++ tailWord_2360031) baseStart_2360031 baseEnd_2360031 := by
    simpa [prefixWord, tailWord_2360031, baseEnd_2360031] using wordTrace_append hprefix tailTrace_2360031
  have hstable : (prefixWord ++ tailWord_2360031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360031).length < 2 ^ (prefixWord ++ tailWord_2360031).sum := by decide
  have hdescent : baseEnd_2360031 < baseStart_2360031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360071 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 6]
def baseStart_2360071 : Nat := 118140960795 + 2360071 * 2 ^ 59
def prefixEnd_2360071 : Nat := 4983230072969 + 3 ^ 40 * 2360071 * 2
def baseEnd_2360071 : Nat := 134650089081926771673193

theorem tailTrace_2360071 : CollatzResearch.WordTrace tailWord_2360071 prefixEnd_2360071 134650089081926771673193 := by
  unfold tailWord_2360071
  simp only [CollatzResearch.WordTrace]
  refine ⟨86078861032873309882024067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57385907355248873254682711 86078861032873309882024067)
  ·
    refine ⟨129118291549309964823036101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86078861032873309882024067 129118291549309964823036101)
    ·
      refine ⟨24209679665495618404319269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129118291549309964823036101 24209679665495618404319269)
      ·
        refine ⟨4539314937280428450809863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24209679665495618404319269 4539314937280428450809863)
        ·
          refine ⟨6808972405920642676214795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539314937280428450809863 6808972405920642676214795)
          ·
            refine ⟨10213458608880964014322193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808972405920642676214795 10213458608880964014322193)
            ·
              refine ⟨7660093956660723010741645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10213458608880964014322193 7660093956660723010741645)
              ·
                refine ⟨2872535233747771129028117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7660093956660723010741645 2872535233747771129028117)
                ·
                  refine ⟨134650089081926771673193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2872535233747771129028117 134650089081926771673193)
                  ·
                    rfl

theorem cell23_2360071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 6].length) (baseStart_2360071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360071 prefixEnd_2360071 := by exact prefixLift 2360071
  have htrace : WordTrace (prefixWord ++ tailWord_2360071) baseStart_2360071 baseEnd_2360071 := by
    simpa [prefixWord, tailWord_2360071, baseEnd_2360071] using wordTrace_append hprefix tailTrace_2360071
  have hstable : (prefixWord ++ tailWord_2360071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360071).length < 2 ^ (prefixWord ++ tailWord_2360071).sum := by decide
  have hdescent : baseEnd_2360071 < baseStart_2360071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360081 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 5, 1, 3]
def baseStart_2360081 : Nat := 118140960795 + 2360081 * 2 ^ 59
def prefixEnd_2360081 : Nat := 4983230072969 + 3 ^ 40 * 2360081 * 2
def baseEnd_2360081 : Nat := 1211855936543885905933691

theorem tailTrace_2360081 : CollatzResearch.WordTrace tailWord_2360081 prefixEnd_2360081 1211855936543885905933691 := by
  unfold tailWord_2360081
  simp only [CollatzResearch.WordTrace]
  refine ⟨86079225762837081589888097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57386150508558054393258731 86079225762837081589888097)
  ·
    refine ⟨64559419322127811192416073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86079225762837081589888097 64559419322127811192416073)
    ·
      refine ⟨48419564491595858394312055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64559419322127811192416073 48419564491595858394312055)
      ·
        refine ⟨72629346737393787591468083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48419564491595858394312055 72629346737393787591468083)
        ·
          refine ⟨108944020106090681387202125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72629346737393787591468083 108944020106090681387202125)
          ·
            refine ⟨40854007539784005520200797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 108944020106090681387202125 40854007539784005520200797)
            ·
              refine ⟨15320252827419002070075299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40854007539784005520200797 15320252827419002070075299)
              ·
                refine ⟨22980379241128503105112949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15320252827419002070075299 22980379241128503105112949)
                ·
                  refine ⟨2154410553855797166104339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22980379241128503105112949 2154410553855797166104339)
                  ·
                    refine ⟨3231615830783695749156509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2154410553855797166104339 3231615830783695749156509)
                    ·
                      refine ⟨1211855936543885905933691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3231615830783695749156509 1211855936543885905933691)
                      ·
                        rfl

theorem cell23_2360081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_2360081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360081 prefixEnd_2360081 := by exact prefixLift 2360081
  have htrace : WordTrace (prefixWord ++ tailWord_2360081) baseStart_2360081 baseEnd_2360081 := by
    simpa [prefixWord, tailWord_2360081, baseEnd_2360081] using wordTrace_append hprefix tailTrace_2360081
  have hstable : (prefixWord ++ tailWord_2360081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360081).length < 2 ^ (prefixWord ++ tailWord_2360081).sum := by decide
  have hdescent : baseEnd_2360081 < baseStart_2360081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360082 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_2360082 : Nat := 118140960795 + 2360082 * 2 ^ 59
def prefixEnd_2360082 : Nat := 4983230072969 + 3 ^ 40 * 2360082 * 2
def baseEnd_2360082 : Nat := 1211856450024540402021187

theorem tailTrace_2360082 : CollatzResearch.WordTrace tailWord_2360082 prefixEnd_2360082 1211856450024540402021187 := by
  unfold tailWord_2360082
  simp only [CollatzResearch.WordTrace]
  refine ⟨21519815558958364690168625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57386174823888972507116333 21519815558958364690168625)
  ·
    refine ⟨16139861669218773517626469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21519815558958364690168625 16139861669218773517626469)
    ·
      refine ⟨3026224062978520034554963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16139861669218773517626469 3026224062978520034554963)
      ·
        refine ⟨4539336094467780051832445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3026224062978520034554963 4539336094467780051832445)
        ·
          refine ⟨1702251035425417519437167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4539336094467780051832445 1702251035425417519437167)
          ·
            refine ⟨2553376553138126279155751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1702251035425417519437167 2553376553138126279155751)
            ·
              refine ⟨3830064829707189418733627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553376553138126279155751 3830064829707189418733627)
              ·
                refine ⟨5745097244560784128100441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830064829707189418733627 5745097244560784128100441)
                ·
                  refine ⟨4308822933420588096075331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5745097244560784128100441 4308822933420588096075331)
                  ·
                    refine ⟨6463234400130882144112997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4308822933420588096075331 6463234400130882144112997)
                    ·
                      refine ⟨1211856450024540402021187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6463234400130882144112997 1211856450024540402021187)
                      ·
                        rfl

theorem cell23_2360082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_2360082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360082 prefixEnd_2360082 := by exact prefixLift 2360082
  have htrace : WordTrace (prefixWord ++ tailWord_2360082) baseStart_2360082 baseEnd_2360082 := by
    simpa [prefixWord, tailWord_2360082, baseEnd_2360082] using wordTrace_append hprefix tailTrace_2360082
  have hstable : (prefixWord ++ tailWord_2360082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360082).length < 2 ^ (prefixWord ++ tailWord_2360082).sum := by decide
  have hdescent : baseEnd_2360082 < baseStart_2360082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360101 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 1, 5]
def baseStart_2360101 : Nat := 118140960795 + 2360101 * 2 ^ 59
def prefixEnd_2360101 : Nat := 4983230072969 + 3 ^ 40 * 2360101 * 2
def baseEnd_2360101 : Nat := 403955402052325275894533

theorem tailTrace_2360101 : CollatzResearch.WordTrace tailWord_2360101 prefixEnd_2360101 403955402052325275894533 := by
  unfold tailWord_2360101
  simp only [CollatzResearch.WordTrace]
  refine ⟨86079955222764625005616157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57386636815176416670410771 86079955222764625005616157)
  ·
    refine ⟨32279983208536734377106059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86079955222764625005616157 32279983208536734377106059)
    ·
      refine ⟨48419974812805101565659089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32279983208536734377106059 48419974812805101565659089)
      ·
        refine ⟨36314981109603826174244317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48419974812805101565659089 36314981109603826174244317)
        ·
          refine ⟨13618117916101434815341619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36314981109603826174244317 13618117916101434815341619)
          ·
            refine ⟨20427176874152152223012429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13618117916101434815341619 20427176874152152223012429)
            ·
              refine ⟨7660191327807057083629661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20427176874152152223012429 7660191327807057083629661)
              ·
                refine ⟨2872571747927646406361123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7660191327807057083629661 2872571747927646406361123)
                ·
                  refine ⟨4308857621891469609541685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2872571747927646406361123 4308857621891469609541685)
                  ·
                    refine ⟨403955402052325275894533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4308857621891469609541685 403955402052325275894533)
                    ·
                      rfl

theorem cell23_2360101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 5].length) (baseStart_2360101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360101 prefixEnd_2360101 := by exact prefixLift 2360101
  have htrace : WordTrace (prefixWord ++ tailWord_2360101) baseStart_2360101 baseEnd_2360101 := by
    simpa [prefixWord, tailWord_2360101, baseEnd_2360101] using wordTrace_append hprefix tailTrace_2360101
  have hstable : (prefixWord ++ tailWord_2360101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360101).length < 2 ^ (prefixWord ++ tailWord_2360101).sum := by decide
  have hdescent : baseEnd_2360101 < baseStart_2360101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360115 : List Nat := [1, 1, 1, 2, 6, 1, 2, 4, 1, 1, 3]
def baseStart_2360115 : Nat := 118140960795 + 2360115 * 2 ^ 59
def prefixEnd_2360115 : Nat := 4983230072969 + 3 ^ 40 * 2360115 * 2
def baseEnd_2360115 : Nat := 1211873394886138772908535

theorem tailTrace_2360115 : CollatzResearch.WordTrace tailWord_2360115 prefixEnd_2360115 1211873394886138772908535 := by
  unfold tailWord_2360115
  simp only [CollatzResearch.WordTrace]
  refine ⟨86080465844713905396625799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57386977229809270264417199 86080465844713905396625799)
  ·
    refine ⟨129120698767070858094938699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86080465844713905396625799 129120698767070858094938699)
    ·
      refine ⟨193681048150606287142408049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129120698767070858094938699 193681048150606287142408049)
      ·
        refine ⟨145260786112954715356806037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193681048150606287142408049 145260786112954715356806037)
        ·
          refine ⟨6809099349044752282350283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145260786112954715356806037 6809099349044752282350283)
          ·
            refine ⟨10213649023567128423525425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809099349044752282350283 10213649023567128423525425)
            ·
              refine ⟨7660236767675346317644069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10213649023567128423525425 7660236767675346317644069)
              ·
                refine ⟨1436294393939127434558263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7660236767675346317644069 1436294393939127434558263)
                ·
                  refine ⟨2154441590908691151837395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436294393939127434558263 2154441590908691151837395)
                  ·
                    refine ⟨3231662386363036727756093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2154441590908691151837395 3231662386363036727756093)
                    ·
                      refine ⟨1211873394886138772908535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3231662386363036727756093 1211873394886138772908535)
                      ·
                        rfl

theorem cell23_2360115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 1, 1, 3].length) (baseStart_2360115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360115 prefixEnd_2360115 := by exact prefixLift 2360115
  have htrace : WordTrace (prefixWord ++ tailWord_2360115) baseStart_2360115 baseEnd_2360115 := by
    simpa [prefixWord, tailWord_2360115, baseEnd_2360115] using wordTrace_append hprefix tailTrace_2360115
  have hstable : (prefixWord ++ tailWord_2360115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360115).length < 2 ^ (prefixWord ++ tailWord_2360115).sum := by decide
  have hdescent : baseEnd_2360115 < baseStart_2360115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360138 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2]
def baseStart_2360138 : Nat := 118140960795 + 2360138 * 2 ^ 59
def prefixEnd_2360138 : Nat := 4983230072969 + 3 ^ 40 * 2360138 * 2
def baseEnd_2360138 : Nat := 1211885204941192182920929

theorem tailTrace_2360138 : CollatzResearch.WordTrace tailWord_2360138 prefixEnd_2360138 1211885204941192182920929 := by
  unfold tailWord_2360138
  simp only [CollatzResearch.WordTrace]
  refine ⟨21520326180907645081178267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57387536482420386883142045 21520326180907645081178267)
  ·
    refine ⟨32280489271361467621767401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21520326180907645081178267 32280489271361467621767401)
    ·
      refine ⟨24210366953521100716325551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32280489271361467621767401 24210366953521100716325551)
      ·
        refine ⟨36315550430281651074488327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24210366953521100716325551 36315550430281651074488327)
        ·
          refine ⟨54473325645422476611732491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36315550430281651074488327 54473325645422476611732491)
          ·
            refine ⟨81709988468133714917598737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54473325645422476611732491 81709988468133714917598737)
            ·
              refine ⟨61282491351100286188199053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81709988468133714917598737 61282491351100286188199053)
              ·
                refine ⟨22980934256662607320574645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61282491351100286188199053 22980934256662607320574645)
                ·
                  refine ⟨2154462586562119436303873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22980934256662607320574645 2154462586562119436303873)
                  ·
                    refine ⟨1615846939921589577227905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2154462586562119436303873 1615846939921589577227905)
                    ·
                      refine ⟨1211885204941192182920929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615846939921589577227905 1211885204941192182920929)
                      ·
                        rfl

theorem cell23_2360138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_2360138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360138 prefixEnd_2360138 := by exact prefixLift 2360138
  have htrace : WordTrace (prefixWord ++ tailWord_2360138) baseStart_2360138 baseEnd_2360138 := by
    simpa [prefixWord, tailWord_2360138, baseEnd_2360138] using wordTrace_append hprefix tailTrace_2360138
  have hstable : (prefixWord ++ tailWord_2360138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360138).length < 2 ^ (prefixWord ++ tailWord_2360138).sum := by decide
  have hdescent : baseEnd_2360138 < baseStart_2360138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360182 : List Nat := [5, 1, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_2360182 : Nat := 118140960795 + 2360182 * 2 ^ 59
def prefixEnd_2360182 : Nat := 4983230072969 + 3 ^ 40 * 2360182 * 2
def baseEnd_2360182 : Nat := 403969266029996670256909

theorem tailTrace_2360182 : CollatzResearch.WordTrace tailWord_2360182 prefixEnd_2360182 403969266029996670256909 := by
  unfold tailWord_2360182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5380181845966948489957175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57388606356980783892876533 5380181845966948489957175)
  ·
    refine ⟨8070272768950422734935763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5380181845966948489957175 8070272768950422734935763)
    ·
      refine ⟨12105409153425634102403645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8070272768950422734935763 12105409153425634102403645)
      ·
        refine ⟨4539528432534612788401367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12105409153425634102403645 4539528432534612788401367)
        ·
          refine ⟨6809292648801919182602051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539528432534612788401367 6809292648801919182602051)
          ·
            refine ⟨10213938973202878773903077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809292648801919182602051 10213938973202878773903077)
            ·
              refine ⟨1915113557475539770106827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10213938973202878773903077 1915113557475539770106827)
              ·
                refine ⟨2872670336213309655160241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1915113557475539770106827 2872670336213309655160241)
                ·
                  refine ⟨2154502752159982241370181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2872670336213309655160241 2154502752159982241370181)
                  ·
                    refine ⟨403969266029996670256909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2154502752159982241370181 403969266029996670256909)
                    ·
                      rfl

theorem cell23_2360182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_2360182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360182 prefixEnd_2360182 := by exact prefixLift 2360182
  have htrace : WordTrace (prefixWord ++ tailWord_2360182) baseStart_2360182 baseEnd_2360182 := by
    simpa [prefixWord, tailWord_2360182, baseEnd_2360182] using wordTrace_append hprefix tailTrace_2360182
  have hstable : (prefixWord ++ tailWord_2360182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360182).length < 2 ^ (prefixWord ++ tailWord_2360182).sum := by decide
  have hdescent : baseEnd_2360182 < baseStart_2360182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360184 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_2360184 : Nat := 118140960795 + 2360184 * 2 ^ 59
def prefixEnd_2360184 : Nat := 4983230072969 + 3 ^ 40 * 2360184 * 2
def baseEnd_2360184 : Nat := 1211908825051299002945717

theorem tailTrace_2360184 : CollatzResearch.WordTrace tailWord_2360184 prefixEnd_2360184 1211908825051299002945717 := by
  unfold tailWord_2360184
  simp only [CollatzResearch.WordTrace]
  refine ⟨43041491240731965090443803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57388654987642620120591737 43041491240731965090443803)
  ·
    refine ⟨64562236861097947635665705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43041491240731965090443803 64562236861097947635665705)
    ·
      refine ⟨48421677645823460726749279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64562236861097947635665705 48421677645823460726749279)
      ·
        refine ⟨72632516468735191090123919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48421677645823460726749279 72632516468735191090123919)
        ·
          refine ⟨108948774703102786635185879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72632516468735191090123919 108948774703102786635185879)
          ·
            refine ⟨163423162054654179952778819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108948774703102786635185879 163423162054654179952778819)
            ·
              refine ⟨245134743081981269929168229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163423162054654179952778819 245134743081981269929168229)
              ·
                refine ⟨45962764327871488111719043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 245134743081981269929168229 45962764327871488111719043)
                ·
                  refine ⟨68944146491807232167578565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45962764327871488111719043 68944146491807232167578565)
                  ·
                    refine ⟨12927027467213856031420981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 68944146491807232167578565 12927027467213856031420981)
                    ·
                      refine ⟨1211908825051299002945717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12927027467213856031420981 1211908825051299002945717)
                      ·
                        rfl

theorem cell23_2360184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_2360184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360184 prefixEnd_2360184 := by exact prefixLift 2360184
  have htrace : WordTrace (prefixWord ++ tailWord_2360184) baseStart_2360184 baseEnd_2360184 := by
    simpa [prefixWord, tailWord_2360184, baseEnd_2360184] using wordTrace_append hprefix tailTrace_2360184
  have hstable : (prefixWord ++ tailWord_2360184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360184).length < 2 ^ (prefixWord ++ tailWord_2360184).sum := by decide
  have hdescent : baseEnd_2360184 < baseStart_2360184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360221 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_2360221 : Nat := 118140960795 + 2360221 * 2 ^ 59
def prefixEnd_2360221 : Nat := 4983230072969 + 3 ^ 40 * 2360221 * 2
def baseEnd_2360221 : Nat := 403975941278505119394349

theorem tailTrace_2360221 : CollatzResearch.WordTrace tailWord_2360221 prefixEnd_2360221 403975941278505119394349 := by
  unfold tailWord_2360221
  simp only [CollatzResearch.WordTrace]
  refine ⟨86084331982329885499984517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57389554654886590333323011 86084331982329885499984517)
  ·
    refine ⟨16140812246686853531247097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86084331982329885499984517 16140812246686853531247097)
    ·
      refine ⟨12105609185015140148435323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16140812246686853531247097 12105609185015140148435323)
      ·
        refine ⟨18158413777522710222652985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12105609185015140148435323 18158413777522710222652985)
        ·
          refine ⟨13618810333142032666989739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18158413777522710222652985 13618810333142032666989739)
          ·
            refine ⟨20428215499713049000484609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13618810333142032666989739 20428215499713049000484609)
            ·
              refine ⟨15321161624784786750363457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20428215499713049000484609 15321161624784786750363457)
              ·
                refine ⟨11490871218588590062772593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15321161624784786750363457 11490871218588590062772593)
                ·
                  refine ⟨8618153413941442547079445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11490871218588590062772593 8618153413941442547079445)
                  ·
                    refine ⟨403975941278505119394349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8618153413941442547079445 403975941278505119394349)
                    ·
                      rfl

theorem cell23_2360221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_2360221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360221 prefixEnd_2360221 := by exact prefixLift 2360221
  have htrace : WordTrace (prefixWord ++ tailWord_2360221) baseStart_2360221 baseEnd_2360221 := by
    simpa [prefixWord, tailWord_2360221, baseEnd_2360221] using wordTrace_append hprefix tailTrace_2360221
  have hstable : (prefixWord ++ tailWord_2360221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360221).length < 2 ^ (prefixWord ++ tailWord_2360221).sum := by decide
  have hdescent : baseEnd_2360221 < baseStart_2360221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360228 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 3, 4, 2]
def baseStart_2360228 : Nat := 118140960795 + 2360228 * 2 ^ 59
def prefixEnd_2360228 : Nat := 4983230072969 + 3 ^ 40 * 2360228 * 2
def baseEnd_2360228 : Nat := 1211931418200096830795515

theorem tailTrace_2360228 : CollatzResearch.WordTrace tailWord_2360228 prefixEnd_2360228 1211931418200096830795515 := by
  unfold tailWord_2360228
  simp only [CollatzResearch.WordTrace]
  refine ⟨43042293646652262847744669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57389724862203017130326225 43042293646652262847744669)
  ·
    refine ⟨16140860117494598567904251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43042293646652262847744669 16140860117494598567904251)
    ·
      refine ⟨24211290176241897851856377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16140860117494598567904251 24211290176241897851856377)
      ·
        refine ⟨18158467632181423388892283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24211290176241897851856377 18158467632181423388892283)
        ·
          refine ⟨27237701448272135083338425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18158467632181423388892283 27237701448272135083338425)
          ·
            refine ⟨20428276086204101312503819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27237701448272135083338425 20428276086204101312503819)
            ·
              refine ⟨30642414129306151968755729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20428276086204101312503819 30642414129306151968755729)
              ·
                refine ⟨22981810596979613976566797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30642414129306151968755729 22981810596979613976566797)
                ·
                  refine ⟨8618178973867355241212549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22981810596979613976566797 8618178973867355241212549)
                  ·
                    refine ⟨1615908557600129107727353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8618178973867355241212549 1615908557600129107727353)
                    ·
                      refine ⟨1211931418200096830795515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615908557600129107727353 1211931418200096830795515)
                      ·
                        rfl

theorem cell23_2360228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_2360228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360228 prefixEnd_2360228 := by exact prefixLift 2360228
  have htrace : WordTrace (prefixWord ++ tailWord_2360228) baseStart_2360228 baseEnd_2360228 := by
    simpa [prefixWord, tailWord_2360228, baseEnd_2360228] using wordTrace_append hprefix tailTrace_2360228
  have hstable : (prefixWord ++ tailWord_2360228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360228).length < 2 ^ (prefixWord ++ tailWord_2360228).sum := by decide
  have hdescent : baseEnd_2360228 < baseStart_2360228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360245 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_2360245 : Nat := 118140960795 + 2360245 * 2 ^ 59
def prefixEnd_2360245 : Nat := 4983230072969 + 3 ^ 40 * 2360245 * 2
def baseEnd_2360245 : Nat := 1211940147371223264282937

theorem tailTrace_2360245 : CollatzResearch.WordTrace tailWord_2360245 prefixEnd_2360245 1211940147371223264282937 := by
  unfold tailWord_2360245
  simp only [CollatzResearch.WordTrace]
  refine ⟨86085207334242937598858189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57390138222828625065905459 86085207334242937598858189)
  ·
    refine ⟨32281952750341101599571821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86085207334242937598858189 32281952750341101599571821)
    ·
      refine ⟨12105732281377913099839433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32281952750341101599571821 12105732281377913099839433)
      ·
        refine ⟨9079299211033434824879575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12105732281377913099839433 9079299211033434824879575)
        ·
          refine ⟨13618948816550152237319363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9079299211033434824879575 13618948816550152237319363)
          ·
            refine ⟨20428423224825228355979045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13618948816550152237319363 20428423224825228355979045)
            ·
              refine ⟨3830329354654730316746071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20428423224825228355979045 3830329354654730316746071)
              ·
                refine ⟨5745494031982095475119107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830329354654730316746071 5745494031982095475119107)
                ·
                  refine ⟨8618241047973143212678661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5745494031982095475119107 8618241047973143212678661)
                  ·
                    refine ⟨1615920196494964352377249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8618241047973143212678661 1615920196494964352377249)
                    ·
                      refine ⟨1211940147371223264282937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1615920196494964352377249 1211940147371223264282937)
                      ·
                        rfl

theorem cell23_2360245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_2360245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360245 prefixEnd_2360245 := by exact prefixLift 2360245
  have htrace : WordTrace (prefixWord ++ tailWord_2360245) baseStart_2360245 baseEnd_2360245 := by
    simpa [prefixWord, tailWord_2360245, baseEnd_2360245] using wordTrace_append hprefix tailTrace_2360245
  have hstable : (prefixWord ++ tailWord_2360245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360245).length < 2 ^ (prefixWord ++ tailWord_2360245).sum := by decide
  have hdescent : baseEnd_2360245 < baseStart_2360245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360285 : List Nat := [1, 4, 3, 1, 2, 1, 2, 4, 5]
def baseStart_2360285 : Nat := 118140960795 + 2360285 * 2 ^ 59
def prefixEnd_2360285 : Nat := 4983230072969 + 3 ^ 40 * 2360285 * 2
def baseEnd_2360285 : Nat := 134662298510822567531417

theorem tailTrace_2360285 : CollatzResearch.WordTrace tailWord_2360285 prefixEnd_2360285 134662298510822567531417 := by
  unfold tailWord_2360285
  simp only [CollatzResearch.WordTrace]
  refine ⟨86086666254098024430314309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57391110836065349620209539 86086666254098024430314309)
  ·
    refine ⟨16141249922643379580683933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86086666254098024430314309 16141249922643379580683933)
    ·
      refine ⟨6052968720991267342756475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16141249922643379580683933 6052968720991267342756475)
      ·
        refine ⟨9079453081486901014134713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6052968720991267342756475 9079453081486901014134713)
        ·
          refine ⟨6809589811115175760601035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9079453081486901014134713 6809589811115175760601035)
          ·
            refine ⟨10214384716672763640901553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809589811115175760601035 10214384716672763640901553)
            ·
              refine ⟨7660788537504572730676165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10214384716672763640901553 7660788537504572730676165)
              ·
                refine ⟨1436397850782107387001781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7660788537504572730676165 1436397850782107387001781)
                ·
                  refine ⟨134662298510822567531417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1436397850782107387001781 134662298510822567531417)
                  ·
                    rfl

theorem cell23_2360285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_2360285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360285 prefixEnd_2360285 := by exact prefixLift 2360285
  have htrace : WordTrace (prefixWord ++ tailWord_2360285) baseStart_2360285 baseEnd_2360285 := by
    simpa [prefixWord, tailWord_2360285, baseEnd_2360285] using wordTrace_append hprefix tailTrace_2360285
  have hstable : (prefixWord ++ tailWord_2360285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360285).length < 2 ^ (prefixWord ++ tailWord_2360285).sum := by decide
  have hdescent : baseEnd_2360285 < baseStart_2360285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360291 : List Nat := [1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2360291 : Nat := 118140960795 + 2360291 * 2 ^ 59
def prefixEnd_2360291 : Nat := 4983230072969 + 3 ^ 40 * 2360291 * 2
def baseEnd_2360291 : Nat := 1211963767481330084307725

theorem tailTrace_2360291 : CollatzResearch.WordTrace tailWord_2360291 prefixEnd_2360291 1211963767481330084307725 := by
  unfold tailWord_2360291
  simp only [CollatzResearch.WordTrace]
  refine ⟨86086885092076287455032727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57391256728050858303355151 86086885092076287455032727)
  ·
    refine ⟨129130327638114431182549091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86086885092076287455032727 129130327638114431182549091)
    ·
      refine ⟨193695491457171646773823637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129130327638114431182549091 193695491457171646773823637)
      ·
        refine ⟨9079476162054920942522983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 193695491457171646773823637 9079476162054920942522983)
        ·
          refine ⟨13619214243082381413784475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9079476162054920942522983 13619214243082381413784475)
          ·
            refine ⟨20428821364623572120676713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13619214243082381413784475 20428821364623572120676713)
            ·
              refine ⟨15321616023467679090507535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20428821364623572120676713 15321616023467679090507535)
              ·
                refine ⟨22982424035201518635761303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15321616023467679090507535 22982424035201518635761303)
                ·
                  refine ⟨34473636052802277953641955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22982424035201518635761303 34473636052802277953641955)
                  ·
                    refine ⟨51710454079203416930462933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34473636052802277953641955 51710454079203416930462933)
                    ·
                      refine ⟨1211963767481330084307725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51710454079203416930462933 1211963767481330084307725)
                      ·
                        rfl

theorem cell23_2360291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2360291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360291 prefixEnd_2360291 := by exact prefixLift 2360291
  have htrace : WordTrace (prefixWord ++ tailWord_2360291) baseStart_2360291 baseEnd_2360291 := by
    simpa [prefixWord, tailWord_2360291, baseEnd_2360291] using wordTrace_append hprefix tailTrace_2360291
  have hstable : (prefixWord ++ tailWord_2360291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360291).length < 2 ^ (prefixWord ++ tailWord_2360291).sum := by decide
  have hdescent : baseEnd_2360291 < baseStart_2360291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360345 : List Nat := [1, 2, 1, 2, 1, 1, 4, 6, 1, 4]
def baseStart_2360345 : Nat := 118140960795 + 2360345 * 2 ^ 59
def prefixEnd_2360345 : Nat := 4983230072969 + 3 ^ 40 * 2360345 * 2
def baseEnd_2360345 : Nat := 403997165145557624344159

theorem tailTrace_2360345 : CollatzResearch.WordTrace tailWord_2360345 prefixEnd_2360345 403997165145557624344159 := by
  unfold tailWord_2360345
  simp only [CollatzResearch.WordTrace]
  refine ⟨86088854633880654677498489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57392569755920436451665659 86088854633880654677498489)
  ·
    refine ⟨64566640975410491008123867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86088854633880654677498489 64566640975410491008123867)
    ·
      refine ⟨96849961463115736512185801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64566640975410491008123867 96849961463115736512185801)
      ·
        refine ⟨72637471097336802384139351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96849961463115736512185801 72637471097336802384139351)
        ·
          refine ⟨108956206646005203576209027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72637471097336802384139351 108956206646005203576209027)
          ·
            refine ⟨163434309969007805364313541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108956206646005203576209027 163434309969007805364313541)
            ·
              refine ⟨30643933119188963505808789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163434309969007805364313541 30643933119188963505808789)
              ·
                refine ⟨1436434364961982664334787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30643933119188963505808789 1436434364961982664334787)
                ·
                  refine ⟨2154651547442973996502181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436434364961982664334787 2154651547442973996502181)
                  ·
                    refine ⟨403997165145557624344159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2154651547442973996502181 403997165145557624344159)
                    ·
                      rfl

theorem cell23_2360345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 1, 4].length) (baseStart_2360345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360345 prefixEnd_2360345 := by exact prefixLift 2360345
  have htrace : WordTrace (prefixWord ++ tailWord_2360345) baseStart_2360345 baseEnd_2360345 := by
    simpa [prefixWord, tailWord_2360345, baseEnd_2360345] using wordTrace_append hprefix tailTrace_2360345
  have hstable : (prefixWord ++ tailWord_2360345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360345).length < 2 ^ (prefixWord ++ tailWord_2360345).sum := by decide
  have hdescent : baseEnd_2360345 < baseStart_2360345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360372 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_2360372 : Nat := 118140960795 + 2360372 * 2 ^ 59
def prefixEnd_2360372 : Nat := 4983230072969 + 3 ^ 40 * 2360372 * 2
def baseEnd_2360372 : Nat := 1212005359414344267394853

theorem tailTrace_2360372 : CollatzResearch.WordTrace tailWord_2360372 prefixEnd_2360372 1212005359414344267394853 := by
  unfold tailWord_2360372
  simp only [CollatzResearch.WordTrace]
  refine ⟨43044919702391419144365685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57393226269855225525820913 43044919702391419144365685)
  ·
    refine ⟨4035461222099195544784283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43044919702391419144365685 4035461222099195544784283)
    ·
      refine ⟨6053191833148793317176425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4035461222099195544784283 6053191833148793317176425)
      ·
        refine ⟨4539893874861594987882319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6053191833148793317176425 4539893874861594987882319)
        ·
          refine ⟨6809840812292392481823479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539893874861594987882319 6809840812292392481823479)
          ·
            refine ⟨10214761218438588722735219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6809840812292392481823479 10214761218438588722735219)
            ·
              refine ⟨15322141827657883084102829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10214761218438588722735219 15322141827657883084102829)
              ·
                refine ⟨5745803185371706156538561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15322141827657883084102829 5745803185371706156538561)
                ·
                  refine ⟨4309352389028779617403921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5745803185371706156538561 4309352389028779617403921)
                  ·
                    refine ⟨3232014291771584713052941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4309352389028779617403921 3232014291771584713052941)
                    ·
                      refine ⟨1212005359414344267394853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3232014291771584713052941 1212005359414344267394853)
                      ·
                        rfl

theorem cell23_2360372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_2360372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360372 prefixEnd_2360372 := by exact prefixLift 2360372
  have htrace : WordTrace (prefixWord ++ tailWord_2360372) baseStart_2360372 baseEnd_2360372 := by
    simpa [prefixWord, tailWord_2360372, baseEnd_2360372] using wordTrace_append hprefix tailTrace_2360372
  have hstable : (prefixWord ++ tailWord_2360372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360372).length < 2 ^ (prefixWord ++ tailWord_2360372).sum := by decide
  have hdescent : baseEnd_2360372 < baseStart_2360372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360408 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_2360408 : Nat := 118140960795 + 2360408 * 2 ^ 59
def prefixEnd_2360408 : Nat := 4983230072969 + 3 ^ 40 * 2360408 * 2
def baseEnd_2360408 : Nat := 1212023844717906126544687

theorem tailTrace_2360408 : CollatzResearch.WordTrace tailWord_2360408 prefixEnd_2360408 1212023844717906126544687 := by
  unfold tailWord_2360408
  simp only [CollatzResearch.WordTrace]
  refine ⟨43045576216326208218520939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57394101621768277624694585 43045576216326208218520939)
  ·
    refine ⟨64568364324489312327781409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43045576216326208218520939 64568364324489312327781409)
    ·
      refine ⟨48426273243366984245836057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64568364324489312327781409 48426273243366984245836057)
      ·
        refine ⟨36319704932525238184377043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48426273243366984245836057 36319704932525238184377043)
        ·
          refine ⟨54479557398787857276565565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36319704932525238184377043 54479557398787857276565565)
          ·
            refine ⟨20429834024545446478712087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54479557398787857276565565 20429834024545446478712087)
            ·
              refine ⟨30644751036818169718068131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20429834024545446478712087 30644751036818169718068131)
              ·
                refine ⟨45967126555227254577102197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30644751036818169718068131 45967126555227254577102197)
                ·
                  refine ⟨4309418114552555116603331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45967126555227254577102197 4309418114552555116603331)
                  ·
                    refine ⟨6464127171828832674904997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4309418114552555116603331 6464127171828832674904997)
                    ·
                      refine ⟨1212023844717906126544687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6464127171828832674904997 1212023844717906126544687)
                      ·
                        rfl

theorem cell23_2360408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_2360408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360408 prefixEnd_2360408 := by exact prefixLift 2360408
  have htrace : WordTrace (prefixWord ++ tailWord_2360408) baseStart_2360408 baseEnd_2360408 := by
    simpa [prefixWord, tailWord_2360408, baseEnd_2360408] using wordTrace_append hprefix tailTrace_2360408
  have hstable : (prefixWord ++ tailWord_2360408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360408).length < 2 ^ (prefixWord ++ tailWord_2360408).sum := by decide
  have hdescent : baseEnd_2360408 < baseStart_2360408 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360429 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_2360429 : Nat := 118140960795 + 2360429 * 2 ^ 59
def prefixEnd_2360429 : Nat := 4983230072969 + 3 ^ 40 * 2360429 * 2
def baseEnd_2360429 : Nat := 1212034627811650544382091

theorem tailTrace_2360429 : CollatzResearch.WordTrace tailWord_2360429 prefixEnd_2360429 1212034627811650544382091 := by
  unfold tailWord_2360429
  simp only [CollatzResearch.WordTrace]
  refine ⟨86091918365576337023556341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57394612243717558015704227 86091918365576337023556341)
  ·
    refine ⟨8071117346772781595958407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86091918365576337023556341 8071117346772781595958407)
    ·
      refine ⟨12106676020159172393937611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8071117346772781595958407 12106676020159172393937611)
      ·
        refine ⟨18160014030238758590906417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12106676020159172393937611 18160014030238758590906417)
        ·
          refine ⟨13620010522679068943179813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18160014030238758590906417 13620010522679068943179813)
          ·
            refine ⟨2553751973002325426846215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13620010522679068943179813 2553751973002325426846215)
            ·
              refine ⟨3830627959503488140269323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553751973002325426846215 3830627959503488140269323)
              ·
                refine ⟨5745941939255232210403985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830627959503488140269323 5745941939255232210403985)
                ·
                  refine ⟨4309456454441424157802989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5745941939255232210403985 4309456454441424157802989)
                  ·
                    refine ⟨1616046170415534059176121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4309456454441424157802989 1616046170415534059176121)
                    ·
                      refine ⟨1212034627811650544382091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616046170415534059176121 1212034627811650544382091)
                      ·
                        rfl

theorem cell23_2360429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_2360429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360429 prefixEnd_2360429 := by exact prefixLift 2360429
  have htrace : WordTrace (prefixWord ++ tailWord_2360429) baseStart_2360429 baseEnd_2360429 := by
    simpa [prefixWord, tailWord_2360429, baseEnd_2360429] using wordTrace_append hprefix tailTrace_2360429
  have hstable : (prefixWord ++ tailWord_2360429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360429).length < 2 ^ (prefixWord ++ tailWord_2360429).sum := by decide
  have hdescent : baseEnd_2360429 < baseStart_2360429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360452 : List Nat := [2, 3, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_2360452 : Nat := 118140960795 + 2360452 * 2 ^ 59
def prefixEnd_2360452 : Nat := 4983230072969 + 3 ^ 40 * 2360452 * 2
def baseEnd_2360452 : Nat := 404015479288901318131495

theorem tailTrace_2360452 : CollatzResearch.WordTrace tailWord_2360452 prefixEnd_2360452 404015479288901318131495 := by
  unfold tailWord_2360452
  simp only [CollatzResearch.WordTrace]
  refine ⟨43046378622246505975821805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57395171496328674634429073 43046378622246505975821805)
  ·
    refine ⟨16142391983342439740933177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43046378622246505975821805 16142391983342439740933177)
    ·
      refine ⟨12106793987506829805699883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16142391983342439740933177 12106793987506829805699883)
      ·
        refine ⟨18160190981260244708549825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12106793987506829805699883 18160190981260244708549825)
        ·
          refine ⟨13620143235945183531412369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18160190981260244708549825 13620143235945183531412369)
          ·
            refine ⟨10215107426958887648559277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13620143235945183531412369 10215107426958887648559277)
            ·
              refine ⟨3830665285109582868209729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10215107426958887648559277 3830665285109582868209729)
              ·
                refine ⟨2872998963832187151157297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3830665285109582868209729 2872998963832187151157297)
                ·
                  refine ⟨2154749222874140363367973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2872998963832187151157297 2154749222874140363367973)
                  ·
                    refine ⟨404015479288901318131495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2154749222874140363367973 404015479288901318131495)
                    ·
                      rfl

theorem cell23_2360452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_2360452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360452 prefixEnd_2360452 := by exact prefixLift 2360452
  have htrace : WordTrace (prefixWord ++ tailWord_2360452) baseStart_2360452 baseEnd_2360452 := by
    simpa [prefixWord, tailWord_2360452, baseEnd_2360452] using wordTrace_append hprefix tailTrace_2360452
  have hstable : (prefixWord ++ tailWord_2360452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360452).length < 2 ^ (prefixWord ++ tailWord_2360452).sum := by decide
  have hdescent : baseEnd_2360452 < baseStart_2360452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360472 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 1, 2, 4]
def baseStart_2360472 : Nat := 118140960795 + 2360472 * 2 ^ 59
def prefixEnd_2360472 : Nat := 4983230072969 + 3 ^ 40 * 2360472 * 2
def baseEnd_2360472 : Nat := 1212056707479793876144393

theorem tailTrace_2360472 : CollatzResearch.WordTrace tailWord_2360472 prefixEnd_2360472 1212056707479793876144393 := by
  unfold tailWord_2360472
  simp only [CollatzResearch.WordTrace]
  refine ⟨43046743352210277683685835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57395657802947036911581113 43046743352210277683685835)
  ·
    refine ⟨64570115028315416525528753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43046743352210277683685835 64570115028315416525528753)
    ·
      refine ⟨48427586271236562394146565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64570115028315416525528753 48427586271236562394146565)
      ·
        refine ⟨9080172425856855448902481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48427586271236562394146565 9080172425856855448902481)
        ·
          refine ⟨6810129319392641586676861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9080172425856855448902481 6810129319392641586676861)
          ·
            refine ⟨2553798494772240595003823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6810129319392641586676861 2553798494772240595003823)
            ·
              refine ⟨3830697742158360892505735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553798494772240595003823 3830697742158360892505735)
              ·
                refine ⟨5746046613237541338758603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830697742158360892505735 5746046613237541338758603)
                ·
                  refine ⟨8619069919856312008137905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5746046613237541338758603 8619069919856312008137905)
                  ·
                    refine ⟨6464302439892234006103429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8619069919856312008137905 6464302439892234006103429)
                    ·
                      refine ⟨1212056707479793876144393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6464302439892234006103429 1212056707479793876144393)
                      ·
                        rfl

theorem cell23_2360472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_2360472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360472 prefixEnd_2360472 := by exact prefixLift 2360472
  have htrace : WordTrace (prefixWord ++ tailWord_2360472) baseStart_2360472 baseEnd_2360472 := by
    simpa [prefixWord, tailWord_2360472, baseEnd_2360472] using wordTrace_append hprefix tailTrace_2360472
  have hstable : (prefixWord ++ tailWord_2360472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360472).length < 2 ^ (prefixWord ++ tailWord_2360472).sum := by decide
  have hdescent : baseEnd_2360472 < baseStart_2360472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360479 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2360479 : Nat := 118140960795 + 2360479 * 2 ^ 59
def prefixEnd_2360479 : Nat := 4983230072969 + 3 ^ 40 * 2360479 * 2
def baseEnd_2360479 : Nat := 1212060301844375348756861

theorem tailTrace_2360479 : CollatzResearch.WordTrace tailWord_2360479 prefixEnd_2360479 1212060301844375348756861 := by
  unfold tailWord_2360479
  simp only [CollatzResearch.WordTrace]
  refine ⟨86093742015395195562876491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57395828010263463708584327 86093742015395195562876491)
  ·
    refine ⟨129140613023092793344314737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86093742015395195562876491 129140613023092793344314737)
    ·
      refine ⟨96855459767319595008236053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129140613023092793344314737 96855459767319595008236053)
      ·
        refine ⟨4540099676593106016011065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 96855459767319595008236053 4540099676593106016011065)
        ·
          refine ⟨3405074757444829512008299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4540099676593106016011065 3405074757444829512008299)
          ·
            refine ⟨5107612136167244268012449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405074757444829512008299 5107612136167244268012449)
            ·
              refine ⟨3830709102125433201009337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5107612136167244268012449 3830709102125433201009337)
              ·
                refine ⟨2873031826594074900757003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3830709102125433201009337 2873031826594074900757003)
                ·
                  refine ⟨4309547739891112351135505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2873031826594074900757003 4309547739891112351135505)
                  ·
                    refine ⟨3232160804918334263351629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4309547739891112351135505 3232160804918334263351629)
                    ·
                      refine ⟨1212060301844375348756861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3232160804918334263351629 1212060301844375348756861)
                      ·
                        rfl

theorem cell23_2360479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2360479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360479 prefixEnd_2360479 := by exact prefixLift 2360479
  have htrace : WordTrace (prefixWord ++ tailWord_2360479) baseStart_2360479 baseEnd_2360479 := by
    simpa [prefixWord, tailWord_2360479, baseEnd_2360479] using wordTrace_append hprefix tailTrace_2360479
  have hstable : (prefixWord ++ tailWord_2360479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360479).length < 2 ^ (prefixWord ++ tailWord_2360479).sum := by decide
  have hdescent : baseEnd_2360479 < baseStart_2360479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360515 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 5, 4, 2]
def baseStart_2360515 : Nat := 118140960795 + 2360515 * 2 ^ 59
def prefixEnd_2360515 : Nat := 4983230072969 + 3 ^ 40 * 2360515 * 2
def baseEnd_2360515 : Nat := 1212078787147937207906695

theorem tailTrace_2360515 : CollatzResearch.WordTrace tailWord_2360515 prefixEnd_2360515 1212078787147937207906695 := by
  unfold tailWord_2360515
  simp only [CollatzResearch.WordTrace]
  refine ⟨86095055043264773711186999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57396703362176515807457999 86095055043264773711186999)
  ·
    refine ⟨129142582564897160566780499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86095055043264773711186999 129142582564897160566780499)
    ·
      refine ⟨193713873847345740850170749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129142582564897160566780499 193713873847345740850170749)
      ·
        refine ⟨72642702692754652818814031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193713873847345740850170749 72642702692754652818814031)
        ·
          refine ⟨108964054039131979228221047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72642702692754652818814031 108964054039131979228221047)
          ·
            refine ⟨163446081058697968842331571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108964054039131979228221047 163446081058697968842331571)
            ·
              refine ⟨245169121588046953263497357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163446081058697968842331571 245169121588046953263497357)
              ·
                refine ⟨91938420595517607473811509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245169121588046953263497357 91938420595517607473811509)
                ·
                  refine ⟨8619226930829775700669829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 91938420595517607473811509 8619226930829775700669829)
                  ·
                    refine ⟨1616105049530582943875593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8619226930829775700669829 1616105049530582943875593)
                    ·
                      refine ⟨1212078787147937207906695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616105049530582943875593 1212078787147937207906695)
                      ·
                        rfl

theorem cell23_2360515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 4, 2].length) (baseStart_2360515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360515 prefixEnd_2360515 := by exact prefixLift 2360515
  have htrace : WordTrace (prefixWord ++ tailWord_2360515) baseStart_2360515 baseEnd_2360515 := by
    simpa [prefixWord, tailWord_2360515, baseEnd_2360515] using wordTrace_append hprefix tailTrace_2360515
  have hstable : (prefixWord ++ tailWord_2360515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360515).length < 2 ^ (prefixWord ++ tailWord_2360515).sum := by decide
  have hdescent : baseEnd_2360515 < baseStart_2360515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360536 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 1, 3, 2]
def baseStart_2360536 : Nat := 118140960795 + 2360536 * 2 ^ 59
def prefixEnd_2360536 : Nat := 4983230072969 + 3 ^ 40 * 2360536 * 2
def baseEnd_2360536 : Nat := 1212089570241681625744099

theorem tailTrace_2360536 : CollatzResearch.WordTrace tailWord_2360536 prefixEnd_2360536 1212089570241681625744099 := by
  unfold tailWord_2360536
  simp only [CollatzResearch.WordTrace]
  refine ⟨43047910488094347148850731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57397213984125796198467641 43047910488094347148850731)
  ·
    refine ⟨64571865732141520723276097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43047910488094347148850731 64571865732141520723276097)
    ·
      refine ⟨48428899299106140542457073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64571865732141520723276097 48428899299106140542457073)
      ·
        refine ⟨36321674474329605406842805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48428899299106140542457073 36321674474329605406842805)
        ·
          refine ⟨3405156981968400506891513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36321674474329605406842805 3405156981968400506891513)
          ·
            refine ⟨2553867736476300380168635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3405156981968400506891513 2553867736476300380168635)
            ·
              refine ⟨3830801604714450570252953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2553867736476300380168635 3830801604714450570252953)
              ·
                refine ⟨2873101203535837927689715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3830801604714450570252953 2873101203535837927689715)
                ·
                  refine ⟨4309651805303756891534573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2873101203535837927689715 4309651805303756891534573)
                  ·
                    refine ⟨1616119426988908834325465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4309651805303756891534573 1616119426988908834325465)
                    ·
                      refine ⟨1212089570241681625744099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616119426988908834325465 1212089570241681625744099)
                      ·
                        rfl

theorem cell23_2360536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_2360536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360536 prefixEnd_2360536 := by exact prefixLift 2360536
  have htrace : WordTrace (prefixWord ++ tailWord_2360536) baseStart_2360536 baseEnd_2360536 := by
    simpa [prefixWord, tailWord_2360536, baseEnd_2360536] using wordTrace_append hprefix tailTrace_2360536
  have hstable : (prefixWord ++ tailWord_2360536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360536).length < 2 ^ (prefixWord ++ tailWord_2360536).sum := by decide
  have hdescent : baseEnd_2360536 < baseStart_2360536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360538 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 9]
def baseStart_2360538 : Nat := 118140960795 + 2360538 * 2 ^ 59
def prefixEnd_2360538 : Nat := 4983230072969 + 3 ^ 40 * 2360538 * 2
def baseEnd_2360538 : Nat := 134676733022554513102121

theorem tailTrace_2360538 : CollatzResearch.WordTrace tailWord_2360538 prefixEnd_2360538 134676733022554513102121 := by
  unfold tailWord_2360538
  simp only [CollatzResearch.WordTrace]
  refine ⟨21523973480545362159818567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57397262614787632426182845 21523973480545362159818567)
  ·
    refine ⟨32285960220818043239727851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21523973480545362159818567 32285960220818043239727851)
    ·
      refine ⟨48428940331227064859591777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32285960220818043239727851 48428940331227064859591777)
      ·
        refine ⟨36321705248420298644693833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48428940331227064859591777 36321705248420298644693833)
        ·
          refine ⟨27241278936315223983520375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36321705248420298644693833 27241278936315223983520375)
          ·
            refine ⟨40861918404472835975280563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27241278936315223983520375 40861918404472835975280563)
            ·
              refine ⟨61292877606709253962920845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40861918404472835975280563 61292877606709253962920845)
              ·
                refine ⟨22984829102515970236095317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61292877606709253962920845 22984829102515970236095317)
                ·
                  refine ⟨134676733022554513102121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22984829102515970236095317 134676733022554513102121)
                  ·
                    rfl

theorem cell23_2360538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_2360538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360538 prefixEnd_2360538 := by exact prefixLift 2360538
  have htrace : WordTrace (prefixWord ++ tailWord_2360538) baseStart_2360538 baseEnd_2360538 := by
    simpa [prefixWord, tailWord_2360538, baseEnd_2360538] using wordTrace_append hprefix tailTrace_2360538
  have hstable : (prefixWord ++ tailWord_2360538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360538).length < 2 ^ (prefixWord ++ tailWord_2360538).sum := by decide
  have hdescent : baseEnd_2360538 < baseStart_2360538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360549 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 1, 4, 2]
def baseStart_2360549 : Nat := 118140960795 + 2360549 * 2 ^ 59
def prefixEnd_2360549 : Nat := 4983230072969 + 3 ^ 40 * 2360549 * 2
def baseEnd_2360549 : Nat := 1212096245490190074881539

theorem tailTrace_2360549 : CollatzResearch.WordTrace tailWord_2360549 prefixEnd_2360549 1212096245490190074881539 := by
  unfold tailWord_2360549
  simp only [CollatzResearch.WordTrace]
  refine ⟨86096295125141597517924701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57397530083427731678616467 86096295125141597517924701)
  ·
    refine ⟨32286110671928099069221763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86096295125141597517924701 32286110671928099069221763)
    ·
      refine ⟨48429166007892148603832645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32286110671928099069221763 48429166007892148603832645)
      ·
        refine ⟨9080468626479777863218621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48429166007892148603832645 9080468626479777863218621)
        ·
          refine ⟨3405175734929916698706983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9080468626479777863218621 3405175734929916698706983)
          ·
            refine ⟨5107763602394875048060475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405175734929916698706983 5107763602394875048060475)
            ·
              refine ⟨7661645403592312572090713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5107763602394875048060475 7661645403592312572090713)
              ·
                refine ⟨5746234052694234429068035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7661645403592312572090713 5746234052694234429068035)
                ·
                  refine ⟨8619351079041351643602053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5746234052694234429068035 8619351079041351643602053)
                  ·
                    refine ⟨1616128327320253433175385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8619351079041351643602053 1616128327320253433175385)
                    ·
                      refine ⟨1212096245490190074881539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616128327320253433175385 1212096245490190074881539)
                      ·
                        rfl

theorem cell23_2360549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_2360549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360549 prefixEnd_2360549 := by exact prefixLift 2360549
  have htrace : WordTrace (prefixWord ++ tailWord_2360549) baseStart_2360549 baseEnd_2360549 := by
    simpa [prefixWord, tailWord_2360549, baseEnd_2360549] using wordTrace_append hprefix tailTrace_2360549
  have hstable : (prefixWord ++ tailWord_2360549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360549).length < 2 ^ (prefixWord ++ tailWord_2360549).sum := by decide
  have hdescent : baseEnd_2360549 < baseStart_2360549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360568 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 5, 7]
def baseStart_2360568 : Nat := 118140960795 + 2360568 * 2 ^ 59
def prefixEnd_2360568 : Nat := 4983230072969 + 3 ^ 40 * 2360568 * 2
def baseEnd_2360568 : Nat := 404035333874208500181317

theorem tailTrace_2360568 : CollatzResearch.WordTrace tailWord_2360568 prefixEnd_2360568 404035333874208500181317 := by
  unfold tailWord_2360568
  simp only [CollatzResearch.WordTrace]
  refine ⟨43048494056036381881433179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57397992074715175841910905 43048494056036381881433179)
  ·
    refine ⟨64572741084054572822149769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43048494056036381881433179 64572741084054572822149769)
    ·
      refine ⟨48429555813040929616612327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64572741084054572822149769 48429555813040929616612327)
      ·
        refine ⟨72644333719561394424918491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48429555813040929616612327 72644333719561394424918491)
        ·
          refine ⟨108966500579342091637377737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72644333719561394424918491 108966500579342091637377737)
          ·
            refine ⟨81724875434506568728033303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108966500579342091637377737 81724875434506568728033303)
            ·
              refine ⟨122587313151759853092049955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81724875434506568728033303 122587313151759853092049955)
              ·
                refine ⟨183880969727639779638074933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122587313151759853092049955 183880969727639779638074933)
                ·
                  refine ⟨17238840911966229341069525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183880969727639779638074933 17238840911966229341069525)
                  ·
                    refine ⟨404035333874208500181317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17238840911966229341069525 404035333874208500181317)
                    ·
                      rfl

theorem cell23_2360568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_2360568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360568 prefixEnd_2360568 := by exact prefixLift 2360568
  have htrace : WordTrace (prefixWord ++ tailWord_2360568) baseStart_2360568 baseEnd_2360568 := by
    simpa [prefixWord, tailWord_2360568, baseEnd_2360568] using wordTrace_append hprefix tailTrace_2360568
  have hstable : (prefixWord ++ tailWord_2360568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360568).length < 2 ^ (prefixWord ++ tailWord_2360568).sum := by decide
  have hdescent : baseEnd_2360568 < baseStart_2360568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360602 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 2, 5]
def baseStart_2360602 : Nat := 118140960795 + 2360602 * 2 ^ 59
def prefixEnd_2360602 : Nat := 4983230072969 + 3 ^ 40 * 2360602 * 2
def baseEnd_2360602 : Nat := 404041153321626122506265

theorem tailTrace_2360602 : CollatzResearch.WordTrace tailWord_2360602 prefixEnd_2360602 404041153321626122506265 := by
  unfold tailWord_2360602
  simp only [CollatzResearch.WordTrace]
  refine ⟨21524557048487396892401015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57398818795966391713069373 21524557048487396892401015)
  ·
    refine ⟨32286835572731095338601523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21524557048487396892401015 32286835572731095338601523)
    ·
      refine ⟨48430253359096643007902285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32286835572731095338601523 48430253359096643007902285)
      ·
        refine ⟨18161345009661241127963357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48430253359096643007902285 18161345009661241127963357)
        ·
          refine ⟨6810504378622965422986259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18161345009661241127963357 6810504378622965422986259)
          ·
            refine ⟨10215756567934448134479389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6810504378622965422986259 10215756567934448134479389)
            ·
              refine ⟨3830908712975418050429771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10215756567934448134479389 3830908712975418050429771)
              ·
                refine ⟨5746363069463127075644657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3830908712975418050429771 5746363069463127075644657)
                ·
                  refine ⟨4309772302097345306733493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5746363069463127075644657 4309772302097345306733493)
                  ·
                    refine ⟨404041153321626122506265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4309772302097345306733493 404041153321626122506265)
                    ·
                      rfl

theorem cell23_2360602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_2360602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360602 prefixEnd_2360602 := by exact prefixLift 2360602
  have htrace : WordTrace (prefixWord ++ tailWord_2360602) baseStart_2360602 baseEnd_2360602 := by
    simpa [prefixWord, tailWord_2360602, baseEnd_2360602] using wordTrace_append hprefix tailTrace_2360602
  have hstable : (prefixWord ++ tailWord_2360602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360602).length < 2 ^ (prefixWord ++ tailWord_2360602).sum := by decide
  have hdescent : baseEnd_2360602 < baseStart_2360602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360645 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 6]
def baseStart_2360645 : Nat := 118140960795 + 2360645 * 2 ^ 59
def prefixEnd_2360645 : Nat := 4983230072969 + 3 ^ 40 * 2360645 * 2
def baseEnd_2360645 : Nat := 134682837737002411031233

theorem tailTrace_2360645 : CollatzResearch.WordTrace tailWord_2360645 prefixEnd_2360645 134682837737002411031233 := by
  unfold tailWord_2360645
  simp only [CollatzResearch.WordTrace]
  refine ⟨86099796532793805913419389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57399864355195870608946259 86099796532793805913419389)
  ·
    refine ⟨32287423699797677217532271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86099796532793805913419389 32287423699797677217532271)
    ·
      refine ⟨48431135549696515826298407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32287423699797677217532271 48431135549696515826298407)
      ·
        refine ⟨72646703324544773739447611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48431135549696515826298407 72646703324544773739447611)
        ·
          refine ⟨108970054986817160609171417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72646703324544773739447611 108970054986817160609171417)
          ·
            refine ⟨81727541240112870456878563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108970054986817160609171417 81727541240112870456878563)
            ·
              refine ⟨122591311860169305685317845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81727541240112870456878563 122591311860169305685317845)
              ·
                refine ⟨2873233871722718101999637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 122591311860169305685317845 2873233871722718101999637)
                ·
                  refine ⟨134682837737002411031233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2873233871722718101999637 134682837737002411031233)
                  ·
                    rfl

theorem cell23_2360645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_2360645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360645 prefixEnd_2360645 := by exact prefixLift 2360645
  have htrace : WordTrace (prefixWord ++ tailWord_2360645) baseStart_2360645 baseEnd_2360645 := by
    simpa [prefixWord, tailWord_2360645, baseEnd_2360645] using wordTrace_append hprefix tailTrace_2360645
  have hstable : (prefixWord ++ tailWord_2360645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360645).length < 2 ^ (prefixWord ++ tailWord_2360645).sum := by decide
  have hdescent : baseEnd_2360645 < baseStart_2360645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360689 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 3, 1, 3]
def baseStart_2360689 : Nat := 118140960795 + 2360689 * 2 ^ 59
def prefixEnd_2360689 : Nat := 4983230072969 + 3 ^ 40 * 2360689 * 2
def baseEnd_2360689 : Nat := 1212168132781819527130895

theorem tailTrace_2360689 : CollatzResearch.WordTrace tailWord_2360689 prefixEnd_2360689 1212168132781819527130895 := by
  unfold tailWord_2360689
  simp only [CollatzResearch.WordTrace]
  refine ⟨86101401344634401428021121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57400934229756267618680747 86101401344634401428021121)
  ·
    refine ⟨64576051008475801071015841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86101401344634401428021121 64576051008475801071015841)
    ·
      refine ⟨48432038256356850803261881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64576051008475801071015841 48432038256356850803261881)
      ·
        refine ⟨36324028692267638102446411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48432038256356850803261881 36324028692267638102446411)
        ·
          refine ⟨54486043038401457153669617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36324028692267638102446411 54486043038401457153669617)
          ·
            refine ⟨40864532278801092865252213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54486043038401457153669617 40864532278801092865252213)
            ·
              refine ⟨3831049901137602456117395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40864532278801092865252213 3831049901137602456117395)
              ·
                refine ⟨5746574851706403684176093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3831049901137602456117395 5746574851706403684176093)
                ·
                  refine ⟨2154965569389901381566035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5746574851706403684176093 2154965569389901381566035)
                  ·
                    refine ⟨3232448354084852072349053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2154965569389901381566035 3232448354084852072349053)
                    ·
                      refine ⟨1212168132781819527130895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3232448354084852072349053 1212168132781819527130895)
                      ·
                        rfl

theorem cell23_2360689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_2360689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360689 prefixEnd_2360689 := by exact prefixLift 2360689
  have htrace : WordTrace (prefixWord ++ tailWord_2360689) baseStart_2360689 baseEnd_2360689 := by
    simpa [prefixWord, tailWord_2360689, baseEnd_2360689] using wordTrace_append hprefix tailTrace_2360689
  have hstable : (prefixWord ++ tailWord_2360689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360689).length < 2 ^ (prefixWord ++ tailWord_2360689).sum := by decide
  have hdescent : baseEnd_2360689 < baseStart_2360689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360735 : List Nat := [1, 1, 2, 5, 1, 13]
def baseStart_2360735 : Nat := 118140960795 + 2360735 * 2 ^ 59
def prefixEnd_2360735 : Nat := 4983230072969 + 3 ^ 40 * 2360735 * 2
def baseEnd_2360735 : Nat := 4988443427538791552081

theorem tailTrace_2360735 : CollatzResearch.WordTrace tailWord_2360735 prefixEnd_2360735 4988443427538791552081 := by
  unfold tailWord_2360735
  simp only [CollatzResearch.WordTrace]
  refine ⟨86103079102467751284195659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57402052734978500856130439 86103079102467751284195659)
  ·
    refine ⟨129154618653701626926293489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86103079102467751284195659 129154618653701626926293489)
    ·
      refine ⟨96865963990276220194720117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129154618653701626926293489 96865963990276220194720117)
      ·
        refine ⟨9081184124088395643255011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96865963990276220194720117 9081184124088395643255011)
        ·
          refine ⟨13621776186132593464882517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9081184124088395643255011 13621776186132593464882517)
          ·
            refine ⟨4988443427538791552081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 13621776186132593464882517 4988443427538791552081)
            ·
              rfl

theorem cell23_2360735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 13].length) (baseStart_2360735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360735 prefixEnd_2360735 := by exact prefixLift 2360735
  have htrace : WordTrace (prefixWord ++ tailWord_2360735) baseStart_2360735 baseEnd_2360735 := by
    simpa [prefixWord, tailWord_2360735, baseEnd_2360735] using wordTrace_append hprefix tailTrace_2360735
  have hstable : (prefixWord ++ tailWord_2360735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360735).length < 2 ^ (prefixWord ++ tailWord_2360735).sum := by decide
  have hdescent : baseEnd_2360735 < baseStart_2360735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360739 : List Nat := [1, 1, 1, 4, 1, 3, 4, 2, 2, 4]
def baseStart_2360739 : Nat := 118140960795 + 2360739 * 2 ^ 59
def prefixEnd_2360739 : Nat := 4983230072969 + 3 ^ 40 * 2360739 * 2
def baseEnd_2360739 : Nat := 404064602271514777168555

theorem tailTrace_2360739 : CollatzResearch.WordTrace tailWord_2360739 prefixEnd_2360739 404064602271514777168555 := by
  unfold tailWord_2360739
  simp only [CollatzResearch.WordTrace]
  refine ⟨86103224994453259967341271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57402149996302173311560847 86103224994453259967341271)
  ·
    refine ⟨129154837491679889951011907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86103224994453259967341271 129154837491679889951011907)
    ·
      refine ⟨193732256237519834926517861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129154837491679889951011907 193732256237519834926517861)
      ·
        refine ⟨36324798044534969048722099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193732256237519834926517861 36324798044534969048722099)
        ·
          refine ⟨54487197066802453573083149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36324798044534969048722099 54487197066802453573083149)
          ·
            refine ⟨20432698900050920089906181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54487197066802453573083149 20432698900050920089906181)
            ·
              refine ⟨3831131043759547516857409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20432698900050920089906181 3831131043759547516857409)
              ·
                refine ⟨2873348282819660637643057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3831131043759547516857409 2873348282819660637643057)
                ·
                  refine ⟨2155011212114745478232293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2873348282819660637643057 2155011212114745478232293)
                  ·
                    refine ⟨404064602271514777168555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2155011212114745478232293 404064602271514777168555)
                    ·
                      rfl

theorem cell23_2360739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 2, 2, 4].length) (baseStart_2360739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360739 prefixEnd_2360739 := by exact prefixLift 2360739
  have htrace : WordTrace (prefixWord ++ tailWord_2360739) baseStart_2360739 baseEnd_2360739 := by
    simpa [prefixWord, tailWord_2360739, baseEnd_2360739] using wordTrace_append hprefix tailTrace_2360739
  have hstable : (prefixWord ++ tailWord_2360739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360739).length < 2 ^ (prefixWord ++ tailWord_2360739).sum := by decide
  have hdescent : baseEnd_2360739 < baseStart_2360739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360755 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 6]
def baseStart_2360755 : Nat := 118140960795 + 2360755 * 2 ^ 59
def prefixEnd_2360755 : Nat := 4983230072969 + 3 ^ 40 * 2360755 * 2
def baseEnd_2360755 : Nat := 1212202022505016268905591

theorem tailTrace_2360755 : CollatzResearch.WordTrace tailWord_2360755 prefixEnd_2360755 1212202022505016268905591 := by
  unfold tailWord_2360755
  simp only [CollatzResearch.WordTrace]
  refine ⟨86103808562395294699923719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57402539041596863133282479 86103808562395294699923719)
  ·
    refine ⟨129155712843592942049885579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86103808562395294699923719 129155712843592942049885579)
    ·
      refine ⟨193733569265389413074828369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129155712843592942049885579 193733569265389413074828369)
      ·
        refine ⟨145300176949042059806121277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193733569265389413074828369 145300176949042059806121277)
        ·
          refine ⟨54487566355890772427295479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145300176949042059806121277 54487566355890772427295479)
          ·
            refine ⟨81731349533836158640943219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54487566355890772427295479 81731349533836158640943219)
            ·
              refine ⟨122597024300754237961414829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81731349533836158640943219 122597024300754237961414829)
              ·
                refine ⟨45973884112782839235530561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122597024300754237961414829 45973884112782839235530561)
                ·
                  refine ⟨34480413084587129426647921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45973884112782839235530561 34480413084587129426647921)
                  ·
                    refine ⟨25860309813440347069985941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34480413084587129426647921 25860309813440347069985941)
                    ·
                      refine ⟨1212202022505016268905591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25860309813440347069985941 1212202022505016268905591)
                      ·
                        rfl

theorem cell23_2360755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_2360755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360755 prefixEnd_2360755 := by exact prefixLift 2360755
  have htrace : WordTrace (prefixWord ++ tailWord_2360755) baseStart_2360755 baseEnd_2360755 := by
    simpa [prefixWord, tailWord_2360755, baseEnd_2360755] using wordTrace_append hprefix tailTrace_2360755
  have hstable : (prefixWord ++ tailWord_2360755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360755).length < 2 ^ (prefixWord ++ tailWord_2360755).sum := by decide
  have hdescent : baseEnd_2360755 < baseStart_2360755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360780 : List Nat := [2, 2, 1, 4, 2, 2, 2, 3, 1, 2, 2]
def baseStart_2360780 : Nat := 118140960795 + 2360780 * 2 ^ 59
def prefixEnd_2360780 : Nat := 4983230072969 + 3 ^ 40 * 2360780 * 2
def baseEnd_2360780 : Nat := 1212214859521378671092977

theorem tailTrace_2360780 : CollatzResearch.WordTrace tailWord_2360780 prefixEnd_2360780 1212214859521378671092977 := by
  unfold tailWord_2360780
  simp only [CollatzResearch.WordTrace]
  refine ⟨43052360193652361984791897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57403146924869815979722529 43052360193652361984791897)
  ·
    refine ⟨32289270145239271488593923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43052360193652361984791897 32289270145239271488593923)
    ·
      refine ⟨48433905217858907232890885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32289270145239271488593923 48433905217858907232890885)
      ·
        refine ⟨9081357228348545106167041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48433905217858907232890885 9081357228348545106167041)
        ·
          refine ⟨6811017921261408829625281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9081357228348545106167041 6811017921261408829625281)
          ·
            refine ⟨5108263440946056622218961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6811017921261408829625281 5108263440946056622218961)
            ·
              refine ⟨3831197580709542466664221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5108263440946056622218961 3831197580709542466664221)
              ·
                refine ⟨1436699092766078424999083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3831197580709542466664221 1436699092766078424999083)
                ·
                  refine ⟨2155048639149117637498625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436699092766078424999083 2155048639149117637498625)
                  ·
                    refine ⟨1616286479361838228123969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2155048639149117637498625 1616286479361838228123969)
                    ·
                      refine ⟨1212214859521378671092977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616286479361838228123969 1212214859521378671092977)
                      ·
                        rfl

theorem cell23_2360780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_2360780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360780 prefixEnd_2360780 := by exact prefixLift 2360780
  have htrace : WordTrace (prefixWord ++ tailWord_2360780) baseStart_2360780 baseEnd_2360780 := by
    simpa [prefixWord, tailWord_2360780, baseEnd_2360780] using wordTrace_append hprefix tailTrace_2360780
  have hstable : (prefixWord ++ tailWord_2360780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360780).length < 2 ^ (prefixWord ++ tailWord_2360780).sum := by decide
  have hdescent : baseEnd_2360780 < baseStart_2360780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360813 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2360813 : Nat := 118140960795 + 2360813 * 2 ^ 59
def prefixEnd_2360813 : Nat := 4983230072969 + 3 ^ 40 * 2360813 * 2
def baseEnd_2360813 : Nat := 1212231804382977041980325

theorem tailTrace_2360813 : CollatzResearch.WordTrace tailWord_2360813 prefixEnd_2360813 1212231804382977041980325 := by
  unfold tailWord_2360813
  simp only [CollatzResearch.WordTrace]
  refine ⟨86105923996185170605535093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57403949330790113737023395 86105923996185170605535093)
  ·
    refine ⟨8072430374642359744268915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86105923996185170605535093 8072430374642359744268915)
    ·
      refine ⟨12108645561963539616403373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8072430374642359744268915 12108645561963539616403373)
      ·
        refine ⟨4540742085736327356151265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12108645561963539616403373 4540742085736327356151265)
        ·
          refine ⟨3405556564302245517113449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4540742085736327356151265 3405556564302245517113449)
          ·
            refine ⟨2554167423226684137835087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3405556564302245517113449 2554167423226684137835087)
            ·
              refine ⟨3831251134840026206752631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554167423226684137835087 3831251134840026206752631)
              ·
                refine ⟨5746876702260039310128947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3831251134840026206752631 5746876702260039310128947)
                ·
                  refine ⟨8620315053390058965193421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5746876702260039310128947 8620315053390058965193421)
                  ·
                    refine ⟨3232618145021272111947533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8620315053390058965193421 3232618145021272111947533)
                    ·
                      refine ⟨1212231804382977041980325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3232618145021272111947533 1212231804382977041980325)
                      ·
                        rfl

theorem cell23_2360813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2360813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360813 prefixEnd_2360813 := by exact prefixLift 2360813
  have htrace : WordTrace (prefixWord ++ tailWord_2360813) baseStart_2360813 baseEnd_2360813 := by
    simpa [prefixWord, tailWord_2360813, baseEnd_2360813] using wordTrace_append hprefix tailTrace_2360813
  have hstable : (prefixWord ++ tailWord_2360813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360813).length < 2 ^ (prefixWord ++ tailWord_2360813).sum := by decide
  have hdescent : baseEnd_2360813 < baseStart_2360813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360819 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 1, 4, 2]
def baseStart_2360819 : Nat := 118140960795 + 2360819 * 2 ^ 59
def prefixEnd_2360819 : Nat := 4983230072969 + 3 ^ 40 * 2360819 * 2
def baseEnd_2360819 : Nat := 1212234885266904018505297

theorem tailTrace_2360819 : CollatzResearch.WordTrace tailWord_2360819 prefixEnd_2360819 1212234885266904018505297 := by
  unfold tailWord_2360819
  simp only [CollatzResearch.WordTrace]
  refine ⟨86106142834163433630253511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57404095222775622420169007 86106142834163433630253511)
  ·
    refine ⟨129159214251245150445380267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86106142834163433630253511 129159214251245150445380267)
    ·
      refine ⟨193738821376867725668070401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129159214251245150445380267 193738821376867725668070401)
      ·
        refine ⟨145304116032650794251052801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193738821376867725668070401 145304116032650794251052801)
        ·
          refine ⟨108978087024488095688289601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145304116032650794251052801 108978087024488095688289601)
          ·
            refine ⟨81733565268366071766217201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108978087024488095688289601 81733565268366071766217201)
            ·
              refine ⟨61300173951274553824662901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81733565268366071766217201 61300173951274553824662901)
              ·
                refine ⟨5746891307931989421062147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61300173951274553824662901 5746891307931989421062147)
                ·
                  refine ⟨8620336961897984131593221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5746891307931989421062147 8620336961897984131593221)
                  ·
                    refine ⟨1616313180355872024673729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8620336961897984131593221 1616313180355872024673729)
                    ·
                      refine ⟨1212234885266904018505297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616313180355872024673729 1212234885266904018505297)
                      ·
                        rfl

theorem cell23_2360819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 4, 2].length) (baseStart_2360819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360819 prefixEnd_2360819 := by exact prefixLift 2360819
  have htrace : WordTrace (prefixWord ++ tailWord_2360819) baseStart_2360819 baseEnd_2360819 := by
    simpa [prefixWord, tailWord_2360819, baseEnd_2360819] using wordTrace_append hprefix tailTrace_2360819
  have hstable : (prefixWord ++ tailWord_2360819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360819).length < 2 ^ (prefixWord ++ tailWord_2360819).sum := by decide
  have hdescent : baseEnd_2360819 < baseStart_2360819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360839 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2360839 : Nat := 118140960795 + 2360839 * 2 ^ 59
def prefixEnd_2360839 : Nat := 4983230072969 + 3 ^ 40 * 2360839 * 2
def baseEnd_2360839 : Nat := 1212245154879993940255205

theorem tailTrace_2360839 : CollatzResearch.WordTrace tailWord_2360839 prefixEnd_2360839 1212245154879993940255205 := by
  unfold tailWord_2360839
  simp only [CollatzResearch.WordTrace]
  refine ⟨86106872294090977045981571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57404581529393984697321047 86106872294090977045981571)
  ·
    refine ⟨129160308441136465568972357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86106872294090977045981571 129160308441136465568972357)
    ·
      refine ⟨24217557832713087294182317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129160308441136465568972357 24217557832713087294182317)
      ·
        refine ⟨9081584187267407735318369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24217557832713087294182317 9081584187267407735318369)
        ·
          refine ⟨6811188140450555801488777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9081584187267407735318369 6811188140450555801488777)
          ·
            refine ⟨5108391105337916851116583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6811188140450555801488777 5108391105337916851116583)
            ·
              refine ⟨7662586658006875276674875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5108391105337916851116583 7662586658006875276674875)
              ·
                refine ⟨11493879987010312915012313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7662586658006875276674875 11493879987010312915012313)
                ·
                  refine ⟨8620409990257734686259235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11493879987010312915012313 8620409990257734686259235)
                  ·
                    refine ⟨12930614985386602029388853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8620409990257734686259235 12930614985386602029388853)
                    ·
                      refine ⟨1212245154879993940255205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12930614985386602029388853 1212245154879993940255205)
                      ·
                        rfl

theorem cell23_2360839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2360839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360839 prefixEnd_2360839 := by exact prefixLift 2360839
  have htrace : WordTrace (prefixWord ++ tailWord_2360839) baseStart_2360839 baseEnd_2360839 := by
    simpa [prefixWord, tailWord_2360839, baseEnd_2360839] using wordTrace_append hprefix tailTrace_2360839
  have hstable : (prefixWord ++ tailWord_2360839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360839).length < 2 ^ (prefixWord ++ tailWord_2360839).sum := by decide
  have hdescent : baseEnd_2360839 < baseStart_2360839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360882 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2360882 : Nat := 118140960795 + 2360882 * 2 ^ 59
def prefixEnd_2360882 : Nat := 4983230072969 + 3 ^ 40 * 2360882 * 2
def baseEnd_2360882 : Nat := 1212267234548137272017507

theorem tailTrace_2360882 : CollatzResearch.WordTrace tailWord_2360882 prefixEnd_2360882 1212267234548137272017507 := by
  unfold tailWord_2360882
  simp only [CollatzResearch.WordTrace]
  refine ⟨21527110158233798847449225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57405627088623463593197933 21527110158233798847449225)
  ·
    refine ⟨16145332618675349135586919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21527110158233798847449225 16145332618675349135586919)
    ·
      refine ⟨24217998928013023703380379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16145332618675349135586919 24217998928013023703380379)
      ·
        refine ⟨36326998392019535555070569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24217998928013023703380379 36326998392019535555070569)
        ·
          refine ⟨27245248794014651666302927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36326998392019535555070569 27245248794014651666302927)
          ·
            refine ⟨40867873191021977499454391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27245248794014651666302927 40867873191021977499454391)
            ·
              refine ⟨61301809786532966249181587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40867873191021977499454391 61301809786532966249181587)
              ·
                refine ⟨91952714679799449373772381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61301809786532966249181587 91952714679799449373772381)
                ·
                  refine ⟨34482268004924793515164643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91952714679799449373772381 34482268004924793515164643)
                  ·
                    refine ⟨51723402007387190272746965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34482268004924793515164643 51723402007387190272746965)
                    ·
                      refine ⟨1212267234548137272017507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51723402007387190272746965 1212267234548137272017507)
                      ·
                        rfl

theorem cell23_2360882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2360882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360882 prefixEnd_2360882 := by exact prefixLift 2360882
  have htrace : WordTrace (prefixWord ++ tailWord_2360882) baseStart_2360882 baseEnd_2360882 := by
    simpa [prefixWord, tailWord_2360882, baseEnd_2360882] using wordTrace_append hprefix tailTrace_2360882
  have hstable : (prefixWord ++ tailWord_2360882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360882).length < 2 ^ (prefixWord ++ tailWord_2360882).sum := by decide
  have hdescent : baseEnd_2360882 < baseStart_2360882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360889 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 2, 5]
def baseStart_2360889 : Nat := 118140960795 + 2360889 * 2 ^ 59
def prefixEnd_2360889 : Nat := 4983230072969 + 3 ^ 40 * 2360889 * 2
def baseEnd_2360889 : Nat := 404090276304239581543325

theorem tailTrace_2360889 : CollatzResearch.WordTrace tailWord_2360889 prefixEnd_2360889 404090276304239581543325 := by
  unfold tailWord_2360889
  simp only [CollatzResearch.WordTrace]
  refine ⟨86108695943909835585301721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57405797295939890390201147 86108695943909835585301721)
  ·
    refine ⟨64581521957932376688976291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86108695943909835585301721 64581521957932376688976291)
    ·
      refine ⟨96872282936898565033464437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64581521957932376688976291 96872282936898565033464437)
      ·
        refine ⟨9081776525334240471887291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96872282936898565033464437 9081776525334240471887291)
        ·
          refine ⟨13622664788001360707830937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9081776525334240471887291 13622664788001360707830937)
          ·
            refine ⟨10216998591001020530873203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13622664788001360707830937 10216998591001020530873203)
            ·
              refine ⟨15325497886501530796309805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10216998591001020530873203 15325497886501530796309805)
              ·
                refine ⟨5747061707438074048616177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15325497886501530796309805 5747061707438074048616177)
                ·
                  refine ⟨4310296280578555536462133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5747061707438074048616177 4310296280578555536462133)
                  ·
                    refine ⟨404090276304239581543325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4310296280578555536462133 404090276304239581543325)
                    ·
                      rfl

theorem cell23_2360889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_2360889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360889 prefixEnd_2360889 := by exact prefixLift 2360889
  have htrace : WordTrace (prefixWord ++ tailWord_2360889) baseStart_2360889 baseEnd_2360889 := by
    simpa [prefixWord, tailWord_2360889, baseEnd_2360889] using wordTrace_append hprefix tailTrace_2360889
  have hstable : (prefixWord ++ tailWord_2360889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360889).length < 2 ^ (prefixWord ++ tailWord_2360889).sum := by decide
  have hdescent : baseEnd_2360889 < baseStart_2360889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360912 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_2360912 : Nat := 118140960795 + 2360912 * 2 ^ 59
def prefixEnd_2360912 : Nat := 4983230072969 + 3 ^ 40 * 2360912 * 2
def baseEnd_2360912 : Nat := 1212282638967772154642369

theorem tailTrace_2360912 : CollatzResearch.WordTrace tailWord_2360912 prefixEnd_2360912 1212282638967772154642369 := by
  unfold tailWord_2360912
  simp only [CollatzResearch.WordTrace]
  refine ⟨43054767411413255256694495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57406356548551007008925993 43054767411413255256694495)
  ·
    refine ⟨64582151117119882885041743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43054767411413255256694495 64582151117119882885041743)
    ·
      refine ⟨96873226675679824327562615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64582151117119882885041743 96873226675679824327562615)
      ·
        refine ⟨145309840013519736491343923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96873226675679824327562615 145309840013519736491343923)
        ·
          refine ⟨217964760020279604737015885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145309840013519736491343923 217964760020279604737015885)
          ·
            refine ⟨81736785007604851776380957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 217964760020279604737015885 81736785007604851776380957)
            ·
              refine ⟨30651294377851819416142859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81736785007604851776380957 30651294377851819416142859)
              ·
                refine ⟨45976941566777729124214289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30651294377851819416142859 45976941566777729124214289)
                ·
                  refine ⟨34482706175083296843160717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45976941566777729124214289 34482706175083296843160717)
                  ·
                    refine ⟨12931014815656236316185269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34482706175083296843160717 12931014815656236316185269)
                    ·
                      refine ⟨1212282638967772154642369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12931014815656236316185269 1212282638967772154642369)
                      ·
                        rfl

theorem cell23_2360912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_2360912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360912 prefixEnd_2360912 := by exact prefixLift 2360912
  have htrace : WordTrace (prefixWord ++ tailWord_2360912) baseStart_2360912 baseEnd_2360912 := by
    simpa [prefixWord, tailWord_2360912, baseEnd_2360912] using wordTrace_append hprefix tailTrace_2360912
  have hstable : (prefixWord ++ tailWord_2360912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360912).length < 2 ^ (prefixWord ++ tailWord_2360912).sum := by decide
  have hdescent : baseEnd_2360912 < baseStart_2360912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360929 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_2360929 : Nat := 118140960795 + 2360929 * 2 ^ 59
def prefixEnd_2360929 : Nat := 4983230072969 + 3 ^ 40 * 2360929 * 2
def baseEnd_2360929 : Nat := 1212291368138898588129791

theorem tailTrace_2360929 : CollatzResearch.WordTrace tailWord_2360929 prefixEnd_2360929 1212291368138898588129791 := by
  unfold tailWord_2360929
  simp only [CollatzResearch.WordTrace]
  refine ⟨86110154863764922416757841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57406769909176614944505227 86110154863764922416757841)
  ·
    refine ⟨64582616147823691812568381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86110154863764922416757841 64582616147823691812568381)
    ·
      refine ⟨24218481055433884429713143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64582616147823691812568381 24218481055433884429713143)
      ·
        refine ⟨36327721583150826644569715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24218481055433884429713143 36327721583150826644569715)
        ·
          refine ⟨54491582374726239966854573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36327721583150826644569715 54491582374726239966854573)
          ·
            refine ⟨20434343390522339987570465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54491582374726239966854573 20434343390522339987570465)
            ·
              refine ⟨15325757542891754990677849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20434343390522339987570465 15325757542891754990677849)
              ·
                refine ⟨11494318157168816243008387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15325757542891754990677849 11494318157168816243008387)
                ·
                  refine ⟨17241477235753224364512581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11494318157168816243008387 17241477235753224364512581)
                  ·
                    refine ⟨3232776981703729568346109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17241477235753224364512581 3232776981703729568346109)
                    ·
                      refine ⟨1212291368138898588129791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3232776981703729568346109 1212291368138898588129791)
                      ·
                        rfl

theorem cell23_2360929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_2360929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360929 prefixEnd_2360929 := by exact prefixLift 2360929
  have htrace : WordTrace (prefixWord ++ tailWord_2360929) baseStart_2360929 baseEnd_2360929 := by
    simpa [prefixWord, tailWord_2360929, baseEnd_2360929] using wordTrace_append hprefix tailTrace_2360929
  have hstable : (prefixWord ++ tailWord_2360929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360929).length < 2 ^ (prefixWord ++ tailWord_2360929).sum := by decide
  have hdescent : baseEnd_2360929 < baseStart_2360929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360936 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 5, 4]
def baseStart_2360936 : Nat := 118140960795 + 2360936 * 2 ^ 59
def prefixEnd_2360936 : Nat := 4983230072969 + 3 ^ 40 * 2360936 * 2
def baseEnd_2360936 : Nat := 404098320834493353580753

theorem tailTrace_2360936 : CollatzResearch.WordTrace tailWord_2360936 prefixEnd_2360936 404098320834493353580753 := by
  unfold tailWord_2360936
  simp only [CollatzResearch.WordTrace]
  refine ⟨43055205087369781306131331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57406940116493041741508441 43055205087369781306131331)
  ·
    refine ⟨64582807631054671959196997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43055205087369781306131331 64582807631054671959196997)
    ·
      refine ⟨12109276430822750992349437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64582807631054671959196997 12109276430822750992349437)
      ·
        refine ⟨4540978661558531622131039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12109276430822750992349437 4540978661558531622131039)
        ·
          refine ⟨6811467992337797433196559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4540978661558531622131039 6811467992337797433196559)
          ·
            refine ⟨10217201988506696149794839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6811467992337797433196559 10217201988506696149794839)
            ·
              refine ⟨15325802982760044224692259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10217201988506696149794839 15325802982760044224692259)
              ·
                refine ⟨22988704474140066337038389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15325802982760044224692259 22988704474140066337038389)
                ·
                  refine ⟨2155191044450631219097349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22988704474140066337038389 2155191044450631219097349)
                  ·
                    refine ⟨404098320834493353580753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2155191044450631219097349 404098320834493353580753)
                    ·
                      rfl

theorem cell23_2360936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_2360936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360936 prefixEnd_2360936 := by exact prefixLift 2360936
  have htrace : WordTrace (prefixWord ++ tailWord_2360936) baseStart_2360936 baseEnd_2360936 := by
    simpa [prefixWord, tailWord_2360936, baseEnd_2360936] using wordTrace_append hprefix tailTrace_2360936
  have hstable : (prefixWord ++ tailWord_2360936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360936).length < 2 ^ (prefixWord ++ tailWord_2360936).sum := by decide
  have hdescent : baseEnd_2360936 < baseStart_2360936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360946 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_2360946 : Nat := 118140960795 + 2360946 * 2 ^ 59
def prefixEnd_2360946 : Nat := 4983230072969 + 3 ^ 40 * 2360946 * 2
def baseEnd_2360946 : Nat := 1212300097310025021617213

theorem tailTrace_2360946 : CollatzResearch.WordTrace tailWord_2360946 prefixEnd_2360946 1212300097310025021617213 := by
  unfold tailWord_2360946
  simp only [CollatzResearch.WordTrace]
  refine ⟨21527693726175833580031673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57407183269802222880084461 21527693726175833580031673)
  ·
    refine ⟨16145770294631875185023755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21527693726175833580031673 16145770294631875185023755)
    ·
      refine ⟨24218655441947812777535633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16145770294631875185023755 24218655441947812777535633)
      ·
        refine ⟨18163991581460859583151725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24218655441947812777535633 18163991581460859583151725)
        ·
          refine ⟨6811496843047822343681897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18163991581460859583151725 6811496843047822343681897)
          ·
            refine ⟨5108622632285866757761423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6811496843047822343681897 5108622632285866757761423)
            ·
              refine ⟨7662933948428800136642135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5108622632285866757761423 7662933948428800136642135)
              ·
                refine ⟨11494400922643200204963203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7662933948428800136642135 11494400922643200204963203)
                ·
                  refine ⟨17241601383964800307444805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11494400922643200204963203 17241601383964800307444805)
                  ·
                    refine ⟨3232800259493400057645901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17241601383964800307444805 3232800259493400057645901)
                    ·
                      refine ⟨1212300097310025021617213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3232800259493400057645901 1212300097310025021617213)
                      ·
                        rfl

theorem cell23_2360946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_2360946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360946 prefixEnd_2360946 := by exact prefixLift 2360946
  have htrace : WordTrace (prefixWord ++ tailWord_2360946) baseStart_2360946 baseEnd_2360946 := by
    simpa [prefixWord, tailWord_2360946, baseEnd_2360946] using wordTrace_append hprefix tailTrace_2360946
  have hstable : (prefixWord ++ tailWord_2360946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360946).length < 2 ^ (prefixWord ++ tailWord_2360946).sum := by decide
  have hdescent : baseEnd_2360946 < baseStart_2360946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360952 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_2360952 : Nat := 118140960795 + 2360952 * 2 ^ 59
def prefixEnd_2360952 : Nat := 4983230072969 + 3 ^ 40 * 2360952 * 2
def baseEnd_2360952 : Nat := 1212303178193951998142185

theorem tailTrace_2360952 : CollatzResearch.WordTrace tailWord_2360952 prefixEnd_2360952 1212303178193951998142185 := by
  unfold tailWord_2360952
  simp only [CollatzResearch.WordTrace]
  refine ⟨43055496871340798672422555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57407329161787731563230073 43055496871340798672422555)
  ·
    refine ⟨64583245307011198008633833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43055496871340798672422555 64583245307011198008633833)
    ·
      refine ⟨48437433980258398506475375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64583245307011198008633833 48437433980258398506475375)
      ·
        refine ⟨72656150970387597759713063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48437433980258398506475375 72656150970387597759713063)
        ·
          refine ⟨108984226455581396639569595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72656150970387597759713063 108984226455581396639569595)
          ·
            refine ⟨163476339683372094959354393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108984226455581396639569595 163476339683372094959354393)
            ·
              refine ⟨122607254762529071219515795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163476339683372094959354393 122607254762529071219515795)
              ·
                refine ⟨183910882143793606829273693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122607254762529071219515795 183910882143793606829273693)
                ·
                  refine ⟨68966580803922602560977635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 183910882143793606829273693 68966580803922602560977635)
                  ·
                    refine ⟨103449871205883903841466453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 68966580803922602560977635 103449871205883903841466453)
                    ·
                      refine ⟨1212303178193951998142185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 103449871205883903841466453 1212303178193951998142185)
                      ·
                        rfl

theorem cell23_2360952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_2360952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360952 prefixEnd_2360952 := by exact prefixLift 2360952
  have htrace : WordTrace (prefixWord ++ tailWord_2360952) baseStart_2360952 baseEnd_2360952 := by
    simpa [prefixWord, tailWord_2360952, baseEnd_2360952] using wordTrace_append hprefix tailTrace_2360952
  have hstable : (prefixWord ++ tailWord_2360952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360952).length < 2 ^ (prefixWord ++ tailWord_2360952).sum := by decide
  have hdescent : baseEnd_2360952 < baseStart_2360952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360953 : List Nat := [1, 2, 1, 3, 3, 1, 4, 3, 1, 4]
def baseStart_2360953 : Nat := 118140960795 + 2360953 * 2 ^ 59
def prefixEnd_2360953 : Nat := 4983230072969 + 3 ^ 40 * 2360953 * 2
def baseEnd_2360953 : Nat := 404101230558202164743227

theorem tailTrace_2360953 : CollatzResearch.WordTrace tailWord_2360953 prefixEnd_2360953 404101230558202164743227 := by
  unfold tailWord_2360953
  simp only [CollatzResearch.WordTrace]
  refine ⟨86111030215677974515631513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57407353477118649677087675 86111030215677974515631513)
  ·
    refine ⟨64583272661758480886723635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86111030215677974515631513 64583272661758480886723635)
    ·
      refine ⟨96874908992637721330085453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64583272661758480886723635 96874908992637721330085453)
      ·
        refine ⟨36328090872239145498782045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96874908992637721330085453 36328090872239145498782045)
        ·
          refine ⟨13623034077089679562043267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36328090872239145498782045 13623034077089679562043267)
          ·
            refine ⟨20434551115634519343064901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13623034077089679562043267 20434551115634519343064901)
            ·
              refine ⟨3831478334181472376824669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20434551115634519343064901 3831478334181472376824669)
              ·
                refine ⟨1436804375318052141309251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3831478334181472376824669 1436804375318052141309251)
                ·
                  refine ⟨2155206562977078211963877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436804375318052141309251 2155206562977078211963877)
                  ·
                    refine ⟨404101230558202164743227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2155206562977078211963877 404101230558202164743227)
                    ·
                      rfl

theorem cell23_2360953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 3, 1, 4].length) (baseStart_2360953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360953 prefixEnd_2360953 := by exact prefixLift 2360953
  have htrace : WordTrace (prefixWord ++ tailWord_2360953) baseStart_2360953 baseEnd_2360953 := by
    simpa [prefixWord, tailWord_2360953, baseEnd_2360953] using wordTrace_append hprefix tailTrace_2360953
  have hstable : (prefixWord ++ tailWord_2360953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360953).length < 2 ^ (prefixWord ++ tailWord_2360953).sum := by decide
  have hdescent : baseEnd_2360953 < baseStart_2360953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360993 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_2360993 : Nat := 118140960795 + 2360993 * 2 ^ 59
def prefixEnd_2360993 : Nat := 4983230072969 + 3 ^ 40 * 2360993 * 2
def baseEnd_2360993 : Nat := 1212324230900786337729497

theorem tailTrace_2360993 : CollatzResearch.WordTrace tailWord_2360993 prefixEnd_2360993 1212324230900786337729497 := by
  unfold tailWord_2360993
  simp only [CollatzResearch.WordTrace]
  refine ⟨86112489135533061347087633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57408326090355374231391755 86112489135533061347087633)
  ·
    refine ⟨64584366851649796010315725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86112489135533061347087633 64584366851649796010315725)
    ·
      refine ⟨24219137569368673503868397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64584366851649796010315725 24219137569368673503868397)
      ·
        refine ⟨9082176588513252563950649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24219137569368673503868397 9082176588513252563950649)
        ·
          refine ⟨6811632441384939422962987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9082176588513252563950649 6811632441384939422962987)
          ·
            refine ⟨10217448662077409134444481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6811632441384939422962987 10217448662077409134444481)
            ·
              refine ⟨7663086496558056850833361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10217448662077409134444481 7663086496558056850833361)
              ·
                refine ⟨5747314872418542638125021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7663086496558056850833361 5747314872418542638125021)
                ·
                  refine ⟨2155243077156953489296883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5747314872418542638125021 2155243077156953489296883)
                  ·
                    refine ⟨3232864615735430233945325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2155243077156953489296883 3232864615735430233945325)
                    ·
                      refine ⟨1212324230900786337729497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3232864615735430233945325 1212324230900786337729497)
                      ·
                        rfl

theorem cell23_2360993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_2360993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360993 prefixEnd_2360993 := by exact prefixLift 2360993
  have htrace : WordTrace (prefixWord ++ tailWord_2360993) baseStart_2360993 baseEnd_2360993 := by
    simpa [prefixWord, tailWord_2360993, baseEnd_2360993] using wordTrace_append hprefix tailTrace_2360993
  have hstable : (prefixWord ++ tailWord_2360993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360993).length < 2 ^ (prefixWord ++ tailWord_2360993).sum := by decide
  have hdescent : baseEnd_2360993 < baseStart_2360993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2360996 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_2360996 : Nat := 118140960795 + 2360996 * 2 ^ 59
def prefixEnd_2360996 : Nat := 4983230072969 + 3 ^ 40 * 2360996 * 2
def baseEnd_2360996 : Nat := 404108590447583275330661

theorem tailTrace_2360996 : CollatzResearch.WordTrace tailWord_2360996 prefixEnd_2360996 404108590447583275330661 := by
  unfold tailWord_2360996
  simp only [CollatzResearch.WordTrace]
  refine ⟨43056299277261096429723421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57408399036348128572964561 43056299277261096429723421)
  ·
    refine ⟨16146112228972911161146283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43056299277261096429723421 16146112228972911161146283)
    ·
      refine ⟨24219168343459366741719425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16146112228972911161146283 24219168343459366741719425)
      ·
        refine ⟨18164376257594525056289569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24219168343459366741719425 18164376257594525056289569)
        ·
          refine ⟨13623282193195893792217177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18164376257594525056289569 13623282193195893792217177)
          ·
            refine ⟨10217461644896920344162883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13623282193195893792217177 10217461644896920344162883)
            ·
              refine ⟨15326192467345380516244325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10217461644896920344162883 15326192467345380516244325)
              ·
                refine ⟨2873661087627258846795811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15326192467345380516244325 2873661087627258846795811)
                ·
                  refine ⟨4310491631440888270193717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2873661087627258846795811 4310491631440888270193717)
                  ·
                    refine ⟨404108590447583275330661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4310491631440888270193717 404108590447583275330661)
                    ·
                      rfl

theorem cell23_2360996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_2360996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2360996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2360996 prefixEnd_2360996 := by exact prefixLift 2360996
  have htrace : WordTrace (prefixWord ++ tailWord_2360996) baseStart_2360996 baseEnd_2360996 := by
    simpa [prefixWord, tailWord_2360996, baseEnd_2360996] using wordTrace_append hprefix tailTrace_2360996
  have hstable : (prefixWord ++ tailWord_2360996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2360996).length < 2 ^ (prefixWord ++ tailWord_2360996).sum := by decide
  have hdescent : baseEnd_2360996 < baseStart_2360996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2360996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361010 : List Nat := [3, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3]
def baseStart_2361010 : Nat := 118140960795 + 2361010 * 2 ^ 59
def prefixEnd_2361010 : Nat := 4983230072969 + 3 ^ 40 * 2361010 * 2
def baseEnd_2361010 : Nat := 1212332960071912771216919

theorem tailTrace_2361010 : CollatzResearch.WordTrace tailWord_2361010 prefixEnd_2361010 1212332960071912771216919 := by
  unfold tailWord_2361010
  simp only [CollatzResearch.WordTrace]
  refine ⟨21528277294117868312614121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57408739450980982166970989 21528277294117868312614121)
  ·
    refine ⟨16146207970588401234460591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21528277294117868312614121 16146207970588401234460591)
    ·
      refine ⟨24219311955882601851690887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16146207970588401234460591 24219311955882601851690887)
      ·
        refine ⟨36328967933823902777536331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24219311955882601851690887 36328967933823902777536331)
        ·
          refine ⟨54493451900735854166304497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36328967933823902777536331 54493451900735854166304497)
          ·
            refine ⟨40870088925551890624728373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54493451900735854166304497 40870088925551890624728373)
            ·
              refine ⟨3831570836770489746068285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40870088925551890624728373 3831570836770489746068285)
              ·
                refine ⟨1436839063788933654775607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3831570836770489746068285 1436839063788933654775607)
                ·
                  refine ⟨2155258595683400482163411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436839063788933654775607 2155258595683400482163411)
                  ·
                    refine ⟨3232887893525100723245117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2155258595683400482163411 3232887893525100723245117)
                    ·
                      refine ⟨1212332960071912771216919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3232887893525100723245117 1212332960071912771216919)
                      ·
                        rfl

theorem cell23_2361010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_2361010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361010 prefixEnd_2361010 := by exact prefixLift 2361010
  have htrace : WordTrace (prefixWord ++ tailWord_2361010) baseStart_2361010 baseEnd_2361010 := by
    simpa [prefixWord, tailWord_2361010, baseEnd_2361010] using wordTrace_append hprefix tailTrace_2361010
  have hstable : (prefixWord ++ tailWord_2361010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361010).length < 2 ^ (prefixWord ++ tailWord_2361010).sum := by decide
  have hdescent : baseEnd_2361010 < baseStart_2361010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361029 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_2361029 : Nat := 118140960795 + 2361029 * 2 ^ 59
def prefixEnd_2361029 : Nat := 4983230072969 + 3 ^ 40 * 2361029 * 2
def baseEnd_2361029 : Nat := 1212342716204348196879331

theorem tailTrace_2361029 : CollatzResearch.WordTrace tailWord_2361029 prefixEnd_2361029 1212342716204348196879331 := by
  unfold tailWord_2361029
  simp only [CollatzResearch.WordTrace]
  refine ⟨86113802163402639495398141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57409201442268426330265427 86113802163402639495398141)
  ·
    refine ⟨32292675811275989810774303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86113802163402639495398141 32292675811275989810774303)
    ·
      refine ⟨48439013716913984716161455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32292675811275989810774303 48439013716913984716161455)
      ·
        refine ⟨72658520575370977074242183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48439013716913984716161455 72658520575370977074242183)
        ·
          refine ⟨108987780863056465611363275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72658520575370977074242183 108987780863056465611363275)
          ·
            refine ⟨163481671294584698417044913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108987780863056465611363275 163481671294584698417044913)
            ·
              refine ⟨122611253470938523812783685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163481671294584698417044913 122611253470938523812783685)
              ·
                refine ⟨22989610025800973214896941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122611253470938523812783685 22989610025800973214896941)
                ·
                  refine ⟨8621103759675364955586353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22989610025800973214896941 8621103759675364955586353)
                  ·
                    refine ⟨6465827819756523716689765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8621103759675364955586353 6465827819756523716689765)
                    ·
                      refine ⟨1212342716204348196879331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6465827819756523716689765 1212342716204348196879331)
                      ·
                        rfl

theorem cell23_2361029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_2361029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361029 prefixEnd_2361029 := by exact prefixLift 2361029
  have htrace : WordTrace (prefixWord ++ tailWord_2361029) baseStart_2361029 baseEnd_2361029 := by
    simpa [prefixWord, tailWord_2361029, baseEnd_2361029] using wordTrace_append hprefix tailTrace_2361029
  have hstable : (prefixWord ++ tailWord_2361029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361029).length < 2 ^ (prefixWord ++ tailWord_2361029).sum := by decide
  have hdescent : baseEnd_2361029 < baseStart_2361029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361066 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_2361066 : Nat := 118140960795 + 2361066 * 2 ^ 59
def prefixEnd_2361066 : Nat := 4983230072969 + 3 ^ 40 * 2361066 * 2
def baseEnd_2361066 : Nat := 1212361714988564552116661

theorem tailTrace_2361066 : CollatzResearch.WordTrace tailWord_2361066 prefixEnd_2361066 1212361714988564552116661 := by
  unfold tailWord_2361066
  simp only [CollatzResearch.WordTrace]
  refine ⟨21528787916067148703623763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57410101109512396542996701 21528787916067148703623763)
  ·
    refine ⟨32293181874100723055435645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21528787916067148703623763 32293181874100723055435645)
    ·
      refine ⟨12109943202787771145788367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32293181874100723055435645 12109943202787771145788367)
      ·
        refine ⟨18164914804181656718682551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12109943202787771145788367 18164914804181656718682551)
        ·
          refine ⟨27247372206272485078023827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18164914804181656718682551 27247372206272485078023827)
          ·
            refine ⟨40871058309408727617035741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27247372206272485078023827 40871058309408727617035741)
            ·
              refine ⟨15326646866028272856388403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40871058309408727617035741 15326646866028272856388403)
              ·
                refine ⟨22989970299042409284582605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15326646866028272856388403 22989970299042409284582605)
                ·
                  refine ⟨8621238862140903481718477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22989970299042409284582605 8621238862140903481718477)
                  ·
                    refine ⟨3232964573302838805644429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8621238862140903481718477 3232964573302838805644429)
                    ·
                      refine ⟨1212361714988564552116661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3232964573302838805644429 1212361714988564552116661)
                      ·
                        rfl

theorem cell23_2361066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_2361066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361066 prefixEnd_2361066 := by exact prefixLift 2361066
  have htrace : WordTrace (prefixWord ++ tailWord_2361066) baseStart_2361066 baseEnd_2361066 := by
    simpa [prefixWord, tailWord_2361066, baseEnd_2361066] using wordTrace_append hprefix tailTrace_2361066
  have hstable : (prefixWord ++ tailWord_2361066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361066).length < 2 ^ (prefixWord ++ tailWord_2361066).sum := by decide
  have hdescent : baseEnd_2361066 < baseStart_2361066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361070 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_2361070 : Nat := 118140960795 + 2361070 * 2 ^ 59
def prefixEnd_2361070 : Nat := 4983230072969 + 3 ^ 40 * 2361070 * 2
def baseEnd_2361070 : Nat := 1212363768911182536466643

theorem tailTrace_2361070 : CollatzResearch.WordTrace tailWord_2361070 prefixEnd_2361070 1212363768911182536466643 := by
  unfold tailWord_2361070
  simp only [CollatzResearch.WordTrace]
  refine ⟨10764412194531762937205083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57410198370836068998427109 10764412194531762937205083)
  ·
    refine ⟨16146618291797644405807625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10764412194531762937205083 16146618291797644405807625)
    ·
      refine ⟨12109963718848233304355719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16146618291797644405807625 12109963718848233304355719)
      ·
        refine ⟨18164945578272349956533579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12109963718848233304355719 18164945578272349956533579)
        ·
          refine ⟨27247418367408524934800369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18164945578272349956533579 27247418367408524934800369)
          ·
            refine ⟨20435563775556393701100277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27247418367408524934800369 20435563775556393701100277)
            ·
              refine ⟨1915834103958411909478151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20435563775556393701100277 1915834103958411909478151)
              ·
                refine ⟨2873751155937617864217227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1915834103958411909478151 2873751155937617864217227)
                ·
                  refine ⟨4310626733906426796325841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2873751155937617864217227 4310626733906426796325841)
                  ·
                    refine ⟨3232970050429820097244381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4310626733906426796325841 3232970050429820097244381)
                    ·
                      refine ⟨1212363768911182536466643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3232970050429820097244381 1212363768911182536466643)
                      ·
                        rfl

theorem cell23_2361070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_2361070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361070 prefixEnd_2361070 := by exact prefixLift 2361070
  have htrace : WordTrace (prefixWord ++ tailWord_2361070) baseStart_2361070 baseEnd_2361070 := by
    simpa [prefixWord, tailWord_2361070, baseEnd_2361070] using wordTrace_append hprefix tailTrace_2361070
  have hstable : (prefixWord ++ tailWord_2361070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361070).length < 2 ^ (prefixWord ++ tailWord_2361070).sum := by decide
  have hdescent : baseEnd_2361070 < baseStart_2361070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361079 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_2361079 : Nat := 118140960795 + 2361079 * 2 ^ 59
def prefixEnd_2361079 : Nat := 4983230072969 + 3 ^ 40 * 2361079 * 2
def baseEnd_2361079 : Nat := 1212368390237073001254101

theorem tailTrace_2361079 : CollatzResearch.WordTrace tailWord_2361079 prefixEnd_2361079 1212368390237073001254101 := by
  unfold tailWord_2361079
  simp only [CollatzResearch.WordTrace]
  refine ⟨86115625813221498034718291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57410417208814332023145527 86115625813221498034718291)
  ·
    refine ⟨129173438719832247052077437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86115625813221498034718291 129173438719832247052077437)
    ·
      refine ⟨48440039519937092644529039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129173438719832247052077437 48440039519937092644529039)
      ·
        refine ⟨72660059279905638966793559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48440039519937092644529039 72660059279905638966793559)
        ·
          refine ⟨108990088919858458450190339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72660059279905638966793559 108990088919858458450190339)
          ·
            refine ⟨163485133379787687675285509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108990088919858458450190339 163485133379787687675285509)
            ·
              refine ⟨30653462508710191439116033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163485133379787687675285509 30653462508710191439116033)
              ·
                refine ⟨22990096881532643579337025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30653462508710191439116033 22990096881532643579337025)
                ·
                  refine ⟨17242572661149482684502769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22990096881532643579337025 17242572661149482684502769)
                  ·
                    refine ⟨12931929495862112013377077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17242572661149482684502769 12931929495862112013377077)
                    ·
                      refine ⟨1212368390237073001254101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12931929495862112013377077 1212368390237073001254101)
                      ·
                        rfl

theorem cell23_2361079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_2361079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361079 prefixEnd_2361079 := by exact prefixLift 2361079
  have htrace : WordTrace (prefixWord ++ tailWord_2361079) baseStart_2361079 baseEnd_2361079 := by
    simpa [prefixWord, tailWord_2361079, baseEnd_2361079] using wordTrace_append hprefix tailTrace_2361079
  have hstable : (prefixWord ++ tailWord_2361079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361079).length < 2 ^ (prefixWord ++ tailWord_2361079).sum := by decide
  have hdescent : baseEnd_2361079 < baseStart_2361079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361099 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 1, 8]
def baseStart_2361099 : Nat := 118140960795 + 2361099 * 2 ^ 59
def prefixEnd_2361099 : Nat := 4983230072969 + 3 ^ 40 * 2361099 * 2
def baseEnd_2361099 : Nat := 404126219950054307668003

theorem tailTrace_2361099 : CollatzResearch.WordTrace tailWord_2361099 prefixEnd_2361099 404126219950054307668003 := by
  unfold tailWord_2361099
  simp only [CollatzResearch.WordTrace]
  refine ⟨86116355273149041450446351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57410903515432694300297567 86116355273149041450446351)
  ·
    refine ⟨129174532909723562175669527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86116355273149041450446351 129174532909723562175669527)
    ·
      refine ⟨193761799364585343263504291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129174532909723562175669527 193761799364585343263504291)
      ·
        refine ⟨290642699046878014895256437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193761799364585343263504291 290642699046878014895256437)
        ·
          refine ⟨27247753035644813896430291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 290642699046878014895256437 27247753035644813896430291)
          ·
            refine ⟨40871629553467220844645437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27247753035644813896430291 40871629553467220844645437)
            ·
              refine ⟨15326861082550207816742039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40871629553467220844645437 15326861082550207816742039)
              ·
                refine ⟨22990291623825311725113059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15326861082550207816742039 22990291623825311725113059)
                ·
                  refine ⟨34485437435737967587669589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22990291623825311725113059 34485437435737967587669589)
                  ·
                    refine ⟨404126219950054307668003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34485437435737967587669589 404126219950054307668003)
                    ·
                      rfl

theorem cell23_2361099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 8].length) (baseStart_2361099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361099 prefixEnd_2361099 := by exact prefixLift 2361099
  have htrace : WordTrace (prefixWord ++ tailWord_2361099) baseStart_2361099 baseEnd_2361099 := by
    simpa [prefixWord, tailWord_2361099, baseEnd_2361099] using wordTrace_append hprefix tailTrace_2361099
  have hstable : (prefixWord ++ tailWord_2361099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361099).length < 2 ^ (prefixWord ++ tailWord_2361099).sum := by decide
  have hdescent : baseEnd_2361099 < baseStart_2361099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361118 : List Nat := [4, 3, 2, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2361118 : Nat := 118140960795 + 2361118 * 2 ^ 59
def prefixEnd_2361118 : Nat := 4983230072969 + 3 ^ 40 * 2361118 * 2
def baseEnd_2361118 : Nat := 1212388415982598348666423

theorem tailTrace_2361118 : CollatzResearch.WordTrace tailWord_2361118 prefixEnd_2361118 1212388415982598348666423 := by
  unfold tailWord_2361118
  simp only [CollatzResearch.WordTrace]
  refine ⟨10764631032510025961923501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57411365506720138463592005 10764631032510025961923501)
  ·
    refine ⟨4036736637191259735721313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10764631032510025961923501 4036736637191259735721313)
    ·
      refine ⟨3027552477893444801790985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4036736637191259735721313 3027552477893444801790985)
      ·
        refine ⟨2270664358420083601343239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3027552477893444801790985 2270664358420083601343239)
        ·
          refine ⟨3405996537630125402014859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270664358420083601343239 3405996537630125402014859)
          ·
            refine ⟨5108994806445188103022289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405996537630125402014859 5108994806445188103022289)
            ·
              refine ⟨3831746104833891077266717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5108994806445188103022289 3831746104833891077266717)
              ·
                refine ⟨1436904789312709153975019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3831746104833891077266717 1436904789312709153975019)
                ·
                  refine ⟨2155357183969063730962529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1436904789312709153975019 2155357183969063730962529)
                  ·
                    refine ⟨1616517887976797798221897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2155357183969063730962529 1616517887976797798221897)
                    ·
                      refine ⟨1212388415982598348666423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616517887976797798221897 1212388415982598348666423)
                      ·
                        rfl

theorem cell23_2361118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2361118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361118 prefixEnd_2361118 := by exact prefixLift 2361118
  have htrace : WordTrace (prefixWord ++ tailWord_2361118) baseStart_2361118 baseEnd_2361118 := by
    simpa [prefixWord, tailWord_2361118, baseEnd_2361118] using wordTrace_append hprefix tailTrace_2361118
  have hstable : (prefixWord ++ tailWord_2361118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361118).length < 2 ^ (prefixWord ++ tailWord_2361118).sum := by decide
  have hdescent : baseEnd_2361118 < baseStart_2361118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361123 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 1, 4, 2]
def baseStart_2361123 : Nat := 118140960795 + 2361123 * 2 ^ 59
def prefixEnd_2361123 : Nat := 4983230072969 + 3 ^ 40 * 2361123 * 2
def baseEnd_2361123 : Nat := 1212390983385870829103899

theorem tailTrace_2361123 : CollatzResearch.WordTrace tailWord_2361123 prefixEnd_2361123 1212390983385870829103899 := by
  unfold tailWord_2361123
  simp only [CollatzResearch.WordTrace]
  refine ⟨86117230625062093549320023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57411487083374729032880015 86117230625062093549320023)
  ·
    refine ⟨129175845937593140323980035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86117230625062093549320023 129175845937593140323980035)
    ·
      refine ⟨193763768906389710485970053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129175845937593140323980035 193763768906389710485970053)
      ·
        refine ⟨36330706669948070716119385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193763768906389710485970053 36330706669948070716119385)
        ·
          refine ⟨27248030002461053037089539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36330706669948070716119385 27248030002461053037089539)
          ·
            refine ⟨40872045003691579555634309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27248030002461053037089539 40872045003691579555634309)
            ·
              refine ⟨7663508438192171166681433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40872045003691579555634309 7663508438192171166681433)
              ·
                refine ⟨5747631328644128375011075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7663508438192171166681433 5747631328644128375011075)
                ·
                  refine ⟨8621446992966192562516613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5747631328644128375011075 8621446992966192562516613)
                  ·
                    refine ⟨1616521311181161105471865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8621446992966192562516613 1616521311181161105471865)
                    ·
                      refine ⟨1212390983385870829103899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616521311181161105471865 1212390983385870829103899)
                      ·
                        rfl

theorem cell23_2361123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_2361123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361123 prefixEnd_2361123 := by exact prefixLift 2361123
  have htrace : WordTrace (prefixWord ++ tailWord_2361123) baseStart_2361123 baseEnd_2361123 := by
    simpa [prefixWord, tailWord_2361123, baseEnd_2361123] using wordTrace_append hprefix tailTrace_2361123
  have hstable : (prefixWord ++ tailWord_2361123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361123).length < 2 ^ (prefixWord ++ tailWord_2361123).sum := by decide
  have hdescent : baseEnd_2361123 < baseStart_2361123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361134 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_2361134 : Nat := 118140960795 + 2361134 * 2 ^ 59
def prefixEnd_2361134 : Nat := 4983230072969 + 3 ^ 40 * 2361134 * 2
def baseEnd_2361134 : Nat := 1212396631673070286066349

theorem tailTrace_2361134 : CollatzResearch.WordTrace tailWord_2361134 prefixEnd_2361134 1212396631673070286066349 := by
  unfold tailWord_2361134
  simp only [CollatzResearch.WordTrace]
  refine ⟨10764703978502780303496307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57411754552014828285313637 10764703978502780303496307)
  ·
    refine ⟨16147055967754170455244461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10764703978502780303496307 16147055967754170455244461)
    ·
      refine ⟨6055145987907813920716673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16147055967754170455244461 6055145987907813920716673)
      ·
        refine ⟨4541359490930860440537505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6055145987907813920716673 4541359490930860440537505)
        ·
          refine ⟨3406019618198145330403129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4541359490930860440537505 3406019618198145330403129)
          ·
            refine ⟨2554514713648608997802347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3406019618198145330403129 2554514713648608997802347)
            ·
              refine ⟨3831772070472913496703521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554514713648608997802347 3831772070472913496703521)
              ·
                refine ⟨2873829052854685122527641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3831772070472913496703521 2873829052854685122527641)
                ·
                  refine ⟨2155371789641013841895731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2873829052854685122527641 2155371789641013841895731)
                  ·
                    refine ⟨3233057684461520762843597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2155371789641013841895731 3233057684461520762843597)
                    ·
                      refine ⟨1212396631673070286066349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3233057684461520762843597 1212396631673070286066349)
                      ·
                        rfl

theorem cell23_2361134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_2361134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361134 prefixEnd_2361134 := by exact prefixLift 2361134
  have htrace : WordTrace (prefixWord ++ tailWord_2361134) baseStart_2361134 baseEnd_2361134 := by
    simpa [prefixWord, tailWord_2361134, baseEnd_2361134] using wordTrace_append hprefix tailTrace_2361134
  have hstable : (prefixWord ++ tailWord_2361134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361134).length < 2 ^ (prefixWord ++ tailWord_2361134).sum := by decide
  have hdescent : baseEnd_2361134 < baseStart_2361134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361146 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 7]
def baseStart_2361146 : Nat := 118140960795 + 2361146 * 2 ^ 59
def prefixEnd_2361146 : Nat := 4983230072969 + 3 ^ 40 * 2361146 * 2
def baseEnd_2361146 : Nat := 134711421493436026568477

theorem tailTrace_2361146 : CollatzResearch.WordTrace tailWord_2361146 prefixEnd_2361146 134711421493436026568477 := by
  unfold tailWord_2361146
  simp only [CollatzResearch.WordTrace]
  refine ⟨21529517375994692119351823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57412046335985845651604861 21529517375994692119351823)
  ·
    refine ⟨32294276063992038179027735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21529517375994692119351823 32294276063992038179027735)
    ·
      refine ⟨48441414095988057268541603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32294276063992038179027735 48441414095988057268541603)
      ·
        refine ⟨72662121143982085902812405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48441414095988057268541603 72662121143982085902812405)
        ·
          refine ⟨6812073857248320553388663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72662121143982085902812405 6812073857248320553388663)
          ·
            refine ⟨10218110785872480830082995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6812073857248320553388663 10218110785872480830082995)
            ·
              refine ⟨15327166178808721245124493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10218110785872480830082995 15327166178808721245124493)
              ·
                refine ⟨5747687317053270466921685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15327166178808721245124493 5747687317053270466921685)
                ·
                  refine ⟨134711421493436026568477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5747687317053270466921685 134711421493436026568477)
                  ·
                    rfl

theorem cell23_2361146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_2361146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361146 prefixEnd_2361146 := by exact prefixLift 2361146
  have htrace : WordTrace (prefixWord ++ tailWord_2361146) baseStart_2361146 baseEnd_2361146 := by
    simpa [prefixWord, tailWord_2361146, baseEnd_2361146] using wordTrace_append hprefix tailTrace_2361146
  have hstable : (prefixWord ++ tailWord_2361146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361146).length < 2 ^ (prefixWord ++ tailWord_2361146).sum := by decide
  have hdescent : baseEnd_2361146 < baseStart_2361146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361157 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 2, 2, 2]
def baseStart_2361157 : Nat := 118140960795 + 2361157 * 2 ^ 59
def prefixEnd_2361157 : Nat := 4983230072969 + 3 ^ 40 * 2361157 * 2
def baseEnd_2361157 : Nat := 1212408441728123696078743

theorem tailTrace_2361157 : CollatzResearch.WordTrace tailWord_2361157 prefixEnd_2361157 1212408441728123696078743 := by
  unfold tailWord_2361157
  simp only [CollatzResearch.WordTrace]
  refine ⟨86118470706938917356057725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57412313804625944904038483 86118470706938917356057725)
  ·
    refine ⟨32294426515102094008521647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86118470706938917356057725 32294426515102094008521647)
    ·
      refine ⟨48441639772653141012782471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32294426515102094008521647 48441639772653141012782471)
      ·
        refine ⟨72662459658979711519173707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48441639772653141012782471 72662459658979711519173707)
        ·
          refine ⟨108993689488469567278760561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72662459658979711519173707 108993689488469567278760561)
          ·
            refine ⟨81745267116352175459070421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108993689488469567278760561 81745267116352175459070421)
            ·
              refine ⟨1915904698039504112321963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 81745267116352175459070421 1915904698039504112321963)
              ·
                refine ⟨2873857047059256168482945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1915904698039504112321963 2873857047059256168482945)
                ·
                  refine ⟨2155392785294442126362209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2873857047059256168482945 2155392785294442126362209)
                  ·
                    refine ⟨1616544588970831594771657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2155392785294442126362209 1616544588970831594771657)
                    ·
                      refine ⟨1212408441728123696078743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616544588970831594771657 1212408441728123696078743)
                      ·
                        rfl

theorem cell23_2361157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 2, 2, 2].length) (baseStart_2361157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361157 prefixEnd_2361157 := by exact prefixLift 2361157
  have htrace : WordTrace (prefixWord ++ tailWord_2361157) baseStart_2361157 baseEnd_2361157 := by
    simpa [prefixWord, tailWord_2361157, baseEnd_2361157] using wordTrace_append hprefix tailTrace_2361157
  have hstable : (prefixWord ++ tailWord_2361157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361157).length < 2 ^ (prefixWord ++ tailWord_2361157).sum := by decide
  have hdescent : baseEnd_2361157 < baseStart_2361157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361213 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 1, 6, 2]
def baseStart_2361213 : Nat := 118140960795 + 2361213 * 2 ^ 59
def prefixEnd_2361213 : Nat := 4983230072969 + 3 ^ 40 * 2361213 * 2
def baseEnd_2361213 : Nat := 1212437196644775476978485

theorem tailTrace_2361213 : CollatzResearch.WordTrace tailWord_2361213 prefixEnd_2361213 1212437196644775476978485 := by
  unfold tailWord_2361213
  simp only [CollatzResearch.WordTrace]
  refine ⟨86120513194736038920096293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57413675463157359280064195 86120513194736038920096293)
  ·
    refine ⟨16147596224013007297518055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86120513194736038920096293 16147596224013007297518055)
    ·
      refine ⟨24221394336019510946277083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16147596224013007297518055 24221394336019510946277083)
      ·
        refine ⟨36332091504029266419415625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24221394336019510946277083 36332091504029266419415625)
        ·
          refine ⟨27249068628021949814561719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36332091504029266419415625 27249068628021949814561719)
          ·
            refine ⟨40873602942032924721842579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27249068628021949814561719 40873602942032924721842579)
            ·
              refine ⟨61310404413049387082763869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40873602942032924721842579 61310404413049387082763869)
              ·
                refine ⟨22991401654893520156036451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61310404413049387082763869 22991401654893520156036451)
                ·
                  refine ⟨34487102482340280234054677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22991401654893520156036451 34487102482340280234054677)
                  ·
                    refine ⟨1616582928859700635971313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 34487102482340280234054677 1616582928859700635971313)
                    ·
                      refine ⟨1212437196644775476978485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616582928859700635971313 1212437196644775476978485)
                      ·
                        rfl

theorem cell23_2361213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_2361213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361213 prefixEnd_2361213 := by exact prefixLift 2361213
  have htrace : WordTrace (prefixWord ++ tailWord_2361213) baseStart_2361213 baseEnd_2361213 := by
    simpa [prefixWord, tailWord_2361213, baseEnd_2361213] using wordTrace_append hprefix tailTrace_2361213
  have hstable : (prefixWord ++ tailWord_2361213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361213).length < 2 ^ (prefixWord ++ tailWord_2361213).sum := by decide
  have hdescent : baseEnd_2361213 < baseStart_2361213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361233 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 3]
def baseStart_2361233 : Nat := 118140960795 + 2361233 * 2 ^ 59
def prefixEnd_2361233 : Nat := 4983230072969 + 3 ^ 40 * 2361233 * 2
def baseEnd_2361233 : Nat := 1212447466257865398728393

theorem tailTrace_2361233 : CollatzResearch.WordTrace tailWord_2361233 prefixEnd_2361233 1212447466257865398728393 := by
  unfold tailWord_2361233
  simp only [CollatzResearch.WordTrace]
  refine ⟨86121242654663582335824353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57414161769775721557216235 86121242654663582335824353)
  ·
    refine ⟨64590931990997686751868265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86121242654663582335824353 64590931990997686751868265)
    ·
      refine ⟨48443198993248265063901199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64590931990997686751868265 48443198993248265063901199)
      ·
        refine ⟨72664798489872397595851799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48443198993248265063901199 72664798489872397595851799)
        ·
          refine ⟨108997197734808596393777699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72664798489872397595851799 108997197734808596393777699)
          ·
            refine ⟨163495796602212894590666549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108997197734808596393777699 163495796602212894590666549)
            ·
              refine ⟨15327730931457458867874989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163495796602212894590666549 15327730931457458867874989)
              ·
                refine ⟨5747899099296547075453121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15327730931457458867874989 5747899099296547075453121)
                ·
                  refine ⟨4310924324472410306589841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5747899099296547075453121 4310924324472410306589841)
                  ·
                    refine ⟨3233193243354307729942381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4310924324472410306589841 3233193243354307729942381)
                    ·
                      refine ⟨1212447466257865398728393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3233193243354307729942381 1212447466257865398728393)
                      ·
                        rfl

theorem cell23_2361233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 3].length) (baseStart_2361233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361233 prefixEnd_2361233 := by exact prefixLift 2361233
  have htrace : WordTrace (prefixWord ++ tailWord_2361233) baseStart_2361233 baseEnd_2361233 := by
    simpa [prefixWord, tailWord_2361233, baseEnd_2361233] using wordTrace_append hprefix tailTrace_2361233
  have hstable : (prefixWord ++ tailWord_2361233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361233).length < 2 ^ (prefixWord ++ tailWord_2361233).sum := by decide
  have hdescent : baseEnd_2361233 < baseStart_2361233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361280 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 3, 1, 3]
def baseStart_2361280 : Nat := 118140960795 + 2361280 * 2 ^ 59
def prefixEnd_2361280 : Nat := 4983230072969 + 3 ^ 40 * 2361280 * 2
def baseEnd_2361280 : Nat := 1212471599848626714840677

theorem tailTrace_2361280 : CollatzResearch.WordTrace tailWord_2361280 prefixEnd_2361280 1212471599848626714840677 := by
  unfold tailWord_2361280
  simp only [CollatzResearch.WordTrace]
  refine ⟨43061478442746654681392647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57415304590328872908523529 43061478442746654681392647)
  ·
    refine ⟨64592217664119982022088971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43061478442746654681392647 64592217664119982022088971)
    ·
      refine ⟨96888326496179973033133457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64592217664119982022088971 96888326496179973033133457)
      ·
        refine ⟨72666244872134979774850093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96888326496179973033133457 72666244872134979774850093)
        ·
          refine ⟨27249841827050617415568785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72666244872134979774850093 27249841827050617415568785)
          ·
            refine ⟨20437381370287963061676589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27249841827050617415568785 20437381370287963061676589)
            ·
              refine ⟨7664018013857986148128721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20437381370287963061676589 7664018013857986148128721)
              ·
                refine ⟨5748013510393489611096541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7664018013857986148128721 5748013510393489611096541)
                ·
                  refine ⟨2155505066397558604161203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5748013510393489611096541 2155505066397558604161203)
                  ·
                    refine ⟨3233257599596337906241805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2155505066397558604161203 3233257599596337906241805)
                    ·
                      refine ⟨1212471599848626714840677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3233257599596337906241805 1212471599848626714840677)
                      ·
                        rfl

theorem cell23_2361280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_2361280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361280 prefixEnd_2361280 := by exact prefixLift 2361280
  have htrace : WordTrace (prefixWord ++ tailWord_2361280) baseStart_2361280 baseEnd_2361280 := by
    simpa [prefixWord, tailWord_2361280, baseEnd_2361280] using wordTrace_append hprefix tailTrace_2361280
  have hstable : (prefixWord ++ tailWord_2361280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361280).length < 2 ^ (prefixWord ++ tailWord_2361280).sum := by decide
  have hdescent : baseEnd_2361280 < baseStart_2361280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361300 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_2361300 : Nat := 118140960795 + 2361300 * 2 ^ 59
def prefixEnd_2361300 : Nat := 4983230072969 + 3 ^ 40 * 2361300 * 2
def baseEnd_2361300 : Nat := 404160623153905545530195

theorem tailTrace_2361300 : CollatzResearch.WordTrace tailWord_2361300 prefixEnd_2361300 404160623153905545530195 := by
  unfold tailWord_2361300
  simp only [CollatzResearch.WordTrace]
  refine ⟨43061843172710426389256677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57415790896947235185675569 43061843172710426389256677)
  ·
    refine ⟨8074095594883204947985627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43061843172710426389256677 8074095594883204947985627)
    ·
      refine ⟨12111143392324807421978441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8074095594883204947985627 12111143392324807421978441)
      ·
        refine ⟨9083357544243605566483831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12111143392324807421978441 9083357544243605566483831)
        ·
          refine ⟨13625036316365408349725747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9083357544243605566483831 13625036316365408349725747)
          ·
            refine ⟨20437554474548112524588621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13625036316365408349725747 20437554474548112524588621)
            ·
              refine ⟨7664082927955542196720733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20437554474548112524588621 7664082927955542196720733)
              ·
                refine ⟨2874031097983328323770275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7664082927955542196720733 2874031097983328323770275)
                ·
                  refine ⟨4311046646974992485655413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874031097983328323770275 4311046646974992485655413)
                  ·
                    refine ⟨404160623153905545530195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4311046646974992485655413 404160623153905545530195)
                    ·
                      rfl

theorem cell23_2361300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_2361300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361300 prefixEnd_2361300 := by exact prefixLift 2361300
  have htrace : WordTrace (prefixWord ++ tailWord_2361300) baseStart_2361300 baseEnd_2361300 := by
    simpa [prefixWord, tailWord_2361300, baseEnd_2361300] using wordTrace_append hprefix tailTrace_2361300
  have hstable : (prefixWord ++ tailWord_2361300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361300).length < 2 ^ (prefixWord ++ tailWord_2361300).sum := by decide
  have hdescent : baseEnd_2361300 < baseStart_2361300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361323 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 3]
def baseStart_2361323 : Nat := 118140960795 + 2361323 * 2 ^ 59
def prefixEnd_2361323 : Nat := 4983230072969 + 3 ^ 40 * 2361323 * 2
def baseEnd_2361323 : Nat := 1212493679516770046602979

theorem tailTrace_2361323 : CollatzResearch.WordTrace tailWord_2361323 prefixEnd_2361323 1212493679516770046602979 := by
  unfold tailWord_2361323
  simp only [CollatzResearch.WordTrace]
  refine ⟨86124525224337527706600623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57416350149558351804400415 86124525224337527706600623)
  ·
    refine ⟨129186787836506291559900935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86124525224337527706600623 129186787836506291559900935)
    ·
      refine ⟨193780181754759437339851403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129186787836506291559900935 193780181754759437339851403)
      ·
        refine ⟨290670272632139156009777105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193780181754759437339851403 290670272632139156009777105)
        ·
          refine ⟨218002704474104367007332829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 290670272632139156009777105 218002704474104367007332829)
          ·
            refine ⟨81751014177789137627749811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218002704474104367007332829 81751014177789137627749811)
            ·
              refine ⟨122626521266683706441624717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81751014177789137627749811 122626521266683706441624717)
              ·
                refine ⟨45984945475006389915609269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122626521266683706441624717 45984945475006389915609269)
                ·
                  refine ⟨4311088638281849054588369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45984945475006389915609269 4311088638281849054588369)
                  ·
                    refine ⟨3233316478711386790941277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4311088638281849054588369 3233316478711386790941277)
                    ·
                      refine ⟨1212493679516770046602979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3233316478711386790941277 1212493679516770046602979)
                      ·
                        rfl

theorem cell23_2361323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 2, 3].length) (baseStart_2361323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361323 prefixEnd_2361323 := by exact prefixLift 2361323
  have htrace : WordTrace (prefixWord ++ tailWord_2361323) baseStart_2361323 baseEnd_2361323 := by
    simpa [prefixWord, tailWord_2361323, baseEnd_2361323] using wordTrace_append hprefix tailTrace_2361323
  have hstable : (prefixWord ++ tailWord_2361323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361323).length < 2 ^ (prefixWord ++ tailWord_2361323).sum := by decide
  have hdescent : baseEnd_2361323 < baseStart_2361323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361337 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 3, 2, 2]
def baseStart_2361337 : Nat := 118140960795 + 2361337 * 2 ^ 59
def prefixEnd_2361337 : Nat := 4983230072969 + 3 ^ 40 * 2361337 * 2
def baseEnd_2361337 : Nat := 1212500868245932991827915

theorem tailTrace_2361337 : CollatzResearch.WordTrace tailWord_2361337 prefixEnd_2361337 1212500868245932991827915 := by
  unfold tailWord_2361337
  simp only [CollatzResearch.WordTrace]
  refine ⟨86125035846286808097610265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57416690564191205398406843 86125035846286808097610265)
  ·
    refine ⟨64593776884715106073207699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86125035846286808097610265 64593776884715106073207699)
    ·
      refine ⟨96890665327072659109811549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64593776884715106073207699 96890665327072659109811549)
      ·
        refine ⟨36333999497652247166179331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96890665327072659109811549 36333999497652247166179331)
        ·
          refine ⟨54500999246478370749268997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36333999497652247166179331 54500999246478370749268997)
          ·
            refine ⟨10218937358714694515487937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54500999246478370749268997 10218937358714694515487937)
            ·
              refine ⟨7664203019036020886615953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10218937358714694515487937 7664203019036020886615953)
              ·
                refine ⟨5748152264277015664961965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7664203019036020886615953 5748152264277015664961965)
                ·
                  refine ⟨2155557099103880874360737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5748152264277015664961965 2155557099103880874360737)
                  ·
                    refine ⟨1616667824327910655770553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2155557099103880874360737 1616667824327910655770553)
                    ·
                      refine ⟨1212500868245932991827915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616667824327910655770553 1212500868245932991827915)
                      ·
                        rfl

theorem cell23_2361337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_2361337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361337 prefixEnd_2361337 := by exact prefixLift 2361337
  have htrace : WordTrace (prefixWord ++ tailWord_2361337) baseStart_2361337 baseEnd_2361337 := by
    simpa [prefixWord, tailWord_2361337, baseEnd_2361337] using wordTrace_append hprefix tailTrace_2361337
  have hstable : (prefixWord ++ tailWord_2361337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361337).length < 2 ^ (prefixWord ++ tailWord_2361337).sum := by decide
  have hdescent : baseEnd_2361337 < baseStart_2361337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361348 : List Nat := [2, 3, 2, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2361348 : Nat := 118140960795 + 2361348 * 2 ^ 59
def prefixEnd_2361348 : Nat := 4983230072969 + 3 ^ 40 * 2361348 * 2
def baseEnd_2361348 : Nat := 1212506516533132448790365

theorem tailTrace_2361348 : CollatzResearch.WordTrace tailWord_2361348 prefixEnd_2361348 1212506516533132448790365 := by
  unfold tailWord_2361348
  simp only [CollatzResearch.WordTrace]
  refine ⟨43062718524623478488130349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57416958032831304650840465 43062718524623478488130349)
  ·
    refine ⟨16148519446733804433048881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43062718524623478488130349 16148519446733804433048881)
    ·
      refine ⟨12111389585050353324786661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16148519446733804433048881 12111389585050353324786661)
      ·
        refine ⟨2270885547196941248397499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12111389585050353324786661 2270885547196941248397499)
        ·
          refine ⟨3406328320795411872596249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2270885547196941248397499 3406328320795411872596249)
          ·
            refine ⟨2554746240596558904447187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3406328320795411872596249 2554746240596558904447187)
            ·
              refine ⟨3832119360894838356670781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554746240596558904447187 3832119360894838356670781)
              ·
                refine ⟨1437044760335564383751543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3832119360894838356670781 1437044760335564383751543)
                ·
                  refine ⟨2155567140503346575627315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437044760335564383751543 2155567140503346575627315)
                  ·
                    refine ⟨3233350710755019863440973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2155567140503346575627315 3233350710755019863440973)
                    ·
                      refine ⟨1212506516533132448790365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3233350710755019863440973 1212506516533132448790365)
                      ·
                        rfl

theorem cell23_2361348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2361348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361348 prefixEnd_2361348 := by exact prefixLift 2361348
  have htrace : WordTrace (prefixWord ++ tailWord_2361348) baseStart_2361348 baseEnd_2361348 := by
    simpa [prefixWord, tailWord_2361348, baseEnd_2361348] using wordTrace_append hprefix tailTrace_2361348
  have hstable : (prefixWord ++ tailWord_2361348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361348).length < 2 ^ (prefixWord ++ tailWord_2361348).sum := by decide
  have hdescent : baseEnd_2361348 < baseStart_2361348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361423 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 4]
def baseStart_2361423 : Nat := 118140960795 + 2361423 * 2 ^ 59
def prefixEnd_2361423 : Nat := 4983230072969 + 3 ^ 40 * 2361423 * 2
def baseEnd_2361423 : Nat := 1212545027582219655352519

theorem tailTrace_2361423 : CollatzResearch.WordTrace tailWord_2361423 prefixEnd_2361423 1212545027582219655352519 := by
  unfold tailWord_2361423
  simp only [CollatzResearch.WordTrace]
  refine ⟨86128172523975244785240923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57418781682650163190160615 86128172523975244785240923)
  ·
    refine ⟨129192258785962867177861385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86128172523975244785240923 129192258785962867177861385)
    ·
      refine ⟨96894194089472150383396039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129192258785962867177861385 96894194089472150383396039)
      ·
        refine ⟨145341291134208225575094059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96894194089472150383396039 145341291134208225575094059)
        ·
          refine ⟨218011936701312338362641089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145341291134208225575094059 218011936701312338362641089)
          ·
            refine ⟨163508952525984253771980817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218011936701312338362641089 163508952525984253771980817)
            ·
              refine ⟨122631714394488190328985613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163508952525984253771980817 122631714394488190328985613)
              ·
                refine ⟨45986892897933071373369605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122631714394488190328985613 45986892897933071373369605)
                ·
                  refine ⟨8622542418362450882506801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45986892897933071373369605 8622542418362450882506801)
                  ·
                    refine ⟨6466906813771838161880101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8622542418362450882506801 6466906813771838161880101)
                    ·
                      refine ⟨1212545027582219655352519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6466906813771838161880101 1212545027582219655352519)
                      ·
                        rfl

theorem cell23_2361423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_2361423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361423 prefixEnd_2361423 := by exact prefixLift 2361423
  have htrace : WordTrace (prefixWord ++ tailWord_2361423) baseStart_2361423 baseEnd_2361423 := by
    simpa [prefixWord, tailWord_2361423, baseEnd_2361423] using wordTrace_append hprefix tailTrace_2361423
  have hstable : (prefixWord ++ tailWord_2361423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361423).length < 2 ^ (prefixWord ++ tailWord_2361423).sum := by decide
  have hdescent : baseEnd_2361423 < baseStart_2361423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361433 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 7]
def baseStart_2361433 : Nat := 118140960795 + 2361433 * 2 ^ 59
def prefixEnd_2361433 : Nat := 4983230072969 + 3 ^ 40 * 2361433 * 2
def baseEnd_2361433 : Nat := 134727795820973846247497

theorem tailTrace_2361433 : CollatzResearch.WordTrace tailWord_2361433 prefixEnd_2361433 134727795820973846247497 := by
  unfold tailWord_2361433
  simp only [CollatzResearch.WordTrace]
  refine ⟨86128537253939016493104953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57419024835959344328736635 86128537253939016493104953)
  ·
    refine ⟨64596402940454262369828715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86128537253939016493104953 64596402940454262369828715)
    ·
      refine ⟨96894604410681393554743073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64596402940454262369828715 96894604410681393554743073)
      ·
        refine ⟨72670953308011045166057305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96894604410681393554743073 72670953308011045166057305)
        ·
          refine ⟨54503214981008283874542979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72670953308011045166057305 54503214981008283874542979)
          ·
            refine ⟨81754822471512425811814469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54503214981008283874542979 81754822471512425811814469)
            ·
              refine ⟨15329029213408579839715213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81754822471512425811814469 15329029213408579839715213)
              ·
                refine ⟨5748385955028217439893205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15329029213408579839715213 5748385955028217439893205)
                ·
                  refine ⟨134727795820973846247497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5748385955028217439893205 134727795820973846247497)
                  ·
                    rfl

theorem cell23_2361433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 7].length) (baseStart_2361433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361433 prefixEnd_2361433 := by exact prefixLift 2361433
  have htrace : WordTrace (prefixWord ++ tailWord_2361433) baseStart_2361433 baseEnd_2361433 := by
    simpa [prefixWord, tailWord_2361433, baseEnd_2361433] using wordTrace_append hprefix tailTrace_2361433
  have hstable : (prefixWord ++ tailWord_2361433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361433).length < 2 ^ (prefixWord ++ tailWord_2361433).sum := by decide
  have hdescent : baseEnd_2361433 < baseStart_2361433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361437 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 2, 6]
def baseStart_2361437 : Nat := 118140960795 + 2361437 * 2 ^ 59
def prefixEnd_2361437 : Nat := 4983230072969 + 3 ^ 40 * 2361437 * 2
def baseEnd_2361437 : Nat := 404184072103794200192485

theorem tailTrace_2361437 : CollatzResearch.WordTrace tailWord_2361437 prefixEnd_2361437 404184072103794200192485 := by
  unfold tailWord_2361437
  simp only [CollatzResearch.WordTrace]
  refine ⟨86128683145924525176250565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57419122097283016784167043 86128683145924525176250565)
  ·
    refine ⟨16149128089860848470546981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86128683145924525176250565 16149128089860848470546981)
    ·
      refine ⟨3027961516848909088227559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16149128089860848470546981 3027961516848909088227559)
      ·
        refine ⟨4541942275273363632341339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3027961516848909088227559 4541942275273363632341339)
        ·
          refine ⟨6812913412910045448512009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4541942275273363632341339 6812913412910045448512009)
          ·
            refine ⟨5109685059682534086384007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6812913412910045448512009 5109685059682534086384007)
            ·
              refine ⟨7664527589523801129576011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5109685059682534086384007 7664527589523801129576011)
              ·
                refine ⟨11496791384285701694364017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7664527589523801129576011 11496791384285701694364017)
                ·
                  refine ⟨8622593538214276270773013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11496791384285701694364017 8622593538214276270773013)
                  ·
                    refine ⟨404184072103794200192485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8622593538214276270773013 404184072103794200192485)
                    ·
                      rfl

theorem cell23_2361437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_2361437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361437 prefixEnd_2361437 := by exact prefixLift 2361437
  have htrace : WordTrace (prefixWord ++ tailWord_2361437) baseStart_2361437 baseEnd_2361437 := by
    simpa [prefixWord, tailWord_2361437, baseEnd_2361437] using wordTrace_append hprefix tailTrace_2361437
  have hstable : (prefixWord ++ tailWord_2361437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361437).length < 2 ^ (prefixWord ++ tailWord_2361437).sum := by decide
  have hdescent : baseEnd_2361437 < baseStart_2361437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361440 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 4]
def baseStart_2361440 : Nat := 118140960795 + 2361440 * 2 ^ 59
def prefixEnd_2361440 : Nat := 4983230072969 + 3 ^ 40 * 2361440 * 2
def baseEnd_2361440 : Nat := 1212553756753346088839941

theorem tailTrace_2361440 : CollatzResearch.WordTrace tailWord_2361440 prefixEnd_2361440 1212553756753346088839941 := by
  unfold tailWord_2361440
  simp only [CollatzResearch.WordTrace]
  refine ⟨43064396282456828344304887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57419195043275771125739849 43064396282456828344304887)
  ·
    refine ⟨64596594423685242516457331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43064396282456828344304887 64596594423685242516457331)
    ·
      refine ⟨96894891635527863774685997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64596594423685242516457331 96894891635527863774685997)
      ·
        refine ⟨36335584363322948915507249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96894891635527863774685997 36335584363322948915507249)
        ·
          refine ⟨27251688272492211686630437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36335584363322948915507249 27251688272492211686630437)
          ·
            refine ⟨5109691551092289691243207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27251688272492211686630437 5109691551092289691243207)
            ·
              refine ⟨7664537326638434536864811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5109691551092289691243207 7664537326638434536864811)
              ·
                refine ⟨11496805989957651805297217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7664537326638434536864811 11496805989957651805297217)
                ·
                  refine ⟨8622604492468238853972913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11496805989957651805297217 8622604492468238853972913)
                  ·
                    refine ⟨6466953369351179140479685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8622604492468238853972913 6466953369351179140479685)
                    ·
                      refine ⟨1212553756753346088839941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6466953369351179140479685 1212553756753346088839941)
                      ·
                        rfl

theorem cell23_2361440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_2361440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361440 prefixEnd_2361440 := by exact prefixLift 2361440
  have htrace : WordTrace (prefixWord ++ tailWord_2361440) baseStart_2361440 baseEnd_2361440 := by
    simpa [prefixWord, tailWord_2361440, baseEnd_2361440] using wordTrace_append hprefix tailTrace_2361440
  have hstable : (prefixWord ++ tailWord_2361440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361440).length < 2 ^ (prefixWord ++ tailWord_2361440).sum := by decide
  have hdescent : baseEnd_2361440 < baseStart_2361440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361444 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 2, 2, 2]
def baseStart_2361444 : Nat := 118140960795 + 2361444 * 2 ^ 59
def prefixEnd_2361444 : Nat := 4983230072969 + 3 ^ 40 * 2361444 * 2
def baseEnd_2361444 : Nat := 1212555810675964073189923

theorem tailTrace_2361444 : CollatzResearch.WordTrace tailWord_2361444 prefixEnd_2361444 1212555810675964073189923 := by
  unfold tailWord_2361444
  simp only [CollatzResearch.WordTrace]
  refine ⟨43064469228449582685877693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57419292304599443581170257 43064469228449582685877693)
  ·
    refine ⟨16149175960668593507204135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43064469228449582685877693 16149175960668593507204135)
    ·
      refine ⟨24223763941002890260806203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16149175960668593507204135 24223763941002890260806203)
      ·
        refine ⟨36335645911504335391209305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24223763941002890260806203 36335645911504335391209305)
        ·
          refine ⟨27251734433628251543406979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36335645911504335391209305 27251734433628251543406979)
          ·
            refine ⟨40877601650442377315110469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27251734433628251543406979 40877601650442377315110469)
            ·
              refine ⟨7664550309457945746583213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40877601650442377315110469 7664550309457945746583213)
              ·
                refine ⟨2874206366046729654968705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7664550309457945746583213 2874206366046729654968705)
                ·
                  refine ⟨2155654774535047241226529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2874206366046729654968705 2155654774535047241226529)
                  ·
                    refine ⟨1616741080901285430919897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2155654774535047241226529 1616741080901285430919897)
                    ·
                      refine ⟨1212555810675964073189923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616741080901285430919897 1212555810675964073189923)
                      ·
                        rfl

theorem cell23_2361444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_2361444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361444 prefixEnd_2361444 := by exact prefixLift 2361444
  have htrace : WordTrace (prefixWord ++ tailWord_2361444) baseStart_2361444 baseEnd_2361444 := by
    simpa [prefixWord, tailWord_2361444, baseEnd_2361444] using wordTrace_append hprefix tailTrace_2361444
  have hstable : (prefixWord ++ tailWord_2361444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361444).length < 2 ^ (prefixWord ++ tailWord_2361444).sum := by decide
  have hdescent : baseEnd_2361444 < baseStart_2361444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361490 : List Nat := [3, 2, 3, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_2361490 : Nat := 118140960795 + 2361490 * 2 ^ 59
def prefixEnd_2361490 : Nat := 4983230072969 + 3 ^ 40 * 2361490 * 2
def baseEnd_2361490 : Nat := 1212579430786070893214711

theorem tailTrace_2361490 : CollatzResearch.WordTrace tailWord_2361490 prefixEnd_2361490 1212579430786070893214711 := by
  unfold tailWord_2361490
  simp only [CollatzResearch.WordTrace]
  refine ⟨21532654053683128806982481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57420410809821676818619949 21532654053683128806982481)
  ·
    refine ⟨16149490540262346605236861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21532654053683128806982481 16149490540262346605236861)
    ·
      refine ⟨6056058952598379976963823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16149490540262346605236861 6056058952598379976963823)
      ·
        refine ⟨9084088428897569965445735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6056058952598379976963823 9084088428897569965445735)
        ·
          refine ⟨13626132643346354948168603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9084088428897569965445735 13626132643346354948168603)
          ·
            refine ⟨20439198965019532422252905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13626132643346354948168603 20439198965019532422252905)
            ·
              refine ⟨15329399223764649316689679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20439198965019532422252905 15329399223764649316689679)
              ·
                refine ⟨22994098835646973975034519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15329399223764649316689679 22994098835646973975034519)
                ·
                  refine ⟨34491148253470460962551779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22994098835646973975034519 34491148253470460962551779)
                  ·
                    refine ⟨51736722380205691443827669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34491148253470460962551779 51736722380205691443827669)
                    ·
                      refine ⟨1212579430786070893214711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51736722380205691443827669 1212579430786070893214711)
                      ·
                        rfl

theorem cell23_2361490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_2361490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361490 prefixEnd_2361490 := by exact prefixLift 2361490
  have htrace : WordTrace (prefixWord ++ tailWord_2361490) baseStart_2361490 baseEnd_2361490 := by
    simpa [prefixWord, tailWord_2361490, baseEnd_2361490] using wordTrace_append hprefix tailTrace_2361490
  have hstable : (prefixWord ++ tailWord_2361490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361490).length < 2 ^ (prefixWord ++ tailWord_2361490).sum := by decide
  have hdescent : baseEnd_2361490 < baseStart_2361490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361500 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2361500 : Nat := 118140960795 + 2361500 * 2 ^ 59
def prefixEnd_2361500 : Nat := 4983230072969 + 3 ^ 40 * 2361500 * 2
def baseEnd_2361500 : Nat := 1212584565592615854089665

theorem tailTrace_2361500 : CollatzResearch.WordTrace tailWord_2361500 prefixEnd_2361500 1212584565592615854089665 := by
  unfold tailWord_2361500
  simp only [CollatzResearch.WordTrace]
  refine ⟨43065490472348143467896977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57420653963130857957195969 43065490472348143467896977)
  ·
    refine ⟨32299117854261107600922733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43065490472348143467896977 32299117854261107600922733)
    ·
      refine ⟨12112169195347915350346025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32299117854261107600922733 12112169195347915350346025)
      ·
        refine ⟨9084126896510936512759519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12112169195347915350346025 9084126896510936512759519)
        ·
          refine ⟨13626190344766404769139279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9084126896510936512759519 13626190344766404769139279)
          ·
            refine ⟨20439285517149607153708919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13626190344766404769139279 20439285517149607153708919)
            ·
              refine ⟨30658928275724410730563379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20439285517149607153708919 30658928275724410730563379)
              ·
                refine ⟨45988392413586616095845069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30658928275724410730563379 45988392413586616095845069)
                ·
                  refine ⟨17245647155094981035941901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45988392413586616095845069 17245647155094981035941901)
                  ·
                    refine ⟨6467117683160617888478213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17245647155094981035941901 6467117683160617888478213)
                    ·
                      refine ⟨1212584565592615854089665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6467117683160617888478213 1212584565592615854089665)
                      ·
                        rfl

theorem cell23_2361500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2361500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361500 prefixEnd_2361500 := by exact prefixLift 2361500
  have htrace : WordTrace (prefixWord ++ tailWord_2361500) baseStart_2361500 baseEnd_2361500 := by
    simpa [prefixWord, tailWord_2361500, baseEnd_2361500] using wordTrace_append hprefix tailTrace_2361500
  have hstable : (prefixWord ++ tailWord_2361500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361500).length < 2 ^ (prefixWord ++ tailWord_2361500).sum := by decide
  have hdescent : baseEnd_2361500 < baseStart_2361500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361517 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_2361517 : Nat := 118140960795 + 2361517 * 2 ^ 59
def prefixEnd_2361517 : Nat := 4983230072969 + 3 ^ 40 * 2361517 * 2
def baseEnd_2361517 : Nat := 1212593294763742287577087

theorem tailTrace_2361517 : CollatzResearch.WordTrace tailWord_2361517 prefixEnd_2361517 1212593294763742287577087 := by
  unfold tailWord_2361517
  simp only [CollatzResearch.WordTrace]
  refine ⟨86131600985634698839162805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57421067323756465892775203 86131600985634698839162805)
  ·
    refine ⟨8074837592403253016171513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86131600985634698839162805 8074837592403253016171513)
    ·
      refine ⟨6056128194302439762128635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8074837592403253016171513 6056128194302439762128635)
      ·
        refine ⟨9084192291453659643192953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6056128194302439762128635 9084192291453659643192953)
        ·
          refine ⟨6813144218590244732394715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9084192291453659643192953 6813144218590244732394715)
          ·
            refine ⟨10219716327885367098592073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6813144218590244732394715 10219716327885367098592073)
            ·
              refine ⟨7664787245914025323944055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10219716327885367098592073 7664787245914025323944055)
              ·
                refine ⟨11497180868871037985916083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7664787245914025323944055 11497180868871037985916083)
                ·
                  refine ⟨17245771303306556978874125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11497180868871037985916083 17245771303306556978874125)
                  ·
                    refine ⟨6467164238739958867077797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17245771303306556978874125 6467164238739958867077797)
                    ·
                      refine ⟨1212593294763742287577087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6467164238739958867077797 1212593294763742287577087)
                      ·
                        rfl

theorem cell23_2361517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_2361517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361517 prefixEnd_2361517 := by exact prefixLift 2361517
  have htrace : WordTrace (prefixWord ++ tailWord_2361517) baseStart_2361517 baseEnd_2361517 := by
    simpa [prefixWord, tailWord_2361517, baseEnd_2361517] using wordTrace_append hprefix tailTrace_2361517
  have hstable : (prefixWord ++ tailWord_2361517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361517).length < 2 ^ (prefixWord ++ tailWord_2361517).sum := by decide
  have hdescent : baseEnd_2361517 < baseStart_2361517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361518 : List Nat := [4, 1, 4, 2, 1, 2, 1, 3, 5]
def baseStart_2361518 : Nat := 118140960795 + 2361518 * 2 ^ 59
def prefixEnd_2361518 : Nat := 4983230072969 + 3 ^ 40 * 2361518 * 2
def baseEnd_2361518 : Nat := 134732645360488531518287

theorem tailTrace_2361518 : CollatzResearch.WordTrace tailWord_2361518 prefixEnd_2361518 134732645360488531518287 := by
  unfold tailWord_2361518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10766454682328884501243651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57421091639087384006632805 10766454682328884501243651)
  ·
    refine ⟨16149682023493326751865477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10766454682328884501243651 16149682023493326751865477)
    ·
      refine ⟨3028065379404998765974777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16149682023493326751865477 3028065379404998765974777)
      ·
        refine ⟨2271049034553749074481083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3028065379404998765974777 2271049034553749074481083)
        ·
          refine ⟨3406573551830623611721625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271049034553749074481083 3406573551830623611721625)
          ·
            refine ⟨2554930163872967708791219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3406573551830623611721625 2554930163872967708791219)
            ·
              refine ⟨3832395245809451563186829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554930163872967708791219 3832395245809451563186829)
              ·
                refine ⟨1437148217178544336195061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3832395245809451563186829 1437148217178544336195061)
                ·
                  refine ⟨134732645360488531518287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1437148217178544336195061 134732645360488531518287)
                  ·
                    rfl

theorem cell23_2361518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_2361518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361518 prefixEnd_2361518 := by exact prefixLift 2361518
  have htrace : WordTrace (prefixWord ++ tailWord_2361518) baseStart_2361518 baseEnd_2361518 := by
    simpa [prefixWord, tailWord_2361518, baseEnd_2361518] using wordTrace_append hprefix tailTrace_2361518
  have hstable : (prefixWord ++ tailWord_2361518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361518).length < 2 ^ (prefixWord ++ tailWord_2361518).sum := by decide
  have hdescent : baseEnd_2361518 < baseStart_2361518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361534 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_2361534 : Nat := 118140960795 + 2361534 * 2 ^ 59
def prefixEnd_2361534 : Nat := 4983230072969 + 3 ^ 40 * 2361534 * 2
def baseEnd_2361534 : Nat := 1212602023934868721064509

theorem tailTrace_2361534 : CollatzResearch.WordTrace tailWord_2361534 prefixEnd_2361534 1212602023934868721064509 := by
  unfold tailWord_2361534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10766527628321638842816457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57421480684382073828354437 10766527628321638842816457)
  ·
    refine ⟨8074895721241229132112343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10766527628321638842816457 8074895721241229132112343)
    ·
      refine ⟨12112343581861843698168515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8074895721241229132112343 12112343581861843698168515)
      ·
        refine ⟨18168515372792765547252773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12112343581861843698168515 18168515372792765547252773)
        ·
          refine ⟨3406596632398643540109895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18168515372792765547252773 3406596632398643540109895)
          ·
            refine ⟨5109894948597965310164843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406596632398643540109895 5109894948597965310164843)
            ·
              refine ⟨7664842422896947965247265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5109894948597965310164843 7664842422896947965247265)
              ·
                refine ⟨5748631817172710973935449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7664842422896947965247265 5748631817172710973935449)
                ·
                  refine ⟨4311473862879533230451587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5748631817172710973935449 4311473862879533230451587)
                  ·
                    refine ⟨6467210794319299845677381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4311473862879533230451587 6467210794319299845677381)
                    ·
                      refine ⟨1212602023934868721064509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6467210794319299845677381 1212602023934868721064509)
                      ·
                        rfl

theorem cell23_2361534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_2361534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361534 prefixEnd_2361534 := by exact prefixLift 2361534
  have htrace : WordTrace (prefixWord ++ tailWord_2361534) baseStart_2361534 baseEnd_2361534 := by
    simpa [prefixWord, tailWord_2361534, baseEnd_2361534] using wordTrace_append hprefix tailTrace_2361534
  have hstable : (prefixWord ++ tailWord_2361534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361534).length < 2 ^ (prefixWord ++ tailWord_2361534).sum := by decide
  have hdescent : baseEnd_2361534 < baseStart_2361534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361567 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 5, 1, 3]
def baseStart_2361567 : Nat := 118140960795 + 2361567 * 2 ^ 59
def prefixEnd_2361567 : Nat := 4983230072969 + 3 ^ 40 * 2361567 * 2
def baseEnd_2361567 : Nat := 1212618968796467091951857

theorem tailTrace_2361567 : CollatzResearch.WordTrace tailWord_2361567 prefixEnd_2361567 1212618968796467091951857 := by
  unfold tailWord_2361567
  simp only [CollatzResearch.WordTrace]
  refine ⟨86133424635453557378482955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57422283090302371585655303 86133424635453557378482955)
  ·
    refine ⟨129200136953180336067724433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86133424635453557378482955 129200136953180336067724433)
    ·
      refine ⟨96900102714885252050793325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129200136953180336067724433 96900102714885252050793325)
      ·
        refine ⟨36337538518081969519047497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96900102714885252050793325 36337538518081969519047497)
        ·
          refine ⟨27253153888561477139285623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36337538518081969519047497 27253153888561477139285623)
          ·
            refine ⟨40879730832842215708928435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27253153888561477139285623 40879730832842215708928435)
            ·
              refine ⟨61319596249263323563392653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40879730832842215708928435 61319596249263323563392653)
              ·
                refine ⟨22994848593473746336272245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61319596249263323563392653 22994848593473746336272245)
                ·
                  refine ⟨2155767055638163719025523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22994848593473746336272245 2155767055638163719025523)
                  ·
                    refine ⟨3233650583457245578538285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2155767055638163719025523 3233650583457245578538285)
                    ·
                      refine ⟨1212618968796467091951857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3233650583457245578538285 1212618968796467091951857)
                      ·
                        rfl

theorem cell23_2361567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_2361567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361567 prefixEnd_2361567 := by exact prefixLift 2361567
  have htrace : WordTrace (prefixWord ++ tailWord_2361567) baseStart_2361567 baseEnd_2361567 := by
    simpa [prefixWord, tailWord_2361567, baseEnd_2361567] using wordTrace_append hprefix tailTrace_2361567
  have hstable : (prefixWord ++ tailWord_2361567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361567).length < 2 ^ (prefixWord ++ tailWord_2361567).sum := by decide
  have hdescent : baseEnd_2361567 < baseStart_2361567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361571 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2361571 : Nat := 118140960795 + 2361571 * 2 ^ 59
def prefixEnd_2361571 : Nat := 4983230072969 + 3 ^ 40 * 2361571 * 2
def baseEnd_2361571 : Nat := 1212621022719085076301839

theorem tailTrace_2361571 : CollatzResearch.WordTrace tailWord_2361571 prefixEnd_2361571 1212621022719085076301839 := by
  unfold tailWord_2361571
  simp only [CollatzResearch.WordTrace]
  refine ⟨86133570527439066061628567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57422380351626044041085711 86133570527439066061628567)
  ·
    refine ⟨129200355791158599092442851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86133570527439066061628567 129200355791158599092442851)
    ·
      refine ⟨193800533686737898638664277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129200355791158599092442851 193800533686737898638664277)
      ·
        refine ⟨2271100004141459749671847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 193800533686737898638664277 2271100004141459749671847)
        ·
          refine ⟨3406650006212189624507771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271100004141459749671847 3406650006212189624507771)
          ·
            refine ⟨5109975009318284436761657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406650006212189624507771 5109975009318284436761657)
            ·
              refine ⟨3832481256988713327571243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5109975009318284436761657 3832481256988713327571243)
              ·
                refine ⟨5748721885483069991356865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832481256988713327571243 5748721885483069991356865)
                ·
                  refine ⟨4311541414112302493517649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5748721885483069991356865 4311541414112302493517649)
                  ·
                    refine ⟨3233656060584226870138237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4311541414112302493517649 3233656060584226870138237)
                    ·
                      refine ⟨1212621022719085076301839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3233656060584226870138237 1212621022719085076301839)
                      ·
                        rfl

theorem cell23_2361571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2361571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361571 prefixEnd_2361571 := by exact prefixLift 2361571
  have htrace : WordTrace (prefixWord ++ tailWord_2361571) baseStart_2361571 baseEnd_2361571 := by
    simpa [prefixWord, tailWord_2361571, baseEnd_2361571] using wordTrace_append hprefix tailTrace_2361571
  have hstable : (prefixWord ++ tailWord_2361571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361571).length < 2 ^ (prefixWord ++ tailWord_2361571).sum := by decide
  have hdescent : baseEnd_2361571 < baseStart_2361571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361577 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 6, 3, 2]
def baseStart_2361577 : Nat := 118140960795 + 2361577 * 2 ^ 59
def prefixEnd_2361577 : Nat := 4983230072969 + 3 ^ 40 * 2361577 * 2
def baseEnd_2361577 : Nat := 1212624103603012052826811

theorem tailTrace_2361577 : CollatzResearch.WordTrace tailWord_2361577 prefixEnd_2361577 1212624103603012052826811 := by
  unfold tailWord_2361577
  simp only [CollatzResearch.WordTrace]
  refine ⟨86133789365417329086346985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57422526243611552724231323 86133789365417329086346985)
  ·
    refine ⟨64600342024062996814760239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86133789365417329086346985 64600342024062996814760239)
    ·
      refine ⟨96900513036094495222140359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64600342024062996814760239 96900513036094495222140359)
      ·
        refine ⟨145350769554141742833210539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96900513036094495222140359 145350769554141742833210539)
        ·
          refine ⟨218026154331212614249815809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145350769554141742833210539 218026154331212614249815809)
          ·
            refine ⟨163519615748409460687361857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218026154331212614249815809 163519615748409460687361857)
            ·
              refine ⟨122639711811307095515521393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163519615748409460687361857 122639711811307095515521393)
              ·
                refine ⟨91979783858480321636641045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 122639711811307095515521393 91979783858480321636641045)
                ·
                  refine ⟨4311552368366265076717549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 91979783858480321636641045 4311552368366265076717549)
                  ·
                    refine ⟨1616832138137349403769081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4311552368366265076717549 1616832138137349403769081)
                    ·
                      refine ⟨1212624103603012052826811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616832138137349403769081 1212624103603012052826811)
                      ·
                        rfl

theorem cell23_2361577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 3, 2].length) (baseStart_2361577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361577 prefixEnd_2361577 := by exact prefixLift 2361577
  have htrace : WordTrace (prefixWord ++ tailWord_2361577) baseStart_2361577 baseEnd_2361577 := by
    simpa [prefixWord, tailWord_2361577, baseEnd_2361577] using wordTrace_append hprefix tailTrace_2361577
  have hstable : (prefixWord ++ tailWord_2361577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361577).length < 2 ^ (prefixWord ++ tailWord_2361577).sum := by decide
  have hdescent : baseEnd_2361577 < baseStart_2361577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361594 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2]
def baseStart_2361594 : Nat := 118140960795 + 2361594 * 2 ^ 59
def prefixEnd_2361594 : Nat := 4983230072969 + 3 ^ 40 * 2361594 * 2
def baseEnd_2361594 : Nat := 1212632832774138486314233

theorem tailTrace_2361594 : CollatzResearch.WordTrace tailWord_2361594 prefixEnd_2361594 1212632832774138486314233 := by
  unfold tailWord_2361594
  simp only [CollatzResearch.WordTrace]
  refine ⟨21533602351588935247428959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57422939604237160659810557 21533602351588935247428959)
  ·
    refine ⟨32300403527383402871143439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21533602351588935247428959 32300403527383402871143439)
    ·
      refine ⟨48450605291075104306715159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32300403527383402871143439 48450605291075104306715159)
      ·
        refine ⟨72675907936612656460072739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48450605291075104306715159 72675907936612656460072739)
        ·
          refine ⟨109013861904918984690109109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72675907936612656460072739 109013861904918984690109109)
          ·
            refine ⟨10220049553586154814697729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 109013861904918984690109109 10220049553586154814697729)
            ·
              refine ⟨7665037165189616111023297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10220049553586154814697729 7665037165189616111023297)
              ·
                refine ⟨5748777873892212083267473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7665037165189616111023297 5748777873892212083267473)
                ·
                  refine ⟨4311583405419159062450605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5748777873892212083267473 4311583405419159062450605)
                  ·
                    refine ⟨1616843777032184648418977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4311583405419159062450605 1616843777032184648418977)
                    ·
                      refine ⟨1212632832774138486314233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616843777032184648418977 1212632832774138486314233)
                      ·
                        rfl

theorem cell23_2361594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2].length) (baseStart_2361594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361594 prefixEnd_2361594 := by exact prefixLift 2361594
  have htrace : WordTrace (prefixWord ++ tailWord_2361594) baseStart_2361594 baseEnd_2361594 := by
    simpa [prefixWord, tailWord_2361594, baseEnd_2361594] using wordTrace_append hprefix tailTrace_2361594
  have hstable : (prefixWord ++ tailWord_2361594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361594).length < 2 ^ (prefixWord ++ tailWord_2361594).sum := by decide
  have hdescent : baseEnd_2361594 < baseStart_2361594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361601 : List Nat := [1, 2, 4, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_2361601 : Nat := 118140960795 + 2361601 * 2 ^ 59
def prefixEnd_2361601 : Nat := 4983230072969 + 3 ^ 40 * 2361601 * 2
def baseEnd_2361601 : Nat := 1212636427138719958926701

theorem tailTrace_2361601 : CollatzResearch.WordTrace tailWord_2361601 prefixEnd_2361601 1212636427138719958926701 := by
  unfold tailWord_2361601
  simp only [CollatzResearch.WordTrace]
  refine ⟨86134664717330381185220657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57423109811553587456813771 86134664717330381185220657)
  ·
    refine ⟨64600998537997785888915493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86134664717330381185220657 64600998537997785888915493)
    ·
      refine ⟨12112687225874584854171655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64600998537997785888915493 12112687225874584854171655)
      ·
        refine ⟨18169030838811877281257483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12112687225874584854171655 18169030838811877281257483)
        ·
          refine ⟨27253546258217815921886225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18169030838811877281257483 27253546258217815921886225)
          ·
            refine ⟨20440159693663361941414669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27253546258217815921886225 20440159693663361941414669)
            ·
              refine ⟨7665059885123760728030501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20440159693663361941414669 7665059885123760728030501)
              ·
                refine ⟨1437198728460705136505719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7665059885123760728030501 1437198728460705136505719)
                ·
                  refine ⟨2155798092691057704758579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437198728460705136505719 2155798092691057704758579)
                  ·
                    refine ⟨3233697139036586557137869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2155798092691057704758579 3233697139036586557137869)
                    ·
                      refine ⟨1212636427138719958926701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3233697139036586557137869 1212636427138719958926701)
                      ·
                        rfl

theorem cell23_2361601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_2361601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361601 prefixEnd_2361601 := by exact prefixLift 2361601
  have htrace : WordTrace (prefixWord ++ tailWord_2361601) baseStart_2361601 baseEnd_2361601 := by
    simpa [prefixWord, tailWord_2361601, baseEnd_2361601] using wordTrace_append hprefix tailTrace_2361601
  have hstable : (prefixWord ++ tailWord_2361601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361601).length < 2 ^ (prefixWord ++ tailWord_2361601).sum := by decide
  have hdescent : baseEnd_2361601 < baseStart_2361601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361617 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 1, 6]
def baseStart_2361617 : Nat := 118140960795 + 2361617 * 2 ^ 59
def prefixEnd_2361617 : Nat := 4983230072969 + 3 ^ 40 * 2361617 * 2
def baseEnd_2361617 : Nat := 404214880943063965442209

theorem tailTrace_2361617 : CollatzResearch.WordTrace tailWord_2361617 prefixEnd_2361617 404214880943063965442209 := by
  unfold tailWord_2361617
  simp only [CollatzResearch.WordTrace]
  refine ⟨86135248285272415917803105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57423498856848277278535403 86135248285272415917803105)
  ·
    refine ⟨64601436213954311938352329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86135248285272415917803105 64601436213954311938352329)
    ·
      refine ⟨48451077160465733953764247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64601436213954311938352329 48451077160465733953764247)
      ·
        refine ⟨72676615740698600930646371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48451077160465733953764247 72676615740698600930646371)
        ·
          refine ⟨109014923611047901395969557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72676615740698600930646371 109014923611047901395969557)
          ·
            refine ⟨5110074544267870377936073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 109014923611047901395969557 5110074544267870377936073)
            ·
              refine ⟨3832555908200902783452055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5110074544267870377936073 3832555908200902783452055)
              ·
                refine ⟨5748833862301354175178083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832555908200902783452055 5748833862301354175178083)
                ·
                  refine ⟨8623250793452031262767125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5748833862301354175178083 8623250793452031262767125)
                  ·
                    refine ⟨404214880943063965442209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8623250793452031262767125 404214880943063965442209)
                    ·
                      rfl

theorem cell23_2361617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 6].length) (baseStart_2361617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361617 prefixEnd_2361617 := by exact prefixLift 2361617
  have htrace : WordTrace (prefixWord ++ tailWord_2361617) baseStart_2361617 baseEnd_2361617 := by
    simpa [prefixWord, tailWord_2361617, baseEnd_2361617] using wordTrace_append hprefix tailTrace_2361617
  have hstable : (prefixWord ++ tailWord_2361617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361617).length < 2 ^ (prefixWord ++ tailWord_2361617).sum := by decide
  have hdescent : baseEnd_2361617 < baseStart_2361617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361627 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 3]
def baseStart_2361627 : Nat := 118140960795 + 2361627 * 2 ^ 59
def prefixEnd_2361627 : Nat := 4983230072969 + 3 ^ 40 * 2361627 * 2
def baseEnd_2361627 : Nat := 1212649777635736857201581

theorem tailTrace_2361627 : CollatzResearch.WordTrace tailWord_2361627 prefixEnd_2361627 1212649777635736857201581 := by
  unfold tailWord_2361627
  simp only [CollatzResearch.WordTrace]
  refine ⟨86135613015236187625667135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57423742010157458417111423 86135613015236187625667135)
  ·
    refine ⟨129203419522854281438500703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86135613015236187625667135 129203419522854281438500703)
    ·
      refine ⟨193805129284281422157751055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129203419522854281438500703 193805129284281422157751055)
      ·
        refine ⟨290707693926422133236626583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193805129284281422157751055 290707693926422133236626583)
        ·
          refine ⟨436061540889633199854939875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290707693926422133236626583 436061540889633199854939875)
          ·
            refine ⟨654092311334449799782409813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436061540889633199854939875 654092311334449799782409813)
            ·
              refine ⟨7665144273450583591200115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 654092311334449799782409813 7665144273450583591200115)
              ·
                refine ⟨11497716410175875386800173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7665144273450583591200115 11497716410175875386800173)
                ·
                  refine ⟨4311643653815953270050065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11497716410175875386800173 4311643653815953270050065)
                  ·
                    refine ⟨3233732740361964952537549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4311643653815953270050065 3233732740361964952537549)
                    ·
                      refine ⟨1212649777635736857201581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3233732740361964952537549 1212649777635736857201581)
                      ·
                        rfl

theorem cell23_2361627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 2, 3].length) (baseStart_2361627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361627 prefixEnd_2361627 := by exact prefixLift 2361627
  have htrace : WordTrace (prefixWord ++ tailWord_2361627) baseStart_2361627 baseEnd_2361627 := by
    simpa [prefixWord, tailWord_2361627, baseEnd_2361627] using wordTrace_append hprefix tailTrace_2361627
  have hstable : (prefixWord ++ tailWord_2361627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361627).length < 2 ^ (prefixWord ++ tailWord_2361627).sum := by decide
  have hdescent : baseEnd_2361627 < baseStart_2361627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361658 : List Nat := [3, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2]
def baseStart_2361658 : Nat := 118140960795 + 2361658 * 2 ^ 59
def prefixEnd_2361658 : Nat := 4983230072969 + 3 ^ 40 * 2361658 * 2
def baseEnd_2361658 : Nat := 1212665695536026235913939

theorem tailTrace_2361658 : CollatzResearch.WordTrace tailWord_2361658 prefixEnd_2361658 1212665695536026235913939 := by
  unfold tailWord_2361658
  simp only [CollatzResearch.WordTrace]
  refine ⟨21534185919530969980011407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57424495785415919946697085 21534185919530969980011407)
  ·
    refine ⟨32301278879296454970017111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21534185919530969980011407 32301278879296454970017111)
    ·
      refine ⟨48451918318944682455025667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32301278879296454970017111 48451918318944682455025667)
      ·
        refine ⟨72677877478417023682538501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48451918318944682455025667 72677877478417023682538501)
        ·
          refine ⟨13627102027203191940475969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72677877478417023682538501 13627102027203191940475969)
          ·
            refine ⟨10220326520402393955356977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13627102027203191940475969 10220326520402393955356977)
            ·
              refine ⟨7665244890301795466517733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10220326520402393955356977 7665244890301795466517733)
              ·
                refine ⟨1437233416931586649972075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7665244890301795466517733 1437233416931586649972075)
                ·
                  refine ⟨2155850125397379974958113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437233416931586649972075 2155850125397379974958113)
                  ·
                    refine ⟨1616887594048034981218585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2155850125397379974958113 1616887594048034981218585)
                    ·
                      refine ⟨1212665695536026235913939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616887594048034981218585 1212665695536026235913939)
                      ·
                        rfl

theorem cell23_2361658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2].length) (baseStart_2361658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361658 prefixEnd_2361658 := by exact prefixLift 2361658
  have htrace : WordTrace (prefixWord ++ tailWord_2361658) baseStart_2361658 baseEnd_2361658 := by
    simpa [prefixWord, tailWord_2361658, baseEnd_2361658] using wordTrace_append hprefix tailTrace_2361658
  have hstable : (prefixWord ++ tailWord_2361658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361658).length < 2 ^ (prefixWord ++ tailWord_2361658).sum := by decide
  have hdescent : baseEnd_2361658 < baseStart_2361658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361668 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_2361668 : Nat := 118140960795 + 2361668 * 2 ^ 59
def prefixEnd_2361668 : Nat := 4983230072969 + 3 ^ 40 * 2361668 * 2
def baseEnd_2361668 : Nat := 404223610114190398929631

theorem tailTrace_2361668 : CollatzResearch.WordTrace tailWord_2361668 prefixEnd_2361668 404223610114190398929631 := by
  unfold tailWord_2361668
  simp only [CollatzResearch.WordTrace]
  refine ⟨43068554204043825813954829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57424738938725101085273105 43068554204043825813954829)
  ·
    refine ⟨16150707826516434680233061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43068554204043825813954829 16150707826516434680233061)
    ·
      refine ⟨3028257717471831502543699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16150707826516434680233061 3028257717471831502543699)
      ·
        refine ⟨4542386576207747253815549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3028257717471831502543699 4542386576207747253815549)
        ·
          refine ⟨1703394966077905220180831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4542386576207747253815549 1703394966077905220180831)
          ·
            refine ⟨2555092449116857830271247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703394966077905220180831 2555092449116857830271247)
            ·
              refine ⟨3832638673675286745406871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555092449116857830271247 3832638673675286745406871)
              ·
                refine ⟨5748958010512930118110307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832638673675286745406871 5748958010512930118110307)
                ·
                  refine ⟨8623437015769395177165461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5748958010512930118110307 8623437015769395177165461)
                  ·
                    refine ⟨404223610114190398929631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8623437015769395177165461 404223610114190398929631)
                    ·
                      rfl

theorem cell23_2361668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_2361668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361668 prefixEnd_2361668 := by exact prefixLift 2361668
  have htrace : WordTrace (prefixWord ++ tailWord_2361668) baseStart_2361668 baseEnd_2361668 := by
    simpa [prefixWord, tailWord_2361668, baseEnd_2361668] using wordTrace_append hprefix tailTrace_2361668
  have hstable : (prefixWord ++ tailWord_2361668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361668).length < 2 ^ (prefixWord ++ tailWord_2361668).sum := by decide
  have hdescent : baseEnd_2361668 < baseStart_2361668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361701 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 1, 3, 2]
def baseStart_2361701 : Nat := 118140960795 + 2361701 * 2 ^ 59
def prefixEnd_2361701 : Nat := 4983230072969 + 3 ^ 40 * 2361701 * 2
def baseEnd_2361701 : Nat := 1212687775204169567676241

theorem tailTrace_2361701 : CollatzResearch.WordTrace tailWord_2361701 prefixEnd_2361701 1212687775204169567676241 := by
  unfold tailWord_2361701
  simp only [CollatzResearch.WordTrace]
  refine ⟨86138312016968098263860957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57425541344645398842573971 86138312016968098263860957)
  ·
    refine ⟨32301867006363036848947859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86138312016968098263860957 32301867006363036848947859)
    ·
      refine ⟨48452800509544555273421789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32301867006363036848947859 48452800509544555273421789)
      ·
        refine ⟨18169800191079208227533171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48452800509544555273421789 18169800191079208227533171)
        ·
          refine ⟨27254700286618812341299757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18169800191079208227533171 27254700286618812341299757)
          ·
            refine ⟨10220512607482054627987409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27254700286618812341299757 10220512607482054627987409)
            ·
              refine ⟨7665384455611540970990557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10220512607482054627987409 7665384455611540970990557)
              ·
                refine ⟨2874519170854327864121459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7665384455611540970990557 2874519170854327864121459)
                ·
                  refine ⟨4311778756281491796182189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874519170854327864121459 4311778756281491796182189)
                  ·
                    refine ⟨1616917033605559423568321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4311778756281491796182189 1616917033605559423568321)
                    ·
                      refine ⟨1212687775204169567676241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616917033605559423568321 1212687775204169567676241)
                      ·
                        rfl

theorem cell23_2361701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_2361701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361701 prefixEnd_2361701 := by exact prefixLift 2361701
  have htrace : WordTrace (prefixWord ++ tailWord_2361701) baseStart_2361701 baseEnd_2361701 := by
    simpa [prefixWord, tailWord_2361701, baseEnd_2361701] using wordTrace_append hprefix tailTrace_2361701
  have hstable : (prefixWord ++ tailWord_2361701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361701).length < 2 ^ (prefixWord ++ tailWord_2361701).sum := by decide
  have hdescent : baseEnd_2361701 < baseStart_2361701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361748 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_2361748 : Nat := 118140960795 + 2361748 * 2 ^ 59
def prefixEnd_2361748 : Nat := 4983230072969 + 3 ^ 40 * 2361748 * 2
def baseEnd_2361748 : Nat := 1212711908794930883788525

theorem tailTrace_2361748 : CollatzResearch.WordTrace tailWord_2361748 prefixEnd_2361748 1212711908794930883788525 := by
  unfold tailWord_2361748
  simp only [CollatzResearch.WordTrace]
  refine ⟨43070013123898912645410949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57426684165198550193881265 43070013123898912645410949)
  ·
    refine ⟨8075627460731046121014553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43070013123898912645410949 8075627460731046121014553)
    ·
      refine ⟨6056720595548284590760915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8075627460731046121014553 6056720595548284590760915)
      ·
        refine ⟨9085080893322426886141373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6056720595548284590760915 9085080893322426886141373)
        ·
          refine ⟨3406905334995910082303015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9085080893322426886141373 3406905334995910082303015)
          ·
            refine ⟨5110358002493865123454523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406905334995910082303015 5110358002493865123454523)
            ·
              refine ⟨7665537003740797685181785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5110358002493865123454523 7665537003740797685181785)
              ·
                refine ⟨5749152752805598263886339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7665537003740797685181785 5749152752805598263886339)
                ·
                  refine ⟨8623729129208397395829509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5749152752805598263886339 8623729129208397395829509)
                  ·
                    refine ⟨1616949211726574511718033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8623729129208397395829509 1616949211726574511718033)
                    ·
                      refine ⟨1212711908794930883788525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616949211726574511718033 1212711908794930883788525)
                      ·
                        rfl

theorem cell23_2361748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_2361748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361748 prefixEnd_2361748 := by exact prefixLift 2361748
  have htrace : WordTrace (prefixWord ++ tailWord_2361748) baseStart_2361748 baseEnd_2361748 := by
    simpa [prefixWord, tailWord_2361748, baseEnd_2361748] using wordTrace_append hprefix tailTrace_2361748
  have hstable : (prefixWord ++ tailWord_2361748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361748).length < 2 ^ (prefixWord ++ tailWord_2361748).sum := by decide
  have hdescent : baseEnd_2361748 < baseStart_2361748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361781 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 2, 3, 3]
def baseStart_2361781 : Nat := 118140960795 + 2361781 * 2 ^ 59
def prefixEnd_2361781 : Nat := 4983230072969 + 3 ^ 40 * 2361781 * 2
def baseEnd_2361781 : Nat := 1212728853656529254675873

theorem tailTrace_2361781 : CollatzResearch.WordTrace tailWord_2361781 prefixEnd_2361781 1212728853656529254675873 := by
  unfold tailWord_2361781
  simp only [CollatzResearch.WordTrace]
  refine ⟨86141229856678271926773197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57427486571118847951182131 86141229856678271926773197)
  ·
    refine ⟨32302961196254351972539949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86141229856678271926773197 32302961196254351972539949)
    ·
      refine ⟨12113610448595381989702481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32302961196254351972539949 12113610448595381989702481)
      ·
        refine ⟨9085207836446536492276861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12113610448595381989702481 9085207836446536492276861)
        ·
          refine ⟨3406952938667451184603823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9085207836446536492276861 3406952938667451184603823)
          ·
            refine ⟨5110429408001176776905735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3406952938667451184603823 5110429408001176776905735)
            ·
              refine ⟨7665644112001765165358603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5110429408001176776905735 7665644112001765165358603)
              ·
                refine ⟨11498466168002647748037905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7665644112001765165358603 11498466168002647748037905)
                ·
                  refine ⟨8623849626001985811028429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11498466168002647748037905 8623849626001985811028429)
                  ·
                    refine ⟨3233943609750744679135661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8623849626001985811028429 3233943609750744679135661)
                    ·
                      refine ⟨1212728853656529254675873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3233943609750744679135661 1212728853656529254675873)
                      ·
                        rfl

theorem cell23_2361781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_2361781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361781 prefixEnd_2361781 := by exact prefixLift 2361781
  have htrace : WordTrace (prefixWord ++ tailWord_2361781) baseStart_2361781 baseEnd_2361781 := by
    simpa [prefixWord, tailWord_2361781, baseEnd_2361781] using wordTrace_append hprefix tailTrace_2361781
  have hstable : (prefixWord ++ tailWord_2361781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361781).length < 2 ^ (prefixWord ++ tailWord_2361781).sum := by decide
  have hdescent : baseEnd_2361781 < baseStart_2361781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361817 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 6]
def baseStart_2361817 : Nat := 118140960795 + 2361817 * 2 ^ 59
def prefixEnd_2361817 : Nat := 4983230072969 + 3 ^ 40 * 2361817 * 2
def baseEnd_2361817 : Nat := 1212747338960091113825707

theorem tailTrace_2361817 : CollatzResearch.WordTrace tailWord_2361817 prefixEnd_2361817 1212747338960091113825707 := by
  unfold tailWord_2361817
  simp only [CollatzResearch.WordTrace]
  refine ⟨86142542884547850075083705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57428361923031900050055803 86142542884547850075083705)
  ·
    refine ⟨64606907163410887556312779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86142542884547850075083705 64606907163410887556312779)
    ·
      refine ⟨96910360745116331334469169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64606907163410887556312779 96910360745116331334469169)
      ·
        refine ⟨72682770558837248500851877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96910360745116331334469169 72682770558837248500851877)
        ·
          refine ⟨13628019479781984093909727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72682770558837248500851877 13628019479781984093909727)
          ·
            refine ⟨20442029219672976140864591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13628019479781984093909727 20442029219672976140864591)
            ·
              refine ⟨30663043829509464211296887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20442029219672976140864591 30663043829509464211296887)
              ·
                refine ⟨45994565744264196316945331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30663043829509464211296887 45994565744264196316945331)
                ·
                  refine ⟨68991848616396294475417997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45994565744264196316945331 68991848616396294475417997)
                  ·
                    refine ⟨25871943231148610428281749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 68991848616396294475417997 25871943231148610428281749)
                    ·
                      refine ⟨1212747338960091113825707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25871943231148610428281749 1212747338960091113825707)
                      ·
                        rfl

theorem cell23_2361817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_2361817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361817 prefixEnd_2361817 := by exact prefixLift 2361817
  have htrace : WordTrace (prefixWord ++ tailWord_2361817) baseStart_2361817 baseEnd_2361817 := by
    simpa [prefixWord, tailWord_2361817, baseEnd_2361817] using wordTrace_append hprefix tailTrace_2361817
  have hstable : (prefixWord ++ tailWord_2361817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361817).length < 2 ^ (prefixWord ++ tailWord_2361817).sum := by decide
  have hdescent : baseEnd_2361817 < baseStart_2361817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361821 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_2361821 : Nat := 118140960795 + 2361821 * 2 ^ 59
def prefixEnd_2361821 : Nat := 4983230072969 + 3 ^ 40 * 2361821 * 2
def baseEnd_2361821 : Nat := 1212749392882709098175689

theorem tailTrace_2361821 : CollatzResearch.WordTrace tailWord_2361821 prefixEnd_2361821 1212749392882709098175689 := by
  unfold tailWord_2361821
  simp only [CollatzResearch.WordTrace]
  refine ⟨86142688776533358758229317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57428459184355572505486211 86142688776533358758229317)
  ·
    refine ⟨16151754145600004767167997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86142688776533358758229317 16151754145600004767167997)
    ·
      refine ⟨6056907804600001787687999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16151754145600004767167997 6056907804600001787687999)
      ·
        refine ⟨9085361706900002681531999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6056907804600001787687999 9085361706900002681531999)
        ·
          refine ⟨13628042560350004022297999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9085361706900002681531999 13628042560350004022297999)
          ·
            refine ⟨20442063840525006033446999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13628042560350004022297999 20442063840525006033446999)
            ·
              refine ⟨30663095760787509050170499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20442063840525006033446999 30663095760787509050170499)
              ·
                refine ⟨45994643641181263575255749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30663095760787509050170499 45994643641181263575255749)
                ·
                  refine ⟨8623995682721486920360453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45994643641181263575255749 8623995682721486920360453)
                  ·
                    refine ⟨1616999190510278797567585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8623995682721486920360453 1616999190510278797567585)
                    ·
                      refine ⟨1212749392882709098175689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1616999190510278797567585 1212749392882709098175689)
                      ·
                        rfl

theorem cell23_2361821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_2361821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361821 prefixEnd_2361821 := by exact prefixLift 2361821
  have htrace : WordTrace (prefixWord ++ tailWord_2361821) baseStart_2361821 baseEnd_2361821 := by
    simpa [prefixWord, tailWord_2361821, baseEnd_2361821] using wordTrace_append hprefix tailTrace_2361821
  have hstable : (prefixWord ++ tailWord_2361821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361821).length < 2 ^ (prefixWord ++ tailWord_2361821).sum := by decide
  have hdescent : baseEnd_2361821 < baseStart_2361821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361824 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 3]
def baseStart_2361824 : Nat := 118140960795 + 2361824 * 2 ^ 59
def prefixEnd_2361824 : Nat := 4983230072969 + 3 ^ 40 * 2361824 * 2
def baseEnd_2361824 : Nat := 1212750933324672586438175

theorem tailTrace_2361824 : CollatzResearch.WordTrace tailWord_2361824 prefixEnd_2361824 1212750933324672586438175 := by
  unfold tailWord_2361824
  simp only [CollatzResearch.WordTrace]
  refine ⟨43071399097761245135294263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57428532130348326847059017 43071399097761245135294263)
  ·
    refine ⟨64607098646641867702941395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43071399097761245135294263 64607098646641867702941395)
    ·
      refine ⟨96910647969962801554412093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64607098646641867702941395 96910647969962801554412093)
      ·
        refine ⟨36341492988736050582904535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96910647969962801554412093 36341492988736050582904535)
        ·
          refine ⟨54512239483104075874356803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36341492988736050582904535 54512239483104075874356803)
          ·
            refine ⟨81768359224656113811535205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54512239483104075874356803 81768359224656113811535205)
            ·
              refine ⟨15331567354623021339662851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81768359224656113811535205 15331567354623021339662851)
              ·
                refine ⟨22997351031934532009494277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15331567354623021339662851 22997351031934532009494277)
                ·
                  refine ⟨4312003318487724751780177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22997351031934532009494277 4312003318487724751780177)
                  ·
                    refine ⟨3234002488865793563835133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4312003318487724751780177 3234002488865793563835133)
                    ·
                      refine ⟨1212750933324672586438175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3234002488865793563835133 1212750933324672586438175)
                      ·
                        rfl

theorem cell23_2361824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_2361824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361824 prefixEnd_2361824 := by exact prefixLift 2361824
  have htrace : WordTrace (prefixWord ++ tailWord_2361824) baseStart_2361824 baseEnd_2361824 := by
    simpa [prefixWord, tailWord_2361824, baseEnd_2361824] using wordTrace_append hprefix tailTrace_2361824
  have hstable : (prefixWord ++ tailWord_2361824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361824).length < 2 ^ (prefixWord ++ tailWord_2361824).sum := by decide
  have hdescent : baseEnd_2361824 < baseStart_2361824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361831 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 3, 4]
def baseStart_2361831 : Nat := 118140960795 + 2361831 * 2 ^ 59
def prefixEnd_2361831 : Nat := 4983230072969 + 3 ^ 40 * 2361831 * 2
def baseEnd_2361831 : Nat := 404251509229751353016881

theorem tailTrace_2361831 : CollatzResearch.WordTrace tailWord_2361831 prefixEnd_2361831 404251509229751353016881 := by
  unfold tailWord_2361831
  simp only [CollatzResearch.WordTrace]
  refine ⟨86143053506497130466093347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57428702337664753644062231 86143053506497130466093347)
  ·
    refine ⟨129214580259745695699140021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86143053506497130466093347 129214580259745695699140021)
    ·
      refine ⟨12113866899351158971794377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129214580259745695699140021 12113866899351158971794377)
      ·
        refine ⟨9085400174513369228845783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12113866899351158971794377 9085400174513369228845783)
        ·
          refine ⟨13628100261770053843268675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9085400174513369228845783 13628100261770053843268675)
          ·
            refine ⟨20442150392655080764903013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13628100261770053843268675 20442150392655080764903013)
            ·
              refine ⟨3832903198622827643419315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20442150392655080764903013 3832903198622827643419315)
              ·
                refine ⟨5749354797934241465128973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3832903198622827643419315 5749354797934241465128973)
                ·
                  refine ⟨2156008049225340549423365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5749354797934241465128973 2156008049225340549423365)
                  ·
                    refine ⟨404251509229751353016881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2156008049225340549423365 404251509229751353016881)
                    ·
                      rfl

theorem cell23_2361831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_2361831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361831 prefixEnd_2361831 := by exact prefixLift 2361831
  have htrace : WordTrace (prefixWord ++ tailWord_2361831) baseStart_2361831 baseEnd_2361831 := by
    simpa [prefixWord, tailWord_2361831, baseEnd_2361831] using wordTrace_append hprefix tailTrace_2361831
  have hstable : (prefixWord ++ tailWord_2361831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361831).length < 2 ^ (prefixWord ++ tailWord_2361831).sum := by decide
  have hdescent : baseEnd_2361831 < baseStart_2361831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361881 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 2, 3, 2]
def baseStart_2361881 : Nat := 118140960795 + 2361881 * 2 ^ 59
def prefixEnd_2361881 : Nat := 4983230072969 + 3 ^ 40 * 2361881 * 2
def baseEnd_2361881 : Nat := 1212780201721978863425413

theorem tailTrace_2361881 : CollatzResearch.WordTrace tailWord_2361881 prefixEnd_2361881 1212780201721978863425413 := by
  unfold tailWord_2361881
  simp only [CollatzResearch.WordTrace]
  refine ⟨86144877156315989005413497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57429918104210659336942331 86144877156315989005413497)
  ·
    refine ⟨64608657867236991754060123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86144877156315989005413497 64608657867236991754060123)
    ·
      refine ⟨96912986800855487631090185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64608657867236991754060123 96912986800855487631090185)
      ·
        refine ⟨72684740100641615723317639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96912986800855487631090185 72684740100641615723317639)
        ·
          refine ⟨109027110150962423584976459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72684740100641615723317639 109027110150962423584976459)
          ·
            refine ⟨163540665226443635377464689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109027110150962423584976459 163540665226443635377464689)
            ·
              refine ⟨122655498919832726533098517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163540665226443635377464689 122655498919832726533098517)
              ·
                refine ⟨5749476511867159056238993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122655498919832726533098517 5749476511867159056238993)
                ·
                  refine ⟨4312107383900369292179245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5749476511867159056238993 4312107383900369292179245)
                  ·
                    refine ⟨1617040268962638484567217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4312107383900369292179245 1617040268962638484567217)
                    ·
                      refine ⟨1212780201721978863425413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617040268962638484567217 1212780201721978863425413)
                      ·
                        rfl

theorem cell23_2361881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 3, 2].length) (baseStart_2361881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361881 prefixEnd_2361881 := by exact prefixLift 2361881
  have htrace : WordTrace (prefixWord ++ tailWord_2361881) baseStart_2361881 baseEnd_2361881 := by
    simpa [prefixWord, tailWord_2361881, baseEnd_2361881] using wordTrace_append hprefix tailTrace_2361881
  have hstable : (prefixWord ++ tailWord_2361881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361881).length < 2 ^ (prefixWord ++ tailWord_2361881).sum := by decide
  have hdescent : baseEnd_2361881 < baseStart_2361881 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361921 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 1, 6]
def baseStart_2361921 : Nat := 118140960795 + 2361921 * 2 ^ 59
def prefixEnd_2361921 : Nat := 4983230072969 + 3 ^ 40 * 2361921 * 2
def baseEnd_2361921 : Nat := 404266913649386235641743

theorem tailTrace_2361921 : CollatzResearch.WordTrace tailWord_2361921 prefixEnd_2361921 404266913649386235641743 := by
  unfold tailWord_2361921
  simp only [CollatzResearch.WordTrace]
  refine ⟨86146336076171075836869617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57430890717447383891246411 86146336076171075836869617)
  ·
    refine ⟨64609752057128306877652213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86146336076171075836869617 64609752057128306877652213)
    ·
      refine ⟨6057164255355778769779895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64609752057128306877652213 6057164255355778769779895)
      ·
        refine ⟨9085746383033668154669843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6057164255355778769779895 9085746383033668154669843)
        ·
          refine ⟨13628619574550502232004765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9085746383033668154669843 13628619574550502232004765)
          ·
            refine ⟨5110732340456438337001787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13628619574550502232004765 5110732340456438337001787)
            ·
              refine ⟨7666098510684657505502681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5110732340456438337001787 7666098510684657505502681)
              ·
                refine ⟨5749573883013493129127011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7666098510684657505502681 5749573883013493129127011)
                ·
                  refine ⟨8624360824520239693690517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5749573883013493129127011 8624360824520239693690517)
                  ·
                    refine ⟨404266913649386235641743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8624360824520239693690517 404266913649386235641743)
                    ·
                      rfl

theorem cell23_2361921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_2361921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361921 prefixEnd_2361921 := by exact prefixLift 2361921
  have htrace : WordTrace (prefixWord ++ tailWord_2361921) baseStart_2361921 baseEnd_2361921 := by
    simpa [prefixWord, tailWord_2361921, baseEnd_2361921] using wordTrace_append hprefix tailTrace_2361921
  have hstable : (prefixWord ++ tailWord_2361921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361921).length < 2 ^ (prefixWord ++ tailWord_2361921).sum := by decide
  have hdescent : baseEnd_2361921 < baseStart_2361921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361931 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 1, 2, 3]
def baseStart_2361931 : Nat := 118140960795 + 2361931 * 2 ^ 59
def prefixEnd_2361931 : Nat := 4983230072969 + 3 ^ 40 * 2361931 * 2
def baseEnd_2361931 : Nat := 1212805875754703667800183

theorem tailTrace_2361931 : CollatzResearch.WordTrace tailWord_2361931 prefixEnd_2361931 1212805875754703667800183 := by
  unfold tailWord_2361931
  simp only [CollatzResearch.WordTrace]
  refine ⟨86146700806134847544733647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57431133870756565029822431 86146700806134847544733647)
  ·
    refine ⟨129220051209202271317100471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86146700806134847544733647 129220051209202271317100471)
    ·
      refine ⟨193830076813803406975650707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129220051209202271317100471 193830076813803406975650707)
      ·
        refine ⟨290745115220705110463476061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193830076813803406975650707 290745115220705110463476061)
        ·
          refine ⟨109029418207764416423803523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290745115220705110463476061 109029418207764416423803523)
          ·
            refine ⟨163544127311646624635705285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109029418207764416423803523 163544127311646624635705285)
            ·
              refine ⟨30664523870933742119194741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163544127311646624635705285 30664523870933742119194741)
              ·
                refine ⟨2874799112900038323674507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30664523870933742119194741 2874799112900038323674507)
                ·
                  refine ⟨4312198669350057485511761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2874799112900038323674507 4312198669350057485511761)
                  ·
                    refine ⟨3234149002012543114133821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4312198669350057485511761 3234149002012543114133821)
                    ·
                      refine ⟨1212805875754703667800183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3234149002012543114133821 1212805875754703667800183)
                      ·
                        rfl

theorem cell23_2361931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 2, 3].length) (baseStart_2361931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361931 prefixEnd_2361931 := by exact prefixLift 2361931
  have htrace : WordTrace (prefixWord ++ tailWord_2361931) baseStart_2361931 baseEnd_2361931 := by
    simpa [prefixWord, tailWord_2361931, baseEnd_2361931] using wordTrace_append hprefix tailTrace_2361931
  have hstable : (prefixWord ++ tailWord_2361931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361931).length < 2 ^ (prefixWord ++ tailWord_2361931).sum := by decide
  have hdescent : baseEnd_2361931 < baseStart_2361931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361938 : List Nat := [3, 2, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_2361938 : Nat := 118140960795 + 2361938 * 2 ^ 59
def prefixEnd_2361938 : Nat := 4983230072969 + 3 ^ 40 * 2361938 * 2
def baseEnd_2361938 : Nat := 404269823373095046804217

theorem tailTrace_2361938 : CollatzResearch.WordTrace tailWord_2361938 prefixEnd_2361938 404269823373095046804217 := by
  unfold tailWord_2361938
  simp only [CollatzResearch.WordTrace]
  refine ⟨21536739029277371935059617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57431304078072991826825645 21536739029277371935059617)
  ·
    refine ⟨16152554271958028951294713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21536739029277371935059617 16152554271958028951294713)
    ·
      refine ⟨12114415703968521713471035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16152554271958028951294713 12114415703968521713471035)
      ·
        refine ⟨18171623555952782570206553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12114415703968521713471035 18171623555952782570206553)
        ·
          refine ⟨13628717666964586927654915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18171623555952782570206553 13628717666964586927654915)
          ·
            refine ⟨20443076500446880391482373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13628717666964586927654915 20443076500446880391482373)
            ·
              refine ⟨3833076843833790073402945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20443076500446880391482373 3833076843833790073402945)
              ·
                refine ⟨2874807632875342555052209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3833076843833790073402945 2874807632875342555052209)
                ·
                  refine ⟨2156105724656506916289157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2874807632875342555052209 2156105724656506916289157)
                  ·
                    refine ⟨404269823373095046804217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2156105724656506916289157 404269823373095046804217)
                    ·
                      rfl

theorem cell23_2361938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_2361938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361938 prefixEnd_2361938 := by exact prefixLift 2361938
  have htrace : WordTrace (prefixWord ++ tailWord_2361938) baseStart_2361938 baseEnd_2361938 := by
    simpa [prefixWord, tailWord_2361938, baseEnd_2361938] using wordTrace_append hprefix tailTrace_2361938
  have hstable : (prefixWord ++ tailWord_2361938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361938).length < 2 ^ (prefixWord ++ tailWord_2361938).sum := by decide
  have hdescent : baseEnd_2361938 < baseStart_2361938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2361961 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 6, 1, 3]
def baseStart_2361961 : Nat := 118140960795 + 2361961 * 2 ^ 59
def prefixEnd_2361961 : Nat := 4983230072969 + 3 ^ 40 * 2361961 * 2
def baseEnd_2361961 : Nat := 1212821280174338550425045

theorem tailTrace_2361961 : CollatzResearch.WordTrace tailWord_2361961 prefixEnd_2361961 1212821280174338550425045 := by
  unfold tailWord_2361961
  simp only [CollatzResearch.WordTrace]
  refine ⟨86147794996026162668325737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57431863330684108445550491 86147794996026162668325737)
  ·
    refine ⟨64610846247019622001244303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86147794996026162668325737 64610846247019622001244303)
    ·
      refine ⟨96916269370529433001866455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64610846247019622001244303 96916269370529433001866455)
      ·
        refine ⟨145374404055794149502799683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96916269370529433001866455 145374404055794149502799683)
        ·
          refine ⟨218061606083691224254199525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145374404055794149502799683 218061606083691224254199525)
          ·
            refine ⟨40886551140692104547662411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 218061606083691224254199525 40886551140692104547662411)
            ·
              refine ⟨61329826711038156821493617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40886551140692104547662411 61329826711038156821493617)
              ·
                refine ⟨45997370033278617616120213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61329826711038156821493617 45997370033278617616120213)
                ·
                  refine ⟨2156126720309935200755635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 45997370033278617616120213 2156126720309935200755635)
                  ·
                    refine ⟨3234190080464902801133453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2156126720309935200755635 3234190080464902801133453)
                    ·
                      refine ⟨1212821280174338550425045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3234190080464902801133453 1212821280174338550425045)
                      ·
                        rfl

theorem cell23_2361961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 6, 1, 3].length) (baseStart_2361961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2361961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2361961 prefixEnd_2361961 := by exact prefixLift 2361961
  have htrace : WordTrace (prefixWord ++ tailWord_2361961) baseStart_2361961 baseEnd_2361961 := by
    simpa [prefixWord, tailWord_2361961, baseEnd_2361961] using wordTrace_append hprefix tailTrace_2361961
  have hstable : (prefixWord ++ tailWord_2361961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2361961).length < 2 ^ (prefixWord ++ tailWord_2361961).sum := by decide
  have hdescent : baseEnd_2361961 < baseStart_2361961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2361961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362012 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_2362012 : Nat := 118140960795 + 2362012 * 2 ^ 59
def prefixEnd_2362012 : Nat := 4983230072969 + 3 ^ 40 * 2362012 * 2
def baseEnd_2362012 : Nat := 1212847467687717850887311

theorem tailTrace_2362012 : CollatzResearch.WordTrace tailWord_2362012 prefixEnd_2362012 1212847467687717850887311 := by
  unfold tailWord_2362012
  simp only [CollatzResearch.WordTrace]
  refine ⟨43074827559420699189216145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57433103412560932252288193 43074827559420699189216145)
  ·
    refine ⟨32306120669565524391912109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43074827559420699189216145 32306120669565524391912109)
    ·
      refine ⟨12114795251087071646967041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32306120669565524391912109 12114795251087071646967041)
      ·
        refine ⟨9086096438315303735225281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12114795251087071646967041 9086096438315303735225281)
        ·
          refine ⟨6814572328736477801418961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9086096438315303735225281 6814572328736477801418961)
          ·
            refine ⟨5110929246552358351064221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6814572328736477801418961 5110929246552358351064221)
            ·
              refine ⟨1916598467457134381649083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5110929246552358351064221 1916598467457134381649083)
              ·
                refine ⟨2874897701185701572473625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1916598467457134381649083 2874897701185701572473625)
                ·
                  refine ⟨2156173275889276179355219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2874897701185701572473625 2156173275889276179355219)
                  ·
                    refine ⟨3234259913833914269032829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2156173275889276179355219 3234259913833914269032829)
                    ·
                      refine ⟨1212847467687717850887311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3234259913833914269032829 1212847467687717850887311)
                      ·
                        rfl

theorem cell23_2362012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_2362012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362012 prefixEnd_2362012 := by exact prefixLift 2362012
  have htrace : WordTrace (prefixWord ++ tailWord_2362012) baseStart_2362012 baseEnd_2362012 := by
    simpa [prefixWord, tailWord_2362012, baseEnd_2362012] using wordTrace_append hprefix tailTrace_2362012
  have hstable : (prefixWord ++ tailWord_2362012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362012).length < 2 ^ (prefixWord ++ tailWord_2362012).sum := by decide
  have hdescent : baseEnd_2362012 < baseStart_2362012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362058 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 7]
def baseStart_2362058 : Nat := 118140960795 + 2362058 * 2 ^ 59
def prefixEnd_2362058 : Nat := 4983230072969 + 3 ^ 40 * 2362058 * 2
def baseEnd_2362058 : Nat := 134763454199758296768011

theorem tailTrace_2362058 : CollatzResearch.WordTrace tailWord_2362058 prefixEnd_2362058 134763454199758296768011 := by
  unfold tailWord_2362058
  simp only [CollatzResearch.WordTrace]
  refine ⟨21537833219168687058651707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57434221917783165489737885 21537833219168687058651707)
  ·
    refine ⟨32306749828753030587977561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21537833219168687058651707 32306749828753030587977561)
    ·
      refine ⟨24230062371564772940983171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32306749828753030587977561 24230062371564772940983171)
      ·
        refine ⟨36345093557347159411474757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24230062371564772940983171 36345093557347159411474757)
        ·
          refine ⟨6814705042002592389651517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36345093557347159411474757 6814705042002592389651517)
          ·
            refine ⟨2555514390750972146119319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6814705042002592389651517 2555514390750972146119319)
            ·
              refine ⟨3833271586126458219178979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555514390750972146119319 3833271586126458219178979)
              ·
                refine ⟨5749907379189687328768469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3833271586126458219178979 5749907379189687328768469)
                ·
                  refine ⟨134763454199758296768011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5749907379189687328768469 134763454199758296768011)
                  ·
                    rfl

theorem cell23_2362058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_2362058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362058 prefixEnd_2362058 := by exact prefixLift 2362058
  have htrace : WordTrace (prefixWord ++ tailWord_2362058) baseStart_2362058 baseEnd_2362058 := by
    simpa [prefixWord, tailWord_2362058, baseEnd_2362058] using wordTrace_append hprefix tailTrace_2362058
  have hstable : (prefixWord ++ tailWord_2362058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362058).length < 2 ^ (prefixWord ++ tailWord_2362058).sum := by decide
  have hdescent : baseEnd_2362058 < baseStart_2362058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362069 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2362069 : Nat := 118140960795 + 2362069 * 2 ^ 59
def prefixEnd_2362069 : Nat := 4983230072969 + 3 ^ 40 * 2362069 * 2
def baseEnd_2362069 : Nat := 1212876736085024127874549

theorem tailTrace_2362069 : CollatzResearch.WordTrace tailWord_2362069 prefixEnd_2362069 1212876736085024127874549 := by
  unfold tailWord_2362069
  simp only [CollatzResearch.WordTrace]
  refine ⟨86151734079634897113257261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57434489386423264742171507 86151734079634897113257261)
  ·
    refine ⟨32306900279863086417471473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86151734079634897113257261 32306900279863086417471473)
    ·
      refine ⟨24230175209897314813103605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32306900279863086417471473 24230175209897314813103605)
      ·
        refine ⟨2271578925927873263728463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24230175209897314813103605 2271578925927873263728463)
        ·
          refine ⟨3407368388891809895592695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271578925927873263728463 3407368388891809895592695)
          ·
            refine ⟨5111052583337714843389043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3407368388891809895592695 5111052583337714843389043)
            ·
              refine ⟨7666578875006572265083565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5111052583337714843389043 7666578875006572265083565)
              ·
                refine ⟨2874967078127464599406337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7666578875006572265083565 2874967078127464599406337)
                ·
                  refine ⟨2156225308595598449554753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2874967078127464599406337 2156225308595598449554753)
                  ·
                    refine ⟨1617168981446698837166065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2156225308595598449554753 1617168981446698837166065)
                    ·
                      refine ⟨1212876736085024127874549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617168981446698837166065 1212876736085024127874549)
                      ·
                        rfl

theorem cell23_2362069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2362069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362069 prefixEnd_2362069 := by exact prefixLift 2362069
  have htrace : WordTrace (prefixWord ++ tailWord_2362069) baseStart_2362069 baseEnd_2362069 := by
    simpa [prefixWord, tailWord_2362069, baseEnd_2362069] using wordTrace_append hprefix tailTrace_2362069
  have hstable : (prefixWord ++ tailWord_2362069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362069).length < 2 ^ (prefixWord ++ tailWord_2362069).sum := by decide
  have hdescent : baseEnd_2362069 < baseStart_2362069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362108 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_2362108 : Nat := 118140960795 + 2362108 * 2 ^ 59
def prefixEnd_2362108 : Nat := 4983230072969 + 3 ^ 40 * 2362108 * 2
def baseEnd_2362108 : Nat := 1212896761830549475286869

theorem tailTrace_2362108 : CollatzResearch.WordTrace tailWord_2362108 prefixEnd_2362108 1212896761830549475286869 := by
  unfold tailWord_2362108
  simp only [CollatzResearch.WordTrace]
  refine ⟨43076578263246803386963489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57435437684329071182617985 43076578263246803386963489)
  ·
    refine ⟨32307433697435102540222617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43076578263246803386963489 32307433697435102540222617)
    ·
      refine ⟨24230575273076326905166963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32307433697435102540222617 24230575273076326905166963)
      ·
        refine ⟨36345862909614490357750445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24230575273076326905166963 36345862909614490357750445)
        ·
          refine ⟨13629698591105433884156417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36345862909614490357750445 13629698591105433884156417)
          ·
            refine ⟨10222273943329075413117313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13629698591105433884156417 10222273943329075413117313)
            ·
              refine ⟨7666705457496806559837985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10222273943329075413117313 7666705457496806559837985)
              ·
                refine ⟨5750029093122604919878489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7666705457496806559837985 5750029093122604919878489)
                ·
                  refine ⟨4312521819841953689908867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5750029093122604919878489 4312521819841953689908867)
                  ·
                    refine ⟨6468782729762930534863301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4312521819841953689908867 6468782729762930534863301)
                    ·
                      refine ⟨1212896761830549475286869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6468782729762930534863301 1212896761830549475286869)
                      ·
                        rfl

theorem cell23_2362108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_2362108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362108 prefixEnd_2362108 := by exact prefixLift 2362108
  have htrace : WordTrace (prefixWord ++ tailWord_2362108) baseStart_2362108 baseEnd_2362108 := by
    simpa [prefixWord, tailWord_2362108, baseEnd_2362108] using wordTrace_append hprefix tailTrace_2362108
  have hstable : (prefixWord ++ tailWord_2362108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362108).length < 2 ^ (prefixWord ++ tailWord_2362108).sum := by decide
  have hdescent : baseEnd_2362108 < baseStart_2362108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362111 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 3]
def baseStart_2362111 : Nat := 118140960795 + 2362111 * 2 ^ 59
def prefixEnd_2362111 : Nat := 4983230072969 + 3 ^ 40 * 2362111 * 2
def baseEnd_2362111 : Nat := 1212898302272512963549355

theorem tailTrace_2362111 : CollatzResearch.WordTrace tailWord_2362111 prefixEnd_2362111 1212898302272512963549355 := by
  unfold tailWord_2362111
  simp only [CollatzResearch.WordTrace]
  refine ⟨86153265945482738286286187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57435510630321825524190791 86153265945482738286286187)
  ·
    refine ⟨129229898918224107429429281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86153265945482738286286187 129229898918224107429429281)
    ·
      refine ⟨96922424188668080572071961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129229898918224107429429281 96922424188668080572071961)
      ·
        refine ⟨72691818141501060429053971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96922424188668080572071961 72691818141501060429053971)
        ·
          refine ⟨109037727212251590643580957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72691818141501060429053971 109037727212251590643580957)
          ·
            refine ⟨40889147704594346491342859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109037727212251590643580957 40889147704594346491342859)
            ·
              refine ⟨61333721556891519737014289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40889147704594346491342859 61333721556891519737014289)
              ·
                refine ⟨46000291167668639802760717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61333721556891519737014289 46000291167668639802760717)
                ·
                  refine ⟨17250109187875739926035269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46000291167668639802760717 17250109187875739926035269)
                  ·
                    refine ⟨3234395472726701236131613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17250109187875739926035269 3234395472726701236131613)
                    ·
                      refine ⟨1212898302272512963549355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3234395472726701236131613 1212898302272512963549355)
                      ·
                        rfl

theorem cell23_2362111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_2362111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362111 prefixEnd_2362111 := by exact prefixLift 2362111
  have htrace : WordTrace (prefixWord ++ tailWord_2362111) baseStart_2362111 baseEnd_2362111 := by
    simpa [prefixWord, tailWord_2362111, baseEnd_2362111] using wordTrace_append hprefix tailTrace_2362111
  have hstable : (prefixWord ++ tailWord_2362111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362111).length < 2 ^ (prefixWord ++ tailWord_2362111).sum := by decide
  have hdescent : baseEnd_2362111 < baseStart_2362111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362131 : List Nat := [1, 1, 1, 2, 1, 3, 3, 5, 6]
def baseStart_2362131 : Nat := 118140960795 + 2362131 * 2 ^ 59
def prefixEnd_2362131 : Nat := 4983230072969 + 3 ^ 40 * 2362131 * 2
def baseEnd_2362131 : Nat := 134767619098400320588807

theorem tailTrace_2362131 : CollatzResearch.WordTrace tailWord_2362131 prefixEnd_2362131 134767619098400320588807 := by
  unfold tailWord_2362131
  simp only [CollatzResearch.WordTrace]
  refine ⟨86153995405410281702014247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57435996936940187801342831 86153995405410281702014247)
  ·
    refine ⟨129230993108115422553021371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86153995405410281702014247 129230993108115422553021371)
    ·
      refine ⟨193846489662173133829532057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129230993108115422553021371 193846489662173133829532057)
      ·
        refine ⟨145384867246629850372149043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193846489662173133829532057 145384867246629850372149043)
        ·
          refine ⟨218077300869944775558223565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145384867246629850372149043 218077300869944775558223565)
          ·
            refine ⟨81778987826229290834333837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 218077300869944775558223565 81778987826229290834333837)
            ·
              refine ⟨30667120434835984062875189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81778987826229290834333837 30667120434835984062875189)
              ·
                refine ⟨2875042540765873505894549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30667120434835984062875189 2875042540765873505894549)
                ·
                  refine ⟨134767619098400320588807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2875042540765873505894549 134767619098400320588807)
                  ·
                    rfl

theorem cell23_2362131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 5, 6].length) (baseStart_2362131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362131 prefixEnd_2362131 := by exact prefixLift 2362131
  have htrace : WordTrace (prefixWord ++ tailWord_2362131) baseStart_2362131 baseEnd_2362131 := by
    simpa [prefixWord, tailWord_2362131, baseEnd_2362131] using wordTrace_append hprefix tailTrace_2362131
  have hstable : (prefixWord ++ tailWord_2362131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362131).length < 2 ^ (prefixWord ++ tailWord_2362131).sum := by decide
  have hdescent : baseEnd_2362131 < baseStart_2362131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362135 : List Nat := [1, 1, 3, 4, 3, 1, 1, 2, 3, 4]
def baseStart_2362135 : Nat := 118140960795 + 2362135 * 2 ^ 59
def prefixEnd_2362135 : Nat := 4983230072969 + 3 ^ 40 * 2362135 * 2
def baseEnd_2362135 : Nat := 404303541936073623216415

theorem tailTrace_2362135 : CollatzResearch.WordTrace tailWord_2362135 prefixEnd_2362135 404303541936073623216415 := by
  unfold tailWord_2362135
  simp only [CollatzResearch.WordTrace]
  refine ⟨86154141297395790385159859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57436094198263860256773239 86154141297395790385159859)
  ·
    refine ⟨129231211946093685577739789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86154141297395790385159859 129231211946093685577739789)
    ·
      refine ⟨48461704479785132091652421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129231211946093685577739789 48461704479785132091652421)
      ·
        refine ⟨9086569589959712267184829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48461704479785132091652421 9086569589959712267184829)
        ·
          refine ⟨3407463596234892100194311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9086569589959712267184829 3407463596234892100194311)
          ·
            refine ⟨5111195394352338150291467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3407463596234892100194311 5111195394352338150291467)
            ·
              refine ⟨7666793091528507225437201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5111195394352338150291467 7666793091528507225437201)
              ·
                refine ⟨5750094818646380419077901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7666793091528507225437201 5750094818646380419077901)
                ·
                  refine ⟨2156285556992392657154213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5750094818646380419077901 2156285556992392657154213)
                  ·
                    refine ⟨404303541936073623216415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2156285556992392657154213 404303541936073623216415)
                    ·
                      rfl

theorem cell23_2362135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_2362135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362135 prefixEnd_2362135 := by exact prefixLift 2362135
  have htrace : WordTrace (prefixWord ++ tailWord_2362135) baseStart_2362135 baseEnd_2362135 := by
    simpa [prefixWord, tailWord_2362135, baseEnd_2362135] using wordTrace_append hprefix tailTrace_2362135
  have hstable : (prefixWord ++ tailWord_2362135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362135).length < 2 ^ (prefixWord ++ tailWord_2362135).sum := by decide
  have hdescent : baseEnd_2362135 < baseStart_2362135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362152 : List Nat := [2, 1, 5, 1, 1, 1, 4, 3, 1, 4]
def baseStart_2362152 : Nat := 118140960795 + 2362152 * 2 ^ 59
def prefixEnd_2362152 : Nat := 4983230072969 + 3 ^ 40 * 2362152 * 2
def baseEnd_2362152 : Nat := 404306451659782434378889

theorem tailTrace_2362152 : CollatzResearch.WordTrace tailWord_2362152 prefixEnd_2362152 404306451659782434378889 := by
  unfold tailWord_2362152
  simp only [CollatzResearch.WordTrace]
  refine ⟨43077380669167101144264355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57436507558889468192352473 43077380669167101144264355)
  ·
    refine ⟨64616071003750651716396533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43077380669167101144264355 64616071003750651716396533)
    ·
      refine ⟨6057756656601623598412175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64616071003750651716396533 6057756656601623598412175)
      ·
        refine ⟨9086634984902435397618263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6057756656601623598412175 9086634984902435397618263)
        ·
          refine ⟨13629952477353653096427395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9086634984902435397618263 13629952477353653096427395)
          ·
            refine ⟨20444928716030479644641093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13629952477353653096427395 20444928716030479644641093)
            ·
              refine ⟨3833424134255714933370205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20444928716030479644641093 3833424134255714933370205)
              ·
                refine ⟨1437534050345893100013827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3833424134255714933370205 1437534050345893100013827)
                ·
                  refine ⟨2156301075518839650020741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437534050345893100013827 2156301075518839650020741)
                  ·
                    refine ⟨404306451659782434378889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2156301075518839650020741 404306451659782434378889)
                    ·
                      rfl

theorem cell23_2362152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_2362152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362152 prefixEnd_2362152 := by exact prefixLift 2362152
  have htrace : WordTrace (prefixWord ++ tailWord_2362152) baseStart_2362152 baseEnd_2362152 := by
    simpa [prefixWord, tailWord_2362152, baseEnd_2362152] using wordTrace_append hprefix tailTrace_2362152
  have hstable : (prefixWord ++ tailWord_2362152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362152).length < 2 ^ (prefixWord ++ tailWord_2362152).sum := by decide
  have hdescent : baseEnd_2362152 < baseStart_2362152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362165 : List Nat := [1, 3, 3, 1, 3, 3, 1, 2, 6]
def baseStart_2362165 : Nat := 118140960795 + 2362165 * 2 ^ 59
def prefixEnd_2362165 : Nat := 4983230072969 + 3 ^ 40 * 2362165 * 2
def baseEnd_2362165 : Nat := 134769558914206194697123

theorem tailTrace_2362165 : CollatzResearch.WordTrace tailWord_2362165 prefixEnd_2362165 134769558914206194697123 := by
  unfold tailWord_2362165
  simp only [CollatzResearch.WordTrace]
  refine ⟨86155235487287105508751949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57436823658191403672501299 86155235487287105508751949)
  ·
    refine ⟨32308213307732664565781981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86155235487287105508751949 32308213307732664565781981)
    ·
      refine ⟨12115579990399749212168243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32308213307732664565781981 12115579990399749212168243)
      ·
        refine ⟨18173369985599623818252365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12115579990399749212168243 18173369985599623818252365)
        ·
          refine ⟨6815013744599858931844637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18173369985599623818252365 6815013744599858931844637)
          ·
            refine ⟨2555630154224947099441739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6815013744599858931844637 2555630154224947099441739)
            ·
              refine ⟨3833445231337420649162609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2555630154224947099441739 3833445231337420649162609)
              ·
                refine ⟨2875083923503065486871957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3833445231337420649162609 2875083923503065486871957)
                ·
                  refine ⟨134769558914206194697123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2875083923503065486871957 134769558914206194697123)
                  ·
                    rfl

theorem cell23_2362165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 1, 2, 6].length) (baseStart_2362165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362165 prefixEnd_2362165 := by exact prefixLift 2362165
  have htrace : WordTrace (prefixWord ++ tailWord_2362165) baseStart_2362165 baseEnd_2362165 := by
    simpa [prefixWord, tailWord_2362165, baseEnd_2362165] using wordTrace_append hprefix tailTrace_2362165
  have hstable : (prefixWord ++ tailWord_2362165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362165).length < 2 ^ (prefixWord ++ tailWord_2362165).sum := by decide
  have hdescent : baseEnd_2362165 < baseStart_2362165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362175 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 3, 1, 3]
def baseStart_2362175 : Nat := 118140960795 + 2362175 * 2 ^ 59
def prefixEnd_2362175 : Nat := 4983230072969 + 3 ^ 40 * 2362175 * 2
def baseEnd_2362175 : Nat := 1212931165034400713149061

theorem tailTrace_2362175 : CollatzResearch.WordTrace tailWord_2362175 prefixEnd_2362175 1212931165034400713149061 := by
  unfold tailWord_2362175
  simp only [CollatzResearch.WordTrace]
  refine ⟨86155600217250877216615979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57437066811500584811077319 86155600217250877216615979)
  ·
    refine ⟨129233400325876315824923969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86155600217250877216615979 129233400325876315824923969)
    ·
      refine ⟨96925050244407236868692977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129233400325876315824923969 96925050244407236868692977)
      ·
        refine ⟨72693787683305427651519733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96925050244407236868692977 72693787683305427651519733)
        ·
          refine ⟨6815042595309883842329975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72693787683305427651519733 6815042595309883842329975)
          ·
            refine ⟨10222563892964825763494963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6815042595309883842329975 10222563892964825763494963)
            ·
              refine ⟨15333845839447238645242445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10222563892964825763494963 15333845839447238645242445)
              ·
                refine ⟨5750192189792714491965917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15333845839447238645242445 5750192189792714491965917)
                ·
                  refine ⟨2156322071172267934487219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5750192189792714491965917 2156322071172267934487219)
                  ·
                    refine ⟨3234483106758401901730829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2156322071172267934487219 3234483106758401901730829)
                    ·
                      refine ⟨1212931165034400713149061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3234483106758401901730829 1212931165034400713149061)
                      ·
                        rfl

theorem cell23_2362175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_2362175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362175 prefixEnd_2362175 := by exact prefixLift 2362175
  have htrace : WordTrace (prefixWord ++ tailWord_2362175) baseStart_2362175 baseEnd_2362175 := by
    simpa [prefixWord, tailWord_2362175, baseEnd_2362175] using wordTrace_append hprefix tailTrace_2362175
  have hstable : (prefixWord ++ tailWord_2362175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362175).length < 2 ^ (prefixWord ++ tailWord_2362175).sum := by decide
  have hdescent : baseEnd_2362175 < baseStart_2362175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362181 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 4]
def baseStart_2362181 : Nat := 118140960795 + 2362181 * 2 ^ 59
def prefixEnd_2362181 : Nat := 4983230072969 + 3 ^ 40 * 2362181 * 2
def baseEnd_2362181 : Nat := 1212934245918327689674033

theorem tailTrace_2362181 : CollatzResearch.WordTrace tailWord_2362181 prefixEnd_2362181 1212934245918327689674033 := by
  unfold tailWord_2362181
  simp only [CollatzResearch.WordTrace]
  refine ⟨86155819055229140241334397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57437212703486093494222931 86155819055229140241334397)
  ·
    refine ⟨32308432145710927590500399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86155819055229140241334397 32308432145710927590500399)
    ·
      refine ⟨48462648218566391385750599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32308432145710927590500399 48462648218566391385750599)
      ·
        refine ⟨72693972327849587078625899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48462648218566391385750599 72693972327849587078625899)
        ·
          refine ⟨109040958491774380617938849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72693972327849587078625899 109040958491774380617938849)
          ·
            refine ⟨81780718868830785463454137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109040958491774380617938849 81780718868830785463454137)
            ·
              refine ⟨61335539151623089097590603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81780718868830785463454137 61335539151623089097590603)
              ·
                refine ⟨92003308727434633646385905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61335539151623089097590603 92003308727434633646385905)
                ·
                  refine ⟨69002481545575975234789429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 92003308727434633646385905 69002481545575975234789429)
                  ·
                    refine ⟨6468982644897747678261509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 69002481545575975234789429 6468982644897747678261509)
                    ·
                      refine ⟨1212934245918327689674033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6468982644897747678261509 1212934245918327689674033)
                      ·
                        rfl

theorem cell23_2362181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 5, 4].length) (baseStart_2362181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362181 prefixEnd_2362181 := by exact prefixLift 2362181
  have htrace : WordTrace (prefixWord ++ tailWord_2362181) baseStart_2362181 baseEnd_2362181 := by
    simpa [prefixWord, tailWord_2362181, baseEnd_2362181] using wordTrace_append hprefix tailTrace_2362181
  have hstable : (prefixWord ++ tailWord_2362181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362181).length < 2 ^ (prefixWord ++ tailWord_2362181).sum := by decide
  have hdescent : baseEnd_2362181 < baseStart_2362181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362208 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 6, 4]
def baseStart_2362208 : Nat := 118140960795 + 2362208 * 2 ^ 59
def prefixEnd_2362208 : Nat := 4983230072969 + 3 ^ 40 * 2362208 * 2
def baseEnd_2362208 : Nat := 404316036631999694678803

theorem tailTrace_2362208 : CollatzResearch.WordTrace tailWord_2362208 prefixEnd_2362208 404316036631999694678803 := by
  unfold tailWord_2362208
  simp only [CollatzResearch.WordTrace]
  refine ⟨43078401913065661926283639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57437869217420882568378185 43078401913065661926283639)
  ·
    refine ⟨64617602869598492889425459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43078401913065661926283639 64617602869598492889425459)
    ·
      refine ⟨96926404304397739334138189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64617602869598492889425459 96926404304397739334138189)
      ·
        refine ⟨36347401614149152250301821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96926404304397739334138189 36347401614149152250301821)
        ·
          refine ⟨13630275605305932093863183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36347401614149152250301821 13630275605305932093863183)
          ·
            refine ⟨20445413407958898140794775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13630275605305932093863183 20445413407958898140794775)
            ·
              refine ⟨30668120111938347211192163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20445413407958898140794775 30668120111938347211192163)
              ·
                refine ⟨46002180167907520816788245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30668120111938347211192163 46002180167907520816788245)
                ·
                  refine ⟨2156352195370665038286949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46002180167907520816788245 2156352195370665038286949)
                  ·
                    refine ⟨404316036631999694678803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2156352195370665038286949 404316036631999694678803)
                    ·
                      rfl

theorem cell23_2362208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 6, 4].length) (baseStart_2362208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362208 prefixEnd_2362208 := by exact prefixLift 2362208
  have htrace : WordTrace (prefixWord ++ tailWord_2362208) baseStart_2362208 baseEnd_2362208 := by
    simpa [prefixWord, tailWord_2362208, baseEnd_2362208] using wordTrace_append hprefix tailTrace_2362208
  have hstable : (prefixWord ++ tailWord_2362208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362208).length < 2 ^ (prefixWord ++ tailWord_2362208).sum := by decide
  have hdescent : baseEnd_2362208 < baseStart_2362208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362215 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_2362215 : Nat := 118140960795 + 2362215 * 2 ^ 59
def prefixEnd_2362215 : Nat := 4983230072969 + 3 ^ 40 * 2362215 * 2
def baseEnd_2362215 : Nat := 1212951704260580556648877

theorem tailTrace_2362215 : CollatzResearch.WordTrace tailWord_2362215 prefixEnd_2362215 1212951704260580556648877 := by
  unfold tailWord_2362215
  simp only [CollatzResearch.WordTrace]
  refine ⟨86157059137105964048072099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57438039424737309365381399 86157059137105964048072099)
  ·
    refine ⟨129235588705658946072108149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86157059137105964048072099 129235588705658946072108149)
    ·
      refine ⟨12115836441155526194260139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 129235588705658946072108149 12115836441155526194260139)
      ·
        refine ⟨18173754661733289291390209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12115836441155526194260139 18173754661733289291390209)
        ·
          refine ⟨13630315996299966968542657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18173754661733289291390209 13630315996299966968542657)
          ·
            refine ⟨10222736997224975226406993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13630315996299966968542657 10222736997224975226406993)
            ·
              refine ⟨7667052747918731419805245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10222736997224975226406993 7667052747918731419805245)
              ·
                refine ⟨2875144780469524282426967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7667052747918731419805245 2875144780469524282426967)
                ·
                  refine ⟨4312717170704286423640451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875144780469524282426967 4312717170704286423640451)
                  ·
                    refine ⟨6469075756056429635460677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4312717170704286423640451 6469075756056429635460677)
                    ·
                      refine ⟨1212951704260580556648877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6469075756056429635460677 1212951704260580556648877)
                      ·
                        rfl

theorem cell23_2362215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_2362215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362215 prefixEnd_2362215 := by exact prefixLift 2362215
  have htrace : WordTrace (prefixWord ++ tailWord_2362215) baseStart_2362215 baseEnd_2362215 := by
    simpa [prefixWord, tailWord_2362215, baseEnd_2362215] using wordTrace_append hprefix tailTrace_2362215
  have hstable : (prefixWord ++ tailWord_2362215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362215).length < 2 ^ (prefixWord ++ tailWord_2362215).sum := by decide
  have hdescent : baseEnd_2362215 < baseStart_2362215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362298 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_2362298 : Nat := 118140960795 + 2362298 * 2 ^ 59
def prefixEnd_2362298 : Nat := 4983230072969 + 3 ^ 40 * 2362298 * 2
def baseEnd_2362298 : Nat := 404331441051634577303665

theorem tailTrace_2362298 : CollatzResearch.WordTrace tailWord_2362298 prefixEnd_2362298 404331441051634577303665 := by
  unfold tailWord_2362298
  simp only [CollatzResearch.WordTrace]
  refine ⟨21540021598951317305835887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57440057597203512815562365 21540021598951317305835887)
  ·
    refine ⟨32310032398426975958753831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21540021598951317305835887 32310032398426975958753831)
    ·
      refine ⟨48465048597640463938130747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32310032398426975958753831 48465048597640463938130747)
      ·
        refine ⟨72697572896460695907196121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48465048597640463938130747 72697572896460695907196121)
        ·
          refine ⟨54523179672345521930397091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72697572896460695907196121 54523179672345521930397091)
          ·
            refine ⟨81784769508518282895595637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54523179672345521930397091 81784769508518282895595637)
            ·
              refine ⟨7667322141423589021462091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 81784769508518282895595637 7667322141423589021462091)
              ·
                refine ⟨11500983212135383532193137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7667322141423589021462091 11500983212135383532193137)
                ·
                  refine ⟨8625737409101537649144853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11500983212135383532193137 8625737409101537649144853)
                  ·
                    refine ⟨404331441051634577303665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8625737409101537649144853 404331441051634577303665)
                    ·
                      rfl

theorem cell23_2362298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_2362298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362298 prefixEnd_2362298 := by exact prefixLift 2362298
  have htrace : WordTrace (prefixWord ++ tailWord_2362298) baseStart_2362298 baseEnd_2362298 := by
    simpa [prefixWord, tailWord_2362298, baseEnd_2362298] using wordTrace_append hprefix tailTrace_2362298
  have hstable : (prefixWord ++ tailWord_2362298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362298).length < 2 ^ (prefixWord ++ tailWord_2362298).sum := by decide
  have hdescent : baseEnd_2362298 < baseStart_2362298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362317 : List Nat := [1, 6, 3, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_2362317 : Nat := 118140960795 + 2362317 * 2 ^ 59
def prefixEnd_2362317 : Nat := 4983230072969 + 3 ^ 40 * 2362317 * 2
def baseEnd_2362317 : Nat := 1213004079287339157573409

theorem tailTrace_2362317 : CollatzResearch.WordTrace tailWord_2362317 prefixEnd_2362317 1213004079287339157573409 := by
  unfold tailWord_2362317
  simp only [CollatzResearch.WordTrace]
  refine ⟨86160779382736435468285205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57440519588490956978856803 86160779382736435468285205)
  ·
    refine ⟨4038786533565770412575869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86160779382736435468285205 4038786533565770412575869)
    ·
      refine ⟨1514544950087163904715951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4038786533565770412575869 1514544950087163904715951)
      ·
        refine ⟨2271817425130745857073927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514544950087163904715951 2271817425130745857073927)
        ·
          refine ⟨3407726137696118785610891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271817425130745857073927 3407726137696118785610891)
          ·
            refine ⟨5111589206544178178416337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3407726137696118785610891 5111589206544178178416337)
            ·
              refine ⟨3833691904908133633812253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5111589206544178178416337 3833691904908133633812253)
              ·
                refine ⟨1437634464340550112679595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3833691904908133633812253 1437634464340550112679595)
                ·
                  refine ⟨2156451696510825169019393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437634464340550112679595 2156451696510825169019393)
                  ·
                    refine ⟨1617338772383118876764545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2156451696510825169019393 1617338772383118876764545)
                    ·
                      refine ⟨1213004079287339157573409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617338772383118876764545 1213004079287339157573409)
                      ·
                        rfl

theorem cell23_2362317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_2362317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362317 prefixEnd_2362317 := by exact prefixLift 2362317
  have htrace : WordTrace (prefixWord ++ tailWord_2362317) baseStart_2362317 baseEnd_2362317 := by
    simpa [prefixWord, tailWord_2362317, baseEnd_2362317] using wordTrace_append hprefix tailTrace_2362317
  have hstable : (prefixWord ++ tailWord_2362317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362317).length < 2 ^ (prefixWord ++ tailWord_2362317).sum := by decide
  have hdescent : baseEnd_2362317 < baseStart_2362317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362326 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_2362326 : Nat := 118140960795 + 2362326 * 2 ^ 59
def prefixEnd_2362326 : Nat := 4983230072969 + 3 ^ 40 * 2362326 * 2
def baseEnd_2362326 : Nat := 1213008700613229622360867

theorem tailTrace_2362326 : CollatzResearch.WordTrace tailWord_2362326 prefixEnd_2362326 1213008700613229622360867 := by
  unfold tailWord_2362326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5385069227481489375335177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57440738426469220003575221 5385069227481489375335177)
  ·
    refine ⟨4038801920611117031501383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5385069227481489375335177 4038801920611117031501383)
    ·
      refine ⟨6058202880916675547252075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4038801920611117031501383 6058202880916675547252075)
      ·
        refine ⟨9087304321375013320878113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6058202880916675547252075 9087304321375013320878113)
        ·
          refine ⟨6815478241031259990658585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9087304321375013320878113 6815478241031259990658585)
          ·
            refine ⟨5111608680773444992993939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6815478241031259990658585 5111608680773444992993939)
            ·
              refine ⟨7667413021160167489490909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5111608680773444992993939 7667413021160167489490909)
              ·
                refine ⟨2875279882935062808559091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7667413021160167489490909 2875279882935062808559091)
                ·
                  refine ⟨4312919824402594212838637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875279882935062808559091 4312919824402594212838637)
                  ·
                    refine ⟨1617344934150972829814489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4312919824402594212838637 1617344934150972829814489)
                    ·
                      refine ⟨1213008700613229622360867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617344934150972829814489 1213008700613229622360867)
                      ·
                        rfl

theorem cell23_2362326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_2362326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362326 prefixEnd_2362326 := by exact prefixLift 2362326
  have htrace : WordTrace (prefixWord ++ tailWord_2362326) baseStart_2362326 baseEnd_2362326 := by
    simpa [prefixWord, tailWord_2362326, baseEnd_2362326] using wordTrace_append hprefix tailTrace_2362326
  have hstable : (prefixWord ++ tailWord_2362326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362326).length < 2 ^ (prefixWord ++ tailWord_2362326).sum := by decide
  have hdescent : baseEnd_2362326 < baseStart_2362326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362375 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 2, 5]
def baseStart_2362375 : Nat := 118140960795 + 2362375 * 2 ^ 59
def prefixEnd_2362375 : Nat := 4983230072969 + 3 ^ 40 * 2362375 * 2
def baseEnd_2362375 : Nat := 404344620388433310216047

theorem tailTrace_2362375 : CollatzResearch.WordTrace tailWord_2362375 prefixEnd_2362375 404344620388433310216047 := by
  unfold tailWord_2362375
  simp only [CollatzResearch.WordTrace]
  refine ⟨86162894816526311373896579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57441929877684207582597719 86162894816526311373896579)
  ·
    refine ⟨129244342224789467060844869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86162894816526311373896579 129244342224789467060844869)
    ·
      refine ⟨24233314167148025073908413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129244342224789467060844869 24233314167148025073908413)
      ·
        refine ⟨9087492812680509402715655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24233314167148025073908413 9087492812680509402715655)
        ·
          refine ⟨13631239219020764104073483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9087492812680509402715655 13631239219020764104073483)
          ·
            refine ⟨20446858828531146156110225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13631239219020764104073483 20446858828531146156110225)
            ·
              refine ⟨15335144121398359617082669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20446858828531146156110225 15335144121398359617082669)
              ·
                refine ⟨5750679045524384856406001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15335144121398359617082669 5750679045524384856406001)
                ·
                  refine ⟨4313009284143288642304501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5750679045524384856406001 4313009284143288642304501)
                  ·
                    refine ⟨404344620388433310216047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4313009284143288642304501 404344620388433310216047)
                    ·
                      rfl

theorem cell23_2362375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_2362375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362375 prefixEnd_2362375 := by exact prefixLift 2362375
  have htrace : WordTrace (prefixWord ++ tailWord_2362375) baseStart_2362375 baseEnd_2362375 := by
    simpa [prefixWord, tailWord_2362375, baseEnd_2362375] using wordTrace_append hprefix tailTrace_2362375
  have hstable : (prefixWord ++ tailWord_2362375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362375).length < 2 ^ (prefixWord ++ tailWord_2362375).sum := by decide
  have hdescent : baseEnd_2362375 < baseStart_2362375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362432 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 3]
def baseStart_2362432 : Nat := 118140960795 + 2362432 * 2 ^ 59
def prefixEnd_2362432 : Nat := 4983230072969 + 3 ^ 40 * 2362432 * 2
def baseEnd_2362432 : Nat := 1213063129562606207635379

theorem tailTrace_2362432 : CollatzResearch.WordTrace tailWord_2362432 prefixEnd_2362432 1213063129562606207635379 := by
  unfold tailWord_2362432
  simp only [CollatzResearch.WordTrace]
  refine ⟨43082486888659905054360775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57443315851546540072481033 43082486888659905054360775)
  ·
    refine ⟨64623730332989857581541163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43082486888659905054360775 64623730332989857581541163)
    ·
      refine ⟨96935595499484786372311745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64623730332989857581541163 96935595499484786372311745)
      ·
        refine ⟨72701696624613589779233809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96935595499484786372311745 72701696624613589779233809)
        ·
          refine ⟨54526272468460192334425357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72701696624613589779233809 54526272468460192334425357)
          ·
            refine ⟨20447352175672572125409509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54526272468460192334425357 20447352175672572125409509)
            ·
              refine ⟨3833878532938607273514283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20447352175672572125409509 3833878532938607273514283)
              ·
                refine ⟨5750817799407910910271425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3833878532938607273514283 5750817799407910910271425)
                ·
                  refine ⟨4313113349555933182703569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5750817799407910910271425 4313113349555933182703569)
                  ·
                    refine ⟨3234835012166949887027677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4313113349555933182703569 3234835012166949887027677)
                    ·
                      refine ⟨1213063129562606207635379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3234835012166949887027677 1213063129562606207635379)
                      ·
                        rfl

theorem cell23_2362432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_2362432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362432 prefixEnd_2362432 := by exact prefixLift 2362432
  have htrace : WordTrace (prefixWord ++ tailWord_2362432) baseStart_2362432 baseEnd_2362432 := by
    simpa [prefixWord, tailWord_2362432, baseEnd_2362432] using wordTrace_append hprefix tailTrace_2362432
  have hstable : (prefixWord ++ tailWord_2362432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362432).length < 2 ^ (prefixWord ++ tailWord_2362432).sum := by decide
  have hdescent : baseEnd_2362432 < baseStart_2362432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362465 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 3, 5]
def baseStart_2362465 : Nat := 118140960795 + 2362465 * 2 ^ 59
def prefixEnd_2362465 : Nat := 4983230072969 + 3 ^ 40 * 2362465 * 2
def baseEnd_2362465 : Nat := 404360024808068192840909

theorem tailTrace_2362465 : CollatzResearch.WordTrace tailWord_2362465 prefixEnd_2362465 404360024808068192840909 := by
  unfold tailWord_2362465
  simp only [CollatzResearch.WordTrace]
  refine ⟨86166177386200256744672849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57444118257466837829781899 86166177386200256744672849)
  ·
    refine ⟨64624633039650192558504637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86166177386200256744672849 64624633039650192558504637)
    ·
      refine ⟨24234237389868822209439239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64624633039650192558504637 24234237389868822209439239)
      ·
        refine ⟨36351356084803233314158859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24234237389868822209439239 36351356084803233314158859)
        ·
          refine ⟨54527034127204849971238289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36351356084803233314158859 54527034127204849971238289)
          ·
            refine ⟨40895275595403637478428717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54527034127204849971238289 40895275595403637478428717)
            ·
              refine ⟨15335728348276364054410769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40895275595403637478428717 15335728348276364054410769)
              ·
                refine ⟨11501796261207273040808077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15335728348276364054410769 11501796261207273040808077)
                ·
                  refine ⟨4313173597952727390303029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11501796261207273040808077 4313173597952727390303029)
                  ·
                    refine ⟨404360024808068192840909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4313173597952727390303029 404360024808068192840909)
                    ·
                      rfl

theorem cell23_2362465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_2362465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362465 prefixEnd_2362465 := by exact prefixLift 2362465
  have htrace : WordTrace (prefixWord ++ tailWord_2362465) baseStart_2362465 baseEnd_2362465 := by
    simpa [prefixWord, tailWord_2362465, baseEnd_2362465] using wordTrace_append hprefix tailTrace_2362465
  have hstable : (prefixWord ++ tailWord_2362465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362465).length < 2 ^ (prefixWord ++ tailWord_2362465).sum := by decide
  have hdescent : baseEnd_2362465 < baseStart_2362465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362482 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_2362482 : Nat := 118140960795 + 2362482 * 2 ^ 59
def prefixEnd_2362482 : Nat := 4983230072969 + 3 ^ 40 * 2362482 * 2
def baseEnd_2362482 : Nat := 404362934531777004003383

theorem tailTrace_2362482 : CollatzResearch.WordTrace tailWord_2362482 prefixEnd_2362482 404362934531777004003383 := by
  unfold tailWord_2362482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21541699356784667162010425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57444531618092445765361133 21541699356784667162010425)
  ·
    refine ⟨16156274517588500371507819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21541699356784667162010425 16156274517588500371507819)
    ·
      refine ⟨24234411776382750557261729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16156274517588500371507819 24234411776382750557261729)
      ·
        refine ⟨18175808832287062917946297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24234411776382750557261729 18175808832287062917946297)
        ·
          refine ⟨13631856624215297188459723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18175808832287062917946297 13631856624215297188459723)
          ·
            refine ⟨20447784936322945782689585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13631856624215297188459723 20447784936322945782689585)
            ·
              refine ⟨15335838702242209337017189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20447784936322945782689585 15335838702242209337017189)
              ·
                refine ⟨2875469756670414250690723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15335838702242209337017189 2875469756670414250690723)
                ·
                  refine ⟨4313204635005621376036085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875469756670414250690723 4313204635005621376036085)
                  ·
                    refine ⟨404362934531777004003383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4313204635005621376036085 404362934531777004003383)
                    ·
                      rfl

theorem cell23_2362482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_2362482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362482 prefixEnd_2362482 := by exact prefixLift 2362482
  have htrace : WordTrace (prefixWord ++ tailWord_2362482) baseStart_2362482 baseEnd_2362482 := by
    simpa [prefixWord, tailWord_2362482, baseEnd_2362482] using wordTrace_append hprefix tailTrace_2362482
  have hstable : (prefixWord ++ tailWord_2362482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362482).length < 2 ^ (prefixWord ++ tailWord_2362482).sum := by decide
  have hdescent : baseEnd_2362482 < baseStart_2362482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362489 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 1, 5, 2]
def baseStart_2362489 : Nat := 118140960795 + 2362489 * 2 ^ 59
def prefixEnd_2362489 : Nat := 4983230072969 + 3 ^ 40 * 2362489 * 2
def baseEnd_2362489 : Nat := 1213092397959912484622617

theorem tailTrace_2362489 : CollatzResearch.WordTrace tailWord_2362489 prefixEnd_2362489 1213092397959912484622617 := by
  unfold tailWord_2362489
  simp only [CollatzResearch.WordTrace]
  refine ⟨86167052738113308843546521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57444701825408872562364347 86167052738113308843546521)
  ·
    refine ⟨64625289553584981632659891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86167052738113308843546521 64625289553584981632659891)
    ·
      refine ⟨96937934330377472448989837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64625289553584981632659891 96937934330377472448989837)
      ·
        refine ⟨36351725373891552168371189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96937934330377472448989837 36351725373891552168371189)
        ·
          refine ⟨3407974253802333015784799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36351725373891552168371189 3407974253802333015784799)
          ·
            refine ⟨5111961380703499523677199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3407974253802333015784799 5111961380703499523677199)
            ·
              refine ⟨7667942071055249285515799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5111961380703499523677199 7667942071055249285515799)
              ·
                refine ⟨11501913106582873928273699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7667942071055249285515799 11501913106582873928273699)
                ·
                  refine ⟨17252869659874310892410549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11501913106582873928273699 17252869659874310892410549)
                  ·
                    refine ⟨1617456530613216646163489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17252869659874310892410549 1617456530613216646163489)
                    ·
                      refine ⟨1213092397959912484622617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617456530613216646163489 1213092397959912484622617)
                      ·
                        rfl

theorem cell23_2362489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_2362489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362489 prefixEnd_2362489 := by exact prefixLift 2362489
  have htrace : WordTrace (prefixWord ++ tailWord_2362489) baseStart_2362489 baseEnd_2362489 := by
    simpa [prefixWord, tailWord_2362489, baseEnd_2362489] using wordTrace_append hprefix tailTrace_2362489
  have hstable : (prefixWord ++ tailWord_2362489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362489).length < 2 ^ (prefixWord ++ tailWord_2362489).sum := by decide
  have hdescent : baseEnd_2362489 < baseStart_2362489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362512 : List Nat := [2, 1, 1, 1, 1, 1, 4, 6, 2, 4]
def baseStart_2362512 : Nat := 118140960795 + 2362512 * 2 ^ 59
def prefixEnd_2362512 : Nat := 4983230072969 + 3 ^ 40 * 2362512 * 2
def baseEnd_2362512 : Nat := 404368069338321964878337

theorem tailTrace_2362512 : CollatzResearch.WordTrace tailWord_2362512 prefixEnd_2362512 404368069338321964878337 := by
  unfold tailWord_2362512
  simp only [CollatzResearch.WordTrace]
  refine ⟨43083945808514991885816895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57445261078019989181089193 43083945808514991885816895)
  ·
    refine ⟨64625918712772487828725343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43083945808514991885816895 64625918712772487828725343)
    ·
      refine ⟨96938878069158731743088015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64625918712772487828725343 96938878069158731743088015)
      ·
        refine ⟨145408317103738097614632023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96938878069158731743088015 145408317103738097614632023)
        ·
          refine ⟨218112475655607146421948035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145408317103738097614632023 218112475655607146421948035)
          ·
            refine ⟨327168713483410719632922053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218112475655607146421948035 327168713483410719632922053)
            ·
              refine ⟨61344133778139509931172885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 327168713483410719632922053 61344133778139509931172885)
              ·
                refine ⟨2875506270850289528023729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61344133778139509931172885 2875506270850289528023729)
                ·
                  refine ⟨2156629703137717146017797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2875506270850289528023729 2156629703137717146017797)
                  ·
                    refine ⟨404368069338321964878337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2156629703137717146017797 404368069338321964878337)
                    ·
                      rfl

theorem cell23_2362512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 6, 2, 4].length) (baseStart_2362512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362512 prefixEnd_2362512 := by exact prefixLift 2362512
  have htrace : WordTrace (prefixWord ++ tailWord_2362512) baseStart_2362512 baseEnd_2362512 := by
    simpa [prefixWord, tailWord_2362512, baseEnd_2362512] using wordTrace_append hprefix tailTrace_2362512
  have hstable : (prefixWord ++ tailWord_2362512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362512).length < 2 ^ (prefixWord ++ tailWord_2362512).sum := by decide
  have hdescent : baseEnd_2362512 < baseStart_2362512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362515 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 4]
def baseStart_2362515 : Nat := 118140960795 + 2362515 * 2 ^ 59
def prefixEnd_2362515 : Nat := 4983230072969 + 3 ^ 40 * 2362515 * 2
def baseEnd_2362515 : Nat := 1213105748456929382897497

theorem tailTrace_2362515 : CollatzResearch.WordTrace tailWord_2362515 prefixEnd_2362515 1213105748456929382897497 := by
  unfold tailWord_2362515
  simp only [CollatzResearch.WordTrace]
  refine ⟨86168001036019115283992999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57445334024012743522661999 86168001036019115283992999)
  ·
    refine ⟨129252001554028672925989499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86168001036019115283992999 129252001554028672925989499)
    ·
      refine ⟨193878002331043009388984249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129252001554028672925989499 193878002331043009388984249)
      ·
        refine ⟨145408501748282257041738187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193878002331043009388984249 145408501748282257041738187)
        ·
          refine ⟨218112752622423385562607281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145408501748282257041738187 218112752622423385562607281)
          ·
            refine ⟨163584564466817539171955461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218112752622423385562607281 163584564466817539171955461)
            ·
              refine ⟨30672105837528288594741649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163584564466817539171955461 30672105837528288594741649)
              ·
                refine ⟨23004079378146216446056237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30672105837528288594741649 23004079378146216446056237)
                ·
                  refine ⟨8626529766804831167271089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23004079378146216446056237 8626529766804831167271089)
                  ·
                    refine ⟨6469897325103623375453317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8626529766804831167271089 6469897325103623375453317)
                    ·
                      refine ⟨1213105748456929382897497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6469897325103623375453317 1213105748456929382897497)
                      ·
                        rfl

theorem cell23_2362515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2, 4].length) (baseStart_2362515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362515 prefixEnd_2362515 := by exact prefixLift 2362515
  have htrace : WordTrace (prefixWord ++ tailWord_2362515) baseStart_2362515 baseEnd_2362515 := by
    simpa [prefixWord, tailWord_2362515, baseEnd_2362515] using wordTrace_append hprefix tailTrace_2362515
  have hstable : (prefixWord ++ tailWord_2362515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362515).length < 2 ^ (prefixWord ++ tailWord_2362515).sum := by decide
  have hdescent : baseEnd_2362515 < baseStart_2362515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362522 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2362522 : Nat := 118140960795 + 2362522 * 2 ^ 59
def prefixEnd_2362522 : Nat := 4983230072969 + 3 ^ 40 * 2362522 * 2
def baseEnd_2362522 : Nat := 1213109342821510855509965

theorem tailTrace_2362522 : CollatzResearch.WordTrace tailWord_2362522 prefixEnd_2362522 1213109342821510855509965 := by
  unfold tailWord_2362522
  simp only [CollatzResearch.WordTrace]
  refine ⟨21542064086748438869874455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57445504231329170319665213 21542064086748438869874455)
  ·
    refine ⟨32313096130122658304811683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21542064086748438869874455 32313096130122658304811683)
    ·
      refine ⟨48469644195183987457217525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32313096130122658304811683 48469644195183987457217525)
      ·
        refine ⟨4544029143298498824114143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48469644195183987457217525 4544029143298498824114143)
        ·
          refine ⟨6816043714947748236171215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4544029143298498824114143 6816043714947748236171215)
          ·
            refine ⟨10224065572421622354256823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6816043714947748236171215 10224065572421622354256823)
            ·
              refine ⟨15336098358632433531385235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10224065572421622354256823 15336098358632433531385235)
              ·
                refine ⟨23004147537948650297077853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15336098358632433531385235 23004147537948650297077853)
                ·
                  refine ⟨8626555326730743861404195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23004147537948650297077853 8626555326730743861404195)
                  ·
                    refine ⟨12939832990096115792106293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8626555326730743861404195 12939832990096115792106293)
                    ·
                      refine ⟨1213109342821510855509965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12939832990096115792106293 1213109342821510855509965)
                      ·
                        rfl

theorem cell23_2362522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2362522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362522 prefixEnd_2362522 := by exact prefixLift 2362522
  have htrace : WordTrace (prefixWord ++ tailWord_2362522) baseStart_2362522 baseEnd_2362522 := by
    simpa [prefixWord, tailWord_2362522, baseEnd_2362522] using wordTrace_append hprefix tailTrace_2362522
  have hstable : (prefixWord ++ tailWord_2362522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362522).length < 2 ^ (prefixWord ++ tailWord_2362522).sum := by decide
  have hdescent : baseEnd_2362522 < baseStart_2362522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362525 : List Nat := [1, 4, 2, 1, 1, 2, 2, 10]
def baseStart_2362525 : Nat := 118140960795 + 2362525 * 2 ^ 59
def prefixEnd_2362525 : Nat := 4983230072969 + 3 ^ 40 * 2362525 * 2
def baseEnd_2362525 : Nat := 44930032713462012732313

theorem tailTrace_2362525 : CollatzResearch.WordTrace tailWord_2362525 prefixEnd_2362525 44930032713462012732313 := by
  unfold tailWord_2362525
  simp only [CollatzResearch.WordTrace]
  refine ⟨86168365765982886991857029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57445577177321924661238019 86168365765982886991857029)
  ·
    refine ⟨16156568581121791310973193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86168365765982886991857029 16156568581121791310973193)
    ·
      refine ⟨12117426435841343483229895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16156568581121791310973193 12117426435841343483229895)
      ·
        refine ⟨18176139653762015224844843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12117426435841343483229895 18176139653762015224844843)
        ·
          refine ⟨27264209480643022837267265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18176139653762015224844843 27264209480643022837267265)
          ·
            refine ⟨20448157110482267127950449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27264209480643022837267265 20448157110482267127950449)
            ·
              refine ⟨15336117832861700345962837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20448157110482267127950449 15336117832861700345962837)
              ·
                refine ⟨44930032713462012732313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15336117832861700345962837 44930032713462012732313)
                ·
                  rfl

theorem cell23_2362525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 10].length) (baseStart_2362525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362525 prefixEnd_2362525 := by exact prefixLift 2362525
  have htrace : WordTrace (prefixWord ++ tailWord_2362525) baseStart_2362525 baseEnd_2362525 := by
    simpa [prefixWord, tailWord_2362525, baseEnd_2362525] using wordTrace_append hprefix tailTrace_2362525
  have hstable : (prefixWord ++ tailWord_2362525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362525).length < 2 ^ (prefixWord ++ tailWord_2362525).sum := by decide
  have hdescent : baseEnd_2362525 < baseStart_2362525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362532 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_2362532 : Nat := 118140960795 + 2362532 * 2 ^ 59
def prefixEnd_2362532 : Nat := 4983230072969 + 3 ^ 40 * 2362532 * 2
def baseEnd_2362532 : Nat := 1213114477628055816384919

theorem tailTrace_2362532 : CollatzResearch.WordTrace tailWord_2362532 prefixEnd_2362532 1213114477628055816384919 := by
  unfold tailWord_2362532
  simp only [CollatzResearch.WordTrace]
  refine ⟨43084310538478763593680925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57445747384638351458241233 43084310538478763593680925)
  ·
    refine ⟨16156616451929536347630347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43084310538478763593680925 16156616451929536347630347)
    ·
      refine ⟨24234924677894304521445521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16156616451929536347630347 24234924677894304521445521)
      ·
        refine ⟨18176193508420728391084141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24234924677894304521445521 18176193508420728391084141)
        ·
          refine ⟨6816072565657773146656553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18176193508420728391084141 6816072565657773146656553)
          ·
            refine ⟨5112054424243329859992415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6816072565657773146656553 5112054424243329859992415)
            ·
              refine ⟨7668081636364994789988623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112054424243329859992415 7668081636364994789988623)
              ·
                refine ⟨11502122454547492184982935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7668081636364994789988623 11502122454547492184982935)
                ·
                  refine ⟨17253183681821238277474403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11502122454547492184982935 17253183681821238277474403)
                  ·
                    refine ⟨25879775522731857416211605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17253183681821238277474403 25879775522731857416211605)
                    ·
                      refine ⟨1213114477628055816384919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25879775522731857416211605 1213114477628055816384919)
                      ·
                        rfl

theorem cell23_2362532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_2362532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362532 prefixEnd_2362532 := by exact prefixLift 2362532
  have htrace : WordTrace (prefixWord ++ tailWord_2362532) baseStart_2362532 baseEnd_2362532 := by
    simpa [prefixWord, tailWord_2362532, baseEnd_2362532] using wordTrace_append hprefix tailTrace_2362532
  have hstable : (prefixWord ++ tailWord_2362532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362532).length < 2 ^ (prefixWord ++ tailWord_2362532).sum := by decide
  have hdescent : baseEnd_2362532 < baseStart_2362532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362553 : List Nat := [1, 2, 1, 4, 1, 3, 3, 3, 1, 2, 2]
def baseStart_2362553 : Nat := 118140960795 + 2362553 * 2 ^ 59
def prefixEnd_2362553 : Nat := 4983230072969 + 3 ^ 40 * 2362553 * 2
def baseEnd_2362553 : Nat := 1213125260721800234222323

theorem tailTrace_2362553 : CollatzResearch.WordTrace tailWord_2362553 prefixEnd_2362553 1213125260721800234222323 := by
  unfold tailWord_2362553
  simp only [CollatzResearch.WordTrace]
  refine ⟨86169387009881447773876313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57446258006587631849250875 86169387009881447773876313)
  ·
    refine ⟨64627040257411085830407235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86169387009881447773876313 64627040257411085830407235)
    ·
      refine ⟨96940560386116628745610853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64627040257411085830407235 96940560386116628745610853)
      ·
        refine ⟨18176355072396867889802035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96940560386116628745610853 18176355072396867889802035)
        ·
          refine ⟨27264532608595301834703053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18176355072396867889802035 27264532608595301834703053)
          ·
            refine ⟨10224199728223238188013645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27264532608595301834703053 10224199728223238188013645)
            ·
              refine ⟨3834074898083714320505117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10224199728223238188013645 3834074898083714320505117)
              ·
                refine ⟨1437778086781392870189419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3834074898083714320505117 1437778086781392870189419)
                ·
                  refine ⟨2156667130172089305284129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437778086781392870189419 2156667130172089305284129)
                  ·
                    refine ⟨1617500347629066978963097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2156667130172089305284129 1617500347629066978963097)
                    ·
                      refine ⟨1213125260721800234222323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617500347629066978963097 1213125260721800234222323)
                      ·
                        rfl

theorem cell23_2362553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_2362553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362553 prefixEnd_2362553 := by exact prefixLift 2362553
  have htrace : WordTrace (prefixWord ++ tailWord_2362553) baseStart_2362553 baseEnd_2362553 := by
    simpa [prefixWord, tailWord_2362553, baseEnd_2362553] using wordTrace_append hprefix tailTrace_2362553
  have hstable : (prefixWord ++ tailWord_2362553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362553).length < 2 ^ (prefixWord ++ tailWord_2362553).sum := by decide
  have hdescent : baseEnd_2362553 < baseStart_2362553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362565 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 5]
def baseStart_2362565 : Nat := 118140960795 + 2362565 * 2 ^ 59
def prefixEnd_2362565 : Nat := 4983230072969 + 3 ^ 40 * 2362565 * 2
def baseEnd_2362565 : Nat := 1213131422489654187272267

theorem tailTrace_2362565 : CollatzResearch.WordTrace tailWord_2362565 prefixEnd_2362565 1213131422489654187272267 := by
  unfold tailWord_2362565
  simp only [CollatzResearch.WordTrace]
  refine ⟨86169824685837973823313149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57446549790558649215542099 86169824685837973823313149)
  ·
    refine ⟨32313684257189240183742431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86169824685837973823313149 32313684257189240183742431)
    ·
      refine ⟨48470526385783860275613647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32313684257189240183742431 48470526385783860275613647)
      ·
        refine ⟨72705789578675790413420471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48470526385783860275613647 72705789578675790413420471)
        ·
          refine ⟨109058684368013685620130707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72705789578675790413420471 109058684368013685620130707)
          ·
            refine ⟨163588026552020528430196061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109058684368013685620130707 163588026552020528430196061)
            ·
              refine ⟨61345509957007698161323523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163588026552020528430196061 61345509957007698161323523)
              ·
                refine ⟨92018264935511547241985285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61345509957007698161323523 92018264935511547241985285)
                ·
                  refine ⟨17253424675408415107872241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92018264935511547241985285 17253424675408415107872241)
                  ·
                    refine ⟨12940068506556311330904181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17253424675408415107872241 12940068506556311330904181)
                    ·
                      refine ⟨1213131422489654187272267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12940068506556311330904181 1213131422489654187272267)
                      ·
                        rfl

theorem cell23_2362565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_2362565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362565 prefixEnd_2362565 := by exact prefixLift 2362565
  have htrace : WordTrace (prefixWord ++ tailWord_2362565) baseStart_2362565 baseEnd_2362565 := by
    simpa [prefixWord, tailWord_2362565, baseEnd_2362565] using wordTrace_append hprefix tailTrace_2362565
  have hstable : (prefixWord ++ tailWord_2362565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362565).length < 2 ^ (prefixWord ++ tailWord_2362565).sum := by decide
  have hdescent : baseEnd_2362565 < baseStart_2362565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362570 : List Nat := [3, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2]
def baseStart_2362570 : Nat := 118140960795 + 2362570 * 2 ^ 59
def prefixEnd_2362570 : Nat := 4983230072969 + 3 ^ 40 * 2362570 * 2
def baseEnd_2362570 : Nat := 1213133989892926667709745

theorem tailTrace_2362570 : CollatzResearch.WordTrace tailWord_2362570 prefixEnd_2362570 1213133989892926667709745 := by
  unfold tailWord_2362570
  simp only [CollatzResearch.WordTrace]
  refine ⟨21542501762704964919311291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57446671367213239784830109 21542501762704964919311291)
  ·
    refine ⟨32313752644057447378966937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21542501762704964919311291 32313752644057447378966937)
    ·
      refine ⟨24235314483043085534225203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32313752644057447378966937 24235314483043085534225203)
      ·
        refine ⟨36352971724564628301337805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24235314483043085534225203 36352971724564628301337805)
        ·
          refine ⟨13632364396711735613001677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36352971724564628301337805 13632364396711735613001677)
          ·
            refine ⟨5112136648766900854875629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13632364396711735613001677 5112136648766900854875629)
            ·
              refine ⟨1917051243287587820578361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5112136648766900854875629 1917051243287587820578361)
              ·
                refine ⟨1437788432465690865433771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1917051243287587820578361 1437788432465690865433771)
                ·
                  refine ⟨2156682648698536298150657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437788432465690865433771 2156682648698536298150657)
                  ·
                    refine ⟨1617511986523902223612993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2156682648698536298150657 1617511986523902223612993)
                    ·
                      refine ⟨1213133989892926667709745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617511986523902223612993 1213133989892926667709745)
                      ·
                        rfl

theorem cell23_2362570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_2362570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362570 prefixEnd_2362570 := by exact prefixLift 2362570
  have htrace : WordTrace (prefixWord ++ tailWord_2362570) baseStart_2362570 baseEnd_2362570 := by
    simpa [prefixWord, tailWord_2362570, baseEnd_2362570] using wordTrace_append hprefix tailTrace_2362570
  have hstable : (prefixWord ++ tailWord_2362570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362570).length < 2 ^ (prefixWord ++ tailWord_2362570).sum := by decide
  have hdescent : baseEnd_2362570 < baseStart_2362570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362580 : List Nat := [2, 4, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_2362580 : Nat := 118140960795 + 2362580 * 2 ^ 59
def prefixEnd_2362580 : Nat := 4983230072969 + 3 ^ 40 * 2362580 * 2
def baseEnd_2362580 : Nat := 404379708233157209528233

theorem tailTrace_2362580 : CollatzResearch.WordTrace tailWord_2362580 prefixEnd_2362580 404379708233157209528233 := by
  unfold tailWord_2362580
  simp only [CollatzResearch.WordTrace]
  refine ⟨43085185890391815692554597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57446914520522420923406129 43085185890391815692554597)
  ·
    refine ⟨8078472354448465442353987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43085185890391815692554597 8078472354448465442353987)
    ·
      refine ⟨12117708531672698163530981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8078472354448465442353987 12117708531672698163530981)
      ·
        refine ⟨2272070349688630905662059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12117708531672698163530981 2272070349688630905662059)
        ·
          refine ⟨3408105524532946358493089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272070349688630905662059 3408105524532946358493089)
          ·
            refine ⟨2556079143399709768869817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408105524532946358493089 2556079143399709768869817)
            ·
              refine ⟨1917059357549782326652363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2556079143399709768869817 1917059357549782326652363)
              ·
                refine ⟨2875589036324673489978545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917059357549782326652363 2875589036324673489978545)
                ·
                  refine ⟨2156691777243505117483909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2875589036324673489978545 2156691777243505117483909)
                  ·
                    refine ⟨404379708233157209528233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2156691777243505117483909 404379708233157209528233)
                    ·
                      rfl

theorem cell23_2362580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_2362580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362580 prefixEnd_2362580 := by exact prefixLift 2362580
  have htrace : WordTrace (prefixWord ++ tailWord_2362580) baseStart_2362580 baseEnd_2362580 := by
    simpa [prefixWord, tailWord_2362580, baseEnd_2362580] using wordTrace_append hprefix tailTrace_2362580
  have hstable : (prefixWord ++ tailWord_2362580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362580).length < 2 ^ (prefixWord ++ tailWord_2362580).sum := by decide
  have hdescent : baseEnd_2362580 < baseStart_2362580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362585 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 1, 8]
def baseStart_2362585 : Nat := 118140960795 + 2362585 * 2 ^ 59
def prefixEnd_2362585 : Nat := 4983230072969 + 3 ^ 40 * 2362585 * 2
def baseEnd_2362585 : Nat := 404380564034248036340725

theorem tailTrace_2362585 : CollatzResearch.WordTrace tailWord_2362585 prefixEnd_2362585 404380564034248036340725 := by
  unfold tailWord_2362585
  simp only [CollatzResearch.WordTrace]
  refine ⟨86170554145765517239041209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57447036097177011492694139 86170554145765517239041209)
  ·
    refine ⟨64627915609324137929280907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86170554145765517239041209 64627915609324137929280907)
    ·
      refine ⟨96941873413986206893921361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64627915609324137929280907 96941873413986206893921361)
      ·
        refine ⟨72706405060489655170441021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96941873413986206893921361 72706405060489655170441021)
        ·
          refine ⟨27264901897683620688915383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72706405060489655170441021 27264901897683620688915383)
          ·
            refine ⟨40897352846525431033373075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27264901897683620688915383 40897352846525431033373075)
            ·
              refine ⟨61346029269788146550059613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40897352846525431033373075 61346029269788146550059613)
              ·
                refine ⟨23004760976170554956272355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61346029269788146550059613 23004760976170554956272355)
                ·
                  refine ⟨34507141464255832434408533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23004760976170554956272355 34507141464255832434408533)
                  ·
                    refine ⟨404380564034248036340725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34507141464255832434408533 404380564034248036340725)
                    ·
                      rfl

theorem cell23_2362585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 8].length) (baseStart_2362585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362585 prefixEnd_2362585 := by exact prefixLift 2362585
  have htrace : WordTrace (prefixWord ++ tailWord_2362585) baseStart_2362585 baseEnd_2362585 := by
    simpa [prefixWord, tailWord_2362585, baseEnd_2362585] using wordTrace_append hprefix tailTrace_2362585
  have hstable : (prefixWord ++ tailWord_2362585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362585).length < 2 ^ (prefixWord ++ tailWord_2362585).sum := by decide
  have hdescent : baseEnd_2362585 < baseStart_2362585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362596 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 1, 3, 2]
def baseStart_2362596 : Nat := 118140960795 + 2362596 * 2 ^ 59
def prefixEnd_2362596 : Nat := 4983230072969 + 3 ^ 40 * 2362596 * 2
def baseEnd_2362596 : Nat := 1213147340389943565984625

theorem tailTrace_2362596 : CollatzResearch.WordTrace tailWord_2362596 prefixEnd_2362596 1213147340389943565984625 := by
  unfold tailWord_2362596
  simp only [CollatzResearch.WordTrace]
  refine ⟨43085477674362833058845821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57447303565817110745127761 43085477674362833058845821)
  ·
    refine ⟨16157054127886062397067183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43085477674362833058845821 16157054127886062397067183)
    ·
      refine ⟨24235581191829093595600775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16157054127886062397067183 24235581191829093595600775)
      ·
        refine ⟨36353371787743640393401163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24235581191829093595600775 36353371787743640393401163)
        ·
          refine ⟨54530057681615460590101745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36353371787743640393401163 54530057681615460590101745)
          ·
            refine ⟨40897543261211595442576309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54530057681615460590101745 40897543261211595442576309)
            ·
              refine ⟨3834144680738587072741529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40897543261211595442576309 3834144680738587072741529)
              ·
                refine ⟨2875608510553940304556147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3834144680738587072741529 2875608510553940304556147)
                ·
                  refine ⟨4313412765830910456834221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2875608510553940304556147 4313412765830910456834221)
                  ·
                    refine ⟨1617529787186591421312833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4313412765830910456834221 1617529787186591421312833)
                    ·
                      refine ⟨1213147340389943565984625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617529787186591421312833 1213147340389943565984625)
                      ·
                        rfl

theorem cell23_2362596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_2362596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362596 prefixEnd_2362596 := by exact prefixLift 2362596
  have htrace : WordTrace (prefixWord ++ tailWord_2362596) baseStart_2362596 baseEnd_2362596 := by
    simpa [prefixWord, tailWord_2362596, baseEnd_2362596] using wordTrace_append hprefix tailTrace_2362596
  have hstable : (prefixWord ++ tailWord_2362596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362596).length < 2 ^ (prefixWord ++ tailWord_2362596).sum := by decide
  have hdescent : baseEnd_2362596 < baseStart_2362596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362615 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 9]
def baseStart_2362615 : Nat := 118140960795 + 2362615 * 2 ^ 59
def prefixEnd_2362615 : Nat := 4983230072969 + 3 ^ 40 * 2362615 * 2
def baseEnd_2362615 : Nat := 134795232946930999071893

theorem tailTrace_2362615 : CollatzResearch.WordTrace tailWord_2362615 prefixEnd_2362615 134795232946930999071893 := by
  unfold tailWord_2362615
  simp only [CollatzResearch.WordTrace]
  refine ⟨86171648335656832362633299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57447765557104554908422199 86171648335656832362633299)
  ·
    refine ⟨129257472503485248543949949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86171648335656832362633299 129257472503485248543949949)
    ·
      refine ⟨48471552188806968203981231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129257472503485248543949949 48471552188806968203981231)
      ·
        refine ⟨72707328283210452305971847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48471552188806968203981231 72707328283210452305971847)
        ·
          refine ⟨109060992424815678458957771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72707328283210452305971847 109060992424815678458957771)
          ·
            refine ⟨163591488637223517688436657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109060992424815678458957771 163591488637223517688436657)
            ·
              refine ⟨122693616477917638266327493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163591488637223517688436657 122693616477917638266327493)
              ·
                refine ⟨23005053089609557174936405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122693616477917638266327493 23005053089609557174936405)
                ·
                  refine ⟨134795232946930999071893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23005053089609557174936405 134795232946930999071893)
                  ·
                    rfl

theorem cell23_2362615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 9].length) (baseStart_2362615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362615 prefixEnd_2362615 := by exact prefixLift 2362615
  have htrace : WordTrace (prefixWord ++ tailWord_2362615) baseStart_2362615 baseEnd_2362615 := by
    simpa [prefixWord, tailWord_2362615, baseEnd_2362615] using wordTrace_append hprefix tailTrace_2362615
  have hstable : (prefixWord ++ tailWord_2362615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362615).length < 2 ^ (prefixWord ++ tailWord_2362615).sum := by decide
  have hdescent : baseEnd_2362615 < baseStart_2362615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362666 : List Nat := [3, 1, 4, 2, 1, 1, 1, 5, 5]
def baseStart_2362666 : Nat := 118140960795 + 2362666 * 2 ^ 59
def prefixEnd_2362666 : Nat := 4983230072969 + 3 ^ 40 * 2362666 * 2
def baseEnd_2362666 : Nat := 134798142670639810234367

theorem tailTrace_2362666 : CollatzResearch.WordTrace tailWord_2362666 prefixEnd_2362666 134798142670639810234367 := by
  unfold tailWord_2362666
  simp only [CollatzResearch.WordTrace]
  refine ⟨21543377114618017018184963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57449005638981378715159901 21543377114618017018184963)
  ·
    refine ⟨32315065671927025527277445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21543377114618017018184963 32315065671927025527277445)
    ·
      refine ⟨6059074813486317286364521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32315065671927025527277445 6059074813486317286364521)
      ·
        refine ⟨4544306110114737964773391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6059074813486317286364521 4544306110114737964773391)
        ·
          refine ⟨6816459165172106947160087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4544306110114737964773391 6816459165172106947160087)
          ·
            refine ⟨10224688747758160420740131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6816459165172106947160087 10224688747758160420740131)
            ·
              refine ⟨15337033121637240631110197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10224688747758160420740131 15337033121637240631110197)
              ·
                refine ⟨1437846855153491309166581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15337033121637240631110197 1437846855153491309166581)
                ·
                  refine ⟨134798142670639810234367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1437846855153491309166581 134798142670639810234367)
                  ·
                    rfl

theorem cell23_2362666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_2362666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362666 prefixEnd_2362666 := by exact prefixLift 2362666
  have htrace : WordTrace (prefixWord ++ tailWord_2362666) baseStart_2362666 baseEnd_2362666 := by
    simpa [prefixWord, tailWord_2362666, baseEnd_2362666] using wordTrace_append hprefix tailTrace_2362666
  have hstable : (prefixWord ++ tailWord_2362666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362666).length < 2 ^ (prefixWord ++ tailWord_2362666).sum := by decide
  have hdescent : baseEnd_2362666 < baseStart_2362666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362694 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2362694 : Nat := 118140960795 + 2362694 * 2 ^ 59
def prefixEnd_2362694 : Nat := 4983230072969 + 3 ^ 40 * 2362694 * 2
def baseEnd_2362694 : Nat := 1213197661494084182559175

theorem tailTrace_2362694 : CollatzResearch.WordTrace tailWord_2362694 prefixEnd_2362694 1213197661494084182559175 := by
  unfold tailWord_2362694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2692954053199082151711223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57449686468247085903172757 2692954053199082151711223)
  ·
    refine ⟨4039431079798623227566835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2692954053199082151711223 4039431079798623227566835)
    ·
      refine ⟨6059146619697934841350253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4039431079798623227566835 6059146619697934841350253)
      ·
        refine ⟨2272179982386725565506345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6059146619697934841350253 2272179982386725565506345)
        ·
          refine ⟨1704134986790044174129759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2272179982386725565506345 1704134986790044174129759)
          ·
            refine ⟨2556202480185066261194639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704134986790044174129759 2556202480185066261194639)
            ·
              refine ⟨3834303720277599391791959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556202480185066261194639 3834303720277599391791959)
              ·
                refine ⟨5751455580416399087687939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3834303720277599391791959 5751455580416399087687939)
                ·
                  refine ⟨8627183370624598631531909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5751455580416399087687939 8627183370624598631531909)
                  ·
                    refine ⟨1617596881992112243412233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8627183370624598631531909 1617596881992112243412233)
                    ·
                      refine ⟨1213197661494084182559175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617596881992112243412233 1213197661494084182559175)
                      ·
                        rfl

theorem cell23_2362694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2362694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362694 prefixEnd_2362694 := by exact prefixLift 2362694
  have htrace : WordTrace (prefixWord ++ tailWord_2362694) baseStart_2362694 baseEnd_2362694 := by
    simpa [prefixWord, tailWord_2362694, baseEnd_2362694] using wordTrace_append hprefix tailTrace_2362694
  have hstable : (prefixWord ++ tailWord_2362694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362694).length < 2 ^ (prefixWord ++ tailWord_2362694).sum := by decide
  have hdescent : baseEnd_2362694 < baseStart_2362694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362712 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_2362712 : Nat := 118140960795 + 2362712 * 2 ^ 59
def prefixEnd_2362712 : Nat := 4983230072969 + 3 ^ 40 * 2362712 * 2
def baseEnd_2362712 : Nat := 1213206904145865112134091

theorem tailTrace_2362712 : CollatzResearch.WordTrace tailWord_2362712 prefixEnd_2362712 1213206904145865112134091 := by
  unfold tailWord_2362712
  simp only [CollatzResearch.WordTrace]
  refine ⟨43087593108152708964457195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57450124144203611952609593 43087593108152708964457195)
  ·
    refine ⟨64631389662229063446685793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43087593108152708964457195 64631389662229063446685793)
    ·
      refine ⟨48473542246671797585014345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64631389662229063446685793 48473542246671797585014345)
      ·
        refine ⟨36355156685003848188760759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48473542246671797585014345 36355156685003848188760759)
        ·
          refine ⟨54532735027505772283141139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36355156685003848188760759 54532735027505772283141139)
          ·
            refine ⟨81799102541258658424711709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54532735027505772283141139 81799102541258658424711709)
            ·
              refine ⟨30674663452971996909266891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81799102541258658424711709 30674663452971996909266891)
              ·
                refine ⟨46011995179457995363900337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30674663452971996909266891 46011995179457995363900337)
                ·
                  refine ⟨34508996384593496522925253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46011995179457995363900337 34508996384593496522925253)
                  ·
                    refine ⟨6470436822111280598048485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 34508996384593496522925253 6470436822111280598048485)
                    ·
                      refine ⟨1213206904145865112134091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6470436822111280598048485 1213206904145865112134091)
                      ·
                        rfl

theorem cell23_2362712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_2362712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362712 prefixEnd_2362712 := by exact prefixLift 2362712
  have htrace : WordTrace (prefixWord ++ tailWord_2362712) baseStart_2362712 baseEnd_2362712 := by
    simpa [prefixWord, tailWord_2362712, baseEnd_2362712] using wordTrace_append hprefix tailTrace_2362712
  have hstable : (prefixWord ++ tailWord_2362712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362712).length < 2 ^ (prefixWord ++ tailWord_2362712).sum := by decide
  have hdescent : baseEnd_2362712 < baseStart_2362712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362717 : List Nat := [1, 4, 5, 1, 1, 2, 1, 3, 5]
def baseStart_2362717 : Nat := 118140960795 + 2362717 * 2 ^ 59
def prefixEnd_2362717 : Nat := 4983230072969 + 3 ^ 40 * 2362717 * 2
def baseEnd_2362717 : Nat := 134801052394348621396841

theorem tailTrace_2362717 : CollatzResearch.WordTrace tailWord_2362717 prefixEnd_2362717 134801052394348621396841 := by
  unfold tailWord_2362717
  simp only [CollatzResearch.WordTrace]
  refine ⟨86175368581287303782846405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57450245720858202521897603 86175368581287303782846405)
  ·
    refine ⟨16157881608991369459283701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86175368581287303782846405 16157881608991369459283701)
    ·
      refine ⟨1514801400842940886807847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16157881608991369459283701 1514801400842940886807847)
      ·
        refine ⟨2272202101264411330211771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514801400842940886807847 2272202101264411330211771)
        ·
          refine ⟨3408303151896616995317657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272202101264411330211771 3408303151896616995317657)
          ·
            refine ⟨2556227363922462746488243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408303151896616995317657 2556227363922462746488243)
            ·
              refine ⟨3834341045883694119732365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556227363922462746488243 3834341045883694119732365)
              ·
                refine ⟨1437877892206385294899637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3834341045883694119732365 1437877892206385294899637)
                ·
                  refine ⟨134801052394348621396841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1437877892206385294899637 134801052394348621396841)
                  ·
                    rfl

theorem cell23_2362717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_2362717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362717 prefixEnd_2362717 := by exact prefixLift 2362717
  have htrace : WordTrace (prefixWord ++ tailWord_2362717) baseStart_2362717 baseEnd_2362717 := by
    simpa [prefixWord, tailWord_2362717, baseEnd_2362717] using wordTrace_append hprefix tailTrace_2362717
  have hstable : (prefixWord ++ tailWord_2362717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362717).length < 2 ^ (prefixWord ++ tailWord_2362717).sum := by decide
  have hdescent : baseEnd_2362717 < baseStart_2362717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362719 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 3]
def baseStart_2362719 : Nat := 118140960795 + 2362719 * 2 ^ 59
def prefixEnd_2362719 : Nat := 4983230072969 + 3 ^ 40 * 2362719 * 2
def baseEnd_2362719 : Nat := 1213210498510446584746559

theorem tailTrace_2362719 : CollatzResearch.WordTrace tailWord_2362719 prefixEnd_2362719 1213210498510446584746559 := by
  unfold tailWord_2362719
  simp only [CollatzResearch.WordTrace]
  refine ⟨86175441527280058124419211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57450294351520038749612807 86175441527280058124419211)
  ·
    refine ⟨129263162290920087186628817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86175441527280058124419211 129263162290920087186628817)
    ·
      refine ⟨96947371718190065389971613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129263162290920087186628817 96947371718190065389971613)
      ·
        refine ⟨36355264394321274521239355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96947371718190065389971613 36355264394321274521239355)
        ·
          refine ⟨54532896591481911781859033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36355264394321274521239355 54532896591481911781859033)
          ·
            refine ⟨40899672443611433836394275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54532896591481911781859033 40899672443611433836394275)
            ·
              refine ⟨61349508665417150754591413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40899672443611433836394275 61349508665417150754591413)
              ·
                refine ⟨5751516437382857883242945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61349508665417150754591413 5751516437382857883242945)
                ·
                  refine ⟨4313637328037143412432209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5751516437382857883242945 4313637328037143412432209)
                  ·
                    refine ⟨3235227996027857559324157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4313637328037143412432209 3235227996027857559324157)
                    ·
                      refine ⟨1213210498510446584746559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3235227996027857559324157 1213210498510446584746559)
                      ·
                        rfl

theorem cell23_2362719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_2362719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362719 prefixEnd_2362719 := by exact prefixLift 2362719
  have htrace : WordTrace (prefixWord ++ tailWord_2362719) baseStart_2362719 baseEnd_2362719 := by
    simpa [prefixWord, tailWord_2362719, baseEnd_2362719] using wordTrace_append hprefix tailTrace_2362719
  have hstable : (prefixWord ++ tailWord_2362719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362719).length < 2 ^ (prefixWord ++ tailWord_2362719).sum := by decide
  have hdescent : baseEnd_2362719 < baseStart_2362719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362743 : List Nat := [1, 1, 3, 1, 1, 2, 7, 2, 1, 4]
def baseStart_2362743 : Nat := 118140960795 + 2362743 * 2 ^ 59
def prefixEnd_2362743 : Nat := 4983230072969 + 3 ^ 40 * 2362743 * 2
def baseEnd_2362743 : Nat := 404407607348718163615483

theorem tailTrace_2362743 : CollatzResearch.WordTrace tailWord_2362743 prefixEnd_2362743 404407607348718163615483 := by
  unfold tailWord_2362743
  simp only [CollatzResearch.WordTrace]
  refine ⟨86176316879193110223292883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57450877919462073482195255 86176316879193110223292883)
  ·
    refine ⟨129264475318789665334939325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86176316879193110223292883 129264475318789665334939325)
    ·
      refine ⟨48474178244546124500602247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129264475318789665334939325 48474178244546124500602247)
      ·
        refine ⟨72711267366819186750903371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48474178244546124500602247 72711267366819186750903371)
        ·
          refine ⟨109066901050228780126355057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72711267366819186750903371 109066901050228780126355057)
          ·
            refine ⟨81800175787671585094766293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109066901050228780126355057 81800175787671585094766293)
            ·
              refine ⟨1917191620023552775658585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 81800175787671585094766293 1917191620023552775658585)
              ·
                refine ⟨1437893715017664581743939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1917191620023552775658585 1437893715017664581743939)
                ·
                  refine ⟨2156840572526496872615909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437893715017664581743939 2156840572526496872615909)
                  ·
                    refine ⟨404407607348718163615483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2156840572526496872615909 404407607348718163615483)
                    ·
                      rfl

theorem cell23_2362743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_2362743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362743 prefixEnd_2362743 := by exact prefixLift 2362743
  have htrace : WordTrace (prefixWord ++ tailWord_2362743) baseStart_2362743 baseEnd_2362743 := by
    simpa [prefixWord, tailWord_2362743, baseEnd_2362743] using wordTrace_append hprefix tailTrace_2362743
  have hstable : (prefixWord ++ tailWord_2362743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362743).length < 2 ^ (prefixWord ++ tailWord_2362743).sum := by decide
  have hdescent : baseEnd_2362743 < baseStart_2362743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362756 : List Nat := [2, 3, 2, 1, 1, 3, 4, 1, 6]
def baseStart_2362756 : Nat := 118140960795 + 2362756 * 2 ^ 59
def prefixEnd_2362756 : Nat := 4983230072969 + 3 ^ 40 * 2362756 * 2
def baseEnd_2362756 : Nat := 134803277477184771109321

theorem tailTrace_2362756 : CollatzResearch.WordTrace tailWord_2362756 prefixEnd_2362756 134803277477184771109321 := by
  unfold tailWord_2362756
  simp only [CollatzResearch.WordTrace]
  refine ⟨43088395514073006721758061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57451194018764008962344081 43088395514073006721758061)
  ·
    refine ⟨16158148317777377520659273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43088395514073006721758061 16158148317777377520659273)
    ·
      refine ⟨12118611238333033140494455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16158148317777377520659273 12118611238333033140494455)
      ·
        refine ⟨18177916857499549710741683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12118611238333033140494455 18177916857499549710741683)
        ·
          refine ⟨27266875286249324566112525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18177916857499549710741683 27266875286249324566112525)
          ·
            refine ⟨10225078232343496712292197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27266875286249324566112525 10225078232343496712292197)
            ·
              refine ⟨1917202168564405633554787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10225078232343496712292197 1917202168564405633554787)
              ·
                refine ⟨2875803252846608450332181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917202168564405633554787 2875803252846608450332181)
                ·
                  refine ⟨134803277477184771109321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2875803252846608450332181 134803277477184771109321)
                  ·
                    rfl

theorem cell23_2362756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_2362756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362756 prefixEnd_2362756 := by exact prefixLift 2362756
  have htrace : WordTrace (prefixWord ++ tailWord_2362756) baseStart_2362756 baseEnd_2362756 := by
    simpa [prefixWord, tailWord_2362756, baseEnd_2362756] using wordTrace_append hprefix tailTrace_2362756
  have hstable : (prefixWord ++ tailWord_2362756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362756).length < 2 ^ (prefixWord ++ tailWord_2362756).sum := by decide
  have hdescent : baseEnd_2362756 < baseStart_2362756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362770 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2362770 : Nat := 118140960795 + 2362770 * 2 ^ 59
def prefixEnd_2362770 : Nat := 4983230072969 + 3 ^ 40 * 2362770 * 2
def baseEnd_2362770 : Nat := 1213236686023825885208825

theorem tailTrace_2362770 : CollatzResearch.WordTrace tailWord_2362770 prefixEnd_2362770 1213236686023825885208825 := by
  unfold tailWord_2362770
  simp only [CollatzResearch.WordTrace]
  refine ⟨21544325412523823458631441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57451534433396862556350509 21544325412523823458631441)
  ·
    refine ⟨16158244059392867593973581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21544325412523823458631441 16158244059392867593973581)
    ·
      refine ⟨6059341522272325347740093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16158244059392867593973581 6059341522272325347740093)
      ·
        refine ⟨2272253070852122005402535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6059341522272325347740093 2272253070852122005402535)
        ·
          refine ⟨3408379606278183008103803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2272253070852122005402535 3408379606278183008103803)
          ·
            refine ⟨5112569409417274512155705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3408379606278183008103803 5112569409417274512155705)
            ·
              refine ⟨3834427057062955884116779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5112569409417274512155705 3834427057062955884116779)
              ·
                refine ⟨5751640585594433826175169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3834427057062955884116779 5751640585594433826175169)
                ·
                  refine ⟨4313730439195825369631377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5751640585594433826175169 4313730439195825369631377)
                  ·
                    refine ⟨3235297829396869027223533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4313730439195825369631377 3235297829396869027223533)
                    ·
                      refine ⟨1213236686023825885208825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3235297829396869027223533 1213236686023825885208825)
                      ·
                        rfl

theorem cell23_2362770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2362770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362770 prefixEnd_2362770 := by exact prefixLift 2362770
  have htrace : WordTrace (prefixWord ++ tailWord_2362770) baseStart_2362770 baseEnd_2362770 := by
    simpa [prefixWord, tailWord_2362770, baseEnd_2362770] using wordTrace_append hprefix tailTrace_2362770
  have hstable : (prefixWord ++ tailWord_2362770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362770).length < 2 ^ (prefixWord ++ tailWord_2362770).sum := by decide
  have hdescent : baseEnd_2362770 < baseStart_2362770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362799 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 4, 4]
def baseStart_2362799 : Nat := 118140960795 + 2362799 * 2 ^ 59
def prefixEnd_2362799 : Nat := 4983230072969 + 3 ^ 40 * 2362799 * 2
def baseEnd_2362799 : Nat := 404417192320935423915397

theorem tailTrace_2362799 : CollatzResearch.WordTrace tailWord_2362799 prefixEnd_2362799 404417192320935423915397 := by
  unfold tailWord_2362799
  simp only [CollatzResearch.WordTrace]
  refine ⟨86178359366990231787331451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57452239577993487858220967 86178359366990231787331451)
  ·
    refine ⟨129267539050485347680997177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86178359366990231787331451 129267539050485347680997177)
    ·
      refine ⟨96950654287864010760747883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129267539050485347680997177 96950654287864010760747883)
      ·
        refine ⟨145425981431796016141121825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96950654287864010760747883 145425981431796016141121825)
        ·
          refine ⟨109069486073847012105841369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145425981431796016141121825 109069486073847012105841369)
          ·
            refine ⟨81802114555385259079381027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109069486073847012105841369 81802114555385259079381027)
            ·
              refine ⟨122703171833077888619071541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81802114555385259079381027 122703171833077888619071541)
              ·
                refine ⟨11503422359351052058037957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122703171833077888619071541 11503422359351052058037957)
                ·
                  refine ⟨2156891692378322260882117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11503422359351052058037957 2156891692378322260882117)
                  ·
                    refine ⟨404417192320935423915397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2156891692378322260882117 404417192320935423915397)
                    ·
                      rfl

theorem cell23_2362799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 4].length) (baseStart_2362799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362799 prefixEnd_2362799 := by exact prefixLift 2362799
  have htrace : WordTrace (prefixWord ++ tailWord_2362799) baseStart_2362799 baseEnd_2362799 := by
    simpa [prefixWord, tailWord_2362799, baseEnd_2362799] using wordTrace_append hprefix tailTrace_2362799
  have hstable : (prefixWord ++ tailWord_2362799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362799).length < 2 ^ (prefixWord ++ tailWord_2362799).sum := by decide
  have hdescent : baseEnd_2362799 < baseStart_2362799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362816 : List Nat := [2, 1, 1, 2, 3, 1, 4, 3, 2, 4]
def baseStart_2362816 : Nat := 118140960795 + 2362816 * 2 ^ 59
def prefixEnd_2362816 : Nat := 4983230072969 + 3 ^ 40 * 2362816 * 2
def baseEnd_2362816 : Nat := 404420102044644235077871

theorem tailTrace_2362816 : CollatzResearch.WordTrace tailWord_2362816 prefixEnd_2362816 404420102044644235077871 := by
  unfold tailWord_2362816
  simp only [CollatzResearch.WordTrace]
  refine ⟨43089489703964321845350151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57452652938619095793800201 43089489703964321845350151)
  ·
    refine ⟨64634234555946482768025227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43089489703964321845350151 64634234555946482768025227)
    ·
      refine ⟨96951351833919724152037841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64634234555946482768025227 96951351833919724152037841)
      ·
        refine ⟨72713513875439793114028381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96951351833919724152037841 72713513875439793114028381)
        ·
          refine ⟨27267567703289922417760643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72713513875439793114028381 27267567703289922417760643)
          ·
            refine ⟨40901351554934883626640965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27267567703289922417760643 40901351554934883626640965)
            ·
              refine ⟨7669003416550290679995181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40901351554934883626640965 7669003416550290679995181)
              ·
                refine ⟨2875876281206359004998193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7669003416550290679995181 2875876281206359004998193)
                ·
                  refine ⟨2156907210904769253748645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2875876281206359004998193 2156907210904769253748645)
                  ·
                    refine ⟨404420102044644235077871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2156907210904769253748645 404420102044644235077871)
                    ·
                      rfl

theorem cell23_2362816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3, 2, 4].length) (baseStart_2362816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362816 prefixEnd_2362816 := by exact prefixLift 2362816
  have htrace : WordTrace (prefixWord ++ tailWord_2362816) baseStart_2362816 baseEnd_2362816 := by
    simpa [prefixWord, tailWord_2362816, baseEnd_2362816] using wordTrace_append hprefix tailTrace_2362816
  have hstable : (prefixWord ++ tailWord_2362816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362816).length < 2 ^ (prefixWord ++ tailWord_2362816).sum := by decide
  have hdescent : baseEnd_2362816 < baseStart_2362816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362819 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 4]
def baseStart_2362819 : Nat := 118140960795 + 2362819 * 2 ^ 59
def prefixEnd_2362819 : Nat := 4983230072969 + 3 ^ 40 * 2362819 * 2
def baseEnd_2362819 : Nat := 1213261846575896193496099

theorem tailTrace_2362819 : CollatzResearch.WordTrace tailWord_2362819 prefixEnd_2362819 1213261846575896193496099 := by
  unfold tailWord_2362819
  simp only [CollatzResearch.WordTrace]
  refine ⟨86179088826917775203059511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57452725884611850135373007 86179088826917775203059511)
  ·
    refine ⟨129268633240376662804589267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86179088826917775203059511 129268633240376662804589267)
    ·
      refine ⟨193902949860564994206883901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129268633240376662804589267 193902949860564994206883901)
      ·
        refine ⟨72713606197711872827581463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 193902949860564994206883901 72713606197711872827581463)
        ·
          refine ⟨109070409296567809241372195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72713606197711872827581463 109070409296567809241372195)
          ·
            refine ⟨163605613944851713862058293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109070409296567809241372195 163605613944851713862058293)
            ·
              refine ⟨15338026307329848174567965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163605613944851713862058293 15338026307329848174567965)
              ·
                refine ⟨5751759865248693065462987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15338026307329848174567965 5751759865248693065462987)
                ·
                  refine ⟨8627639797873039598194481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5751759865248693065462987 8627639797873039598194481)
                  ·
                    refine ⟨6470729848404779698645861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8627639797873039598194481 6470729848404779698645861)
                    ·
                      refine ⟨1213261846575896193496099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6470729848404779698645861 1213261846575896193496099)
                      ·
                        rfl

theorem cell23_2362819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_2362819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362819 prefixEnd_2362819 := by exact prefixLift 2362819
  have htrace : WordTrace (prefixWord ++ tailWord_2362819) baseStart_2362819 baseEnd_2362819 := by
    simpa [prefixWord, tailWord_2362819, baseEnd_2362819] using wordTrace_append hprefix tailTrace_2362819
  have hstable : (prefixWord ++ tailWord_2362819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362819).length < 2 ^ (prefixWord ++ tailWord_2362819).sum := by decide
  have hdescent : baseEnd_2362819 < baseStart_2362819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362823 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 3, 2, 2]
def baseStart_2362823 : Nat := 118140960795 + 2362823 * 2 ^ 59
def prefixEnd_2362823 : Nat := 4983230072969 + 3 ^ 40 * 2362823 * 2
def baseEnd_2362823 : Nat := 1213263900498514177846081

theorem tailTrace_2362823 : CollatzResearch.WordTrace tailWord_2362823 prefixEnd_2362823 1213263900498514177846081 := by
  unfold tailWord_2362823
  simp only [CollatzResearch.WordTrace]
  refine ⟨86179234718903283886205123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57452823145935522590803415 86179234718903283886205123)
  ·
    refine ⟨129268852078354925829307685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86179234718903283886205123 129268852078354925829307685)
    ·
      refine ⟨24237909764691548592995191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129268852078354925829307685 24237909764691548592995191)
      ·
        refine ⟨36356864647037322889492787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24237909764691548592995191 36356864647037322889492787)
        ·
          refine ⟨54535296970555984334239181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36356864647037322889492787 54535296970555984334239181)
          ·
            refine ⟨20450736363958494125339693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54535296970555984334239181 20450736363958494125339693)
            ·
              refine ⟨7669026136484435297002385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20450736363958494125339693 7669026136484435297002385)
              ·
                refine ⟨5751769602363326472751789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7669026136484435297002385 5751769602363326472751789)
                ·
                  refine ⟨2156913600886247427281921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5751769602363326472751789 2156913600886247427281921)
                  ·
                    refine ⟨1617685200664685570461441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2156913600886247427281921 1617685200664685570461441)
                    ·
                      refine ⟨1213263900498514177846081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617685200664685570461441 1213263900498514177846081)
                      ·
                        rfl

theorem cell23_2362823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_2362823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362823 prefixEnd_2362823 := by exact prefixLift 2362823
  have htrace : WordTrace (prefixWord ++ tailWord_2362823) baseStart_2362823 baseEnd_2362823 := by
    simpa [prefixWord, tailWord_2362823, baseEnd_2362823] using wordTrace_append hprefix tailTrace_2362823
  have hstable : (prefixWord ++ tailWord_2362823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362823).length < 2 ^ (prefixWord ++ tailWord_2362823).sum := by decide
  have hdescent : baseEnd_2362823 < baseStart_2362823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362826 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_2362826 : Nat := 118140960795 + 2362826 * 2 ^ 59
def prefixEnd_2362826 : Nat := 4983230072969 + 3 ^ 40 * 2362826 * 2
def baseEnd_2362826 : Nat := 1213265440940477666108567

theorem tailTrace_2362826 : CollatzResearch.WordTrace tailWord_2362826 prefixEnd_2362826 1213265440940477666108567 := by
  unfold tailWord_2362826
  simp only [CollatzResearch.WordTrace]
  refine ⟨21544836034473103849641083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57452896091928276932376221 21544836034473103849641083)
  ·
    refine ⟨32317254051709655774461625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21544836034473103849641083 32317254051709655774461625)
    ·
      refine ⟨24237940538782241830846219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32317254051709655774461625 24237940538782241830846219)
      ·
        refine ⟨36356910808173362746269329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24237940538782241830846219 36356910808173362746269329)
        ·
          refine ⟨27267683106130022059701997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36356910808173362746269329 27267683106130022059701997)
          ·
            refine ⟨10225381164798758272388249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27267683106130022059701997 10225381164798758272388249)
            ·
              refine ⟨7669035873599068704291187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10225381164798758272388249 7669035873599068704291187)
              ·
                refine ⟨11503553810398603056436781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7669035873599068704291187 11503553810398603056436781)
                ·
                  refine ⟨4313832678899476146163793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11503553810398603056436781 4313832678899476146163793)
                  ·
                    refine ⟨3235374509174607109622845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4313832678899476146163793 3235374509174607109622845)
                    ·
                      refine ⟨1213265440940477666108567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3235374509174607109622845 1213265440940477666108567)
                      ·
                        rfl

theorem cell23_2362826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_2362826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362826 prefixEnd_2362826 := by exact prefixLift 2362826
  have htrace : WordTrace (prefixWord ++ tailWord_2362826) baseStart_2362826 baseEnd_2362826 := by
    simpa [prefixWord, tailWord_2362826, baseEnd_2362826] using wordTrace_append hprefix tailTrace_2362826
  have hstable : (prefixWord ++ tailWord_2362826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362826).length < 2 ^ (prefixWord ++ tailWord_2362826).sum := by decide
  have hdescent : baseEnd_2362826 < baseStart_2362826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362840 : List Nat := [2, 1, 2, 2, 2, 1, 3, 5, 1, 2, 2]
def baseStart_2362840 : Nat := 118140960795 + 2362840 * 2 ^ 59
def prefixEnd_2362840 : Nat := 4983230072969 + 3 ^ 40 * 2362840 * 2
def baseEnd_2362840 : Nat := 1213272629669640611333503

theorem tailTrace_2362840 : CollatzResearch.WordTrace tailWord_2362840 prefixEnd_2362840 1213272629669640611333503 := by
  unfold tailWord_2362840
  simp only [CollatzResearch.WordTrace]
  refine ⟨43089927379920847894786987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57453236506561130526382649 43089927379920847894786987)
  ·
    refine ⟨64634891069881271842180481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43089927379920847894786987 64634891069881271842180481)
    ·
      refine ⟨48476168302410953881635361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64634891069881271842180481 48476168302410953881635361)
      ·
        refine ⟨36357126226808215411226521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48476168302410953881635361 36357126226808215411226521)
        ·
          refine ⟨27267844670106161558419891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36357126226808215411226521 27267844670106161558419891)
          ·
            refine ⟨40901767005159242337629837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27267844670106161558419891 40901767005159242337629837)
            ·
              refine ⟨15338162626934715876611189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40901767005159242337629837 15338162626934715876611189)
              ·
                refine ⟨1437952746275129613432299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15338162626934715876611189 1437952746275129613432299)
                ·
                  refine ⟨2156929119412694420148449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1437952746275129613432299 2156929119412694420148449)
                  ·
                    refine ⟨1617696839559520815111337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2156929119412694420148449 1617696839559520815111337)
                    ·
                      refine ⟨1213272629669640611333503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617696839559520815111337 1213272629669640611333503)
                      ·
                        rfl

theorem cell23_2362840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_2362840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362840 prefixEnd_2362840 := by exact prefixLift 2362840
  have htrace : WordTrace (prefixWord ++ tailWord_2362840) baseStart_2362840 baseEnd_2362840 := by
    simpa [prefixWord, tailWord_2362840, baseEnd_2362840] using wordTrace_append hprefix tailTrace_2362840
  have hstable : (prefixWord ++ tailWord_2362840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362840).length < 2 ^ (prefixWord ++ tailWord_2362840).sum := by decide
  have hdescent : baseEnd_2362840 < baseStart_2362840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362899 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 5]
def baseStart_2362899 : Nat := 118140960795 + 2362899 * 2 ^ 59
def prefixEnd_2362899 : Nat := 4983230072969 + 3 ^ 40 * 2362899 * 2
def baseEnd_2362899 : Nat := 1213302925028255880495731

theorem tailTrace_2362899 : CollatzResearch.WordTrace tailWord_2362899 prefixEnd_2362899 1213302925028255880495731 := by
  unfold tailWord_2362899
  simp only [CollatzResearch.WordTrace]
  refine ⟨86182006666627948865971751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57454671111085299243981167 86182006666627948865971751)
  ·
    refine ⟨129273009999941923298957627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86182006666627948865971751 129273009999941923298957627)
    ·
      refine ⟨193909514999912884948436441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129273009999941923298957627 193909514999912884948436441)
      ·
        refine ⟨145432136249934663711327331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 193909514999912884948436441 145432136249934663711327331)
        ·
          refine ⟨218148204374901995566990997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145432136249934663711327331 218148204374901995566990997)
          ·
            refine ⟨10225697080073531042202703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 218148204374901995566990997 10225697080073531042202703)
            ·
              refine ⟨15338545620110296563304055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10225697080073531042202703 15338545620110296563304055)
              ·
                refine ⟨23007818430165444844956083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15338545620110296563304055 23007818430165444844956083)
                ·
                  refine ⟨34511727645248167267434125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23007818430165444844956083 34511727645248167267434125)
                  ·
                    refine ⟨12941897866968062725287797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34511727645248167267434125 12941897866968062725287797)
                    ·
                      refine ⟨1213302925028255880495731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12941897866968062725287797 1213302925028255880495731)
                      ·
                        rfl

theorem cell23_2362899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 3, 5].length) (baseStart_2362899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362899 prefixEnd_2362899 := by exact prefixLift 2362899
  have htrace : WordTrace (prefixWord ++ tailWord_2362899) baseStart_2362899 baseEnd_2362899 := by
    simpa [prefixWord, tailWord_2362899, baseEnd_2362899] using wordTrace_append hprefix tailTrace_2362899
  have hstable : (prefixWord ++ tailWord_2362899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362899).length < 2 ^ (prefixWord ++ tailWord_2362899).sum := by decide
  have hdescent : baseEnd_2362899 < baseStart_2362899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2362934 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_2362934 : Nat := 118140960795 + 2362934 * 2 ^ 59
def prefixEnd_2362934 : Nat := 4983230072969 + 3 ^ 40 * 2362934 * 2
def baseEnd_2362934 : Nat := 1213320896851163243558071

theorem tailTrace_2362934 : CollatzResearch.WordTrace tailWord_2362934 prefixEnd_2362934 1213320896851163243558071 := by
  unfold tailWord_2362934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5386455201343821865218491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57455522147667433228997237 5386455201343821865218491)
  ·
    refine ⟨8079682802015732797827737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5386455201343821865218491 8079682802015732797827737)
    ·
      refine ⟨6059762101511799598370803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8079682802015732797827737 6059762101511799598370803)
      ·
        refine ⟨9089643152267699397556205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6059762101511799598370803 9089643152267699397556205)
        ·
          refine ⟨3408616182100387274083577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9089643152267699397556205 3408616182100387274083577)
          ·
            refine ⟨2556462136575290455562683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408616182100387274083577 2556462136575290455562683)
            ·
              refine ⟨3834693204862935683344025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556462136575290455562683 3834693204862935683344025)
              ·
                refine ⟨2876019903647201762508019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3834693204862935683344025 2876019903647201762508019)
                ·
                  refine ⟨4314029855470802643762029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876019903647201762508019 4314029855470802643762029)
                  ·
                    refine ⟨1617761195801550991410761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4314029855470802643762029 1617761195801550991410761)
                    ·
                      refine ⟨1213320896851163243558071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617761195801550991410761 1213320896851163243558071)
                      ·
                        rfl

theorem cell23_2362934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_2362934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2362934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2362934 prefixEnd_2362934 := by exact prefixLift 2362934
  have htrace : WordTrace (prefixWord ++ tailWord_2362934) baseStart_2362934 baseEnd_2362934 := by
    simpa [prefixWord, tailWord_2362934, baseEnd_2362934] using wordTrace_append hprefix tailTrace_2362934
  have hstable : (prefixWord ++ tailWord_2362934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2362934).length < 2 ^ (prefixWord ++ tailWord_2362934).sum := by decide
  have hdescent : baseEnd_2362934 < baseStart_2362934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2362934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363043 : List Nat := [1, 1, 1, 4, 1, 1, 7, 1, 6]
def baseStart_2363043 : Nat := 118140960795 + 2363043 * 2 ^ 59
def prefixEnd_2363043 : Nat := 4983230072969 + 3 ^ 40 * 2363043 * 2
def baseEnd_2363043 : Nat := 134819651804722590788341

theorem tailTrace_2363043 : CollatzResearch.WordTrace tailWord_2363043 prefixEnd_2363043 134819651804722590788341 := by
  unfold tailWord_2363043
  simp only [CollatzResearch.WordTrace]
  refine ⟨86187258778106261459213783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57458172518737507639475855 86187258778106261459213783)
  ·
    refine ⟨129280888167159392188820675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86187258778106261459213783 129280888167159392188820675)
    ·
      refine ⟨193921332250739088283231013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129280888167159392188820675 193921332250739088283231013)
      ·
        refine ⟨36360249797013579053105815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 193921332250739088283231013 36360249797013579053105815)
        ·
          refine ⟨54540374695520368579658723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36360249797013579053105815 54540374695520368579658723)
          ·
            refine ⟨81810562043280552869488085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54540374695520368579658723 81810562043280552869488085)
            ·
              refine ⟨1917435047889387957878627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 81810562043280552869488085 1917435047889387957878627)
              ·
                refine ⟨2876152571834081936817941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917435047889387957878627 2876152571834081936817941)
                ·
                  refine ⟨134819651804722590788341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2876152571834081936817941 134819651804722590788341)
                  ·
                    rfl

theorem cell23_2363043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 7, 1, 6].length) (baseStart_2363043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363043 prefixEnd_2363043 := by exact prefixLift 2363043
  have htrace : WordTrace (prefixWord ++ tailWord_2363043) baseStart_2363043 baseEnd_2363043 := by
    simpa [prefixWord, tailWord_2363043, baseEnd_2363043] using wordTrace_append hprefix tailTrace_2363043
  have hstable : (prefixWord ++ tailWord_2363043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363043).length < 2 ^ (prefixWord ++ tailWord_2363043).sum := by decide
  have hdescent : baseEnd_2363043 < baseStart_2363043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363053 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_2363053 : Nat := 118140960795 + 2363053 * 2 ^ 59
def prefixEnd_2363053 : Nat := 4983230072969 + 3 ^ 40 * 2363053 * 2
def baseEnd_2363053 : Nat := 1213382001049048277970023

theorem tailTrace_2363053 : CollatzResearch.WordTrace tailWord_2363053 prefixEnd_2363053 1213382001049048277970023 := by
  unfold tailWord_2363053
  simp only [CollatzResearch.WordTrace]
  refine ⟨86187623508070033167077813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57458415672046688778051875 86187623508070033167077813)
  ·
    refine ⟨8080089703881565609413545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86187623508070033167077813 8080089703881565609413545)
    ·
      refine ⟨6060067277911174207060159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8080089703881565609413545 6060067277911174207060159)
      ·
        refine ⟨9090100916866761310590239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6060067277911174207060159 9090100916866761310590239)
        ·
          refine ⟨13635151375300141965885359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9090100916866761310590239 13635151375300141965885359)
          ·
            refine ⟨20452727062950212948828039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13635151375300141965885359 20452727062950212948828039)
            ·
              refine ⟨30679090594425319423242059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20452727062950212948828039 30679090594425319423242059)
              ·
                refine ⟨46018635891637979134863089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30679090594425319423242059 46018635891637979134863089)
                ·
                  refine ⟨34513976918728484351147317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46018635891637979134863089 34513976918728484351147317)
                  ·
                    refine ⟨3235685336130795407920061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34513976918728484351147317 3235685336130795407920061)
                    ·
                      refine ⟨1213382001049048277970023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3235685336130795407920061 1213382001049048277970023)
                      ·
                        rfl

theorem cell23_2363053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_2363053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363053 prefixEnd_2363053 := by exact prefixLift 2363053
  have htrace : WordTrace (prefixWord ++ tailWord_2363053) baseStart_2363053 baseEnd_2363053 := by
    simpa [prefixWord, tailWord_2363053, baseEnd_2363053] using wordTrace_append hprefix tailTrace_2363053
  have hstable : (prefixWord ++ tailWord_2363053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363053).length < 2 ^ (prefixWord ++ tailWord_2363053).sum := by decide
  have hdescent : baseEnd_2363053 < baseStart_2363053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363056 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 3, 5]
def baseStart_2363056 : Nat := 118140960795 + 2363056 * 2 ^ 59
def prefixEnd_2363056 : Nat := 4983230072969 + 3 ^ 40 * 2363056 * 2
def baseEnd_2363056 : Nat := 404461180497003922077503

theorem tailTrace_2363056 : CollatzResearch.WordTrace tailWord_2363056 prefixEnd_2363056 404461180497003922077503 := by
  unfold tailWord_2363056
  simp only [CollatzResearch.WordTrace]
  refine ⟨43093866463529582339718511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57458488618039443119624681 43093866463529582339718511)
  ·
    refine ⟨64640799695294373509577767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43093866463529582339718511 64640799695294373509577767)
    ·
      refine ⟨96961199542941560264366651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64640799695294373509577767 96961199542941560264366651)
      ·
        refine ⟨145441799314412340396549977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96961199542941560264366651 145441799314412340396549977)
        ·
          refine ⟨109081349485809255297412483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145441799314412340396549977 109081349485809255297412483)
          ·
            refine ⟨163622024228713882946118725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109081349485809255297412483 163622024228713882946118725)
            ·
              refine ⟨30679129542883853052397261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 163622024228713882946118725 30679129542883853052397261)
              ·
                refine ⟨11504673578581444894648973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30679129542883853052397261 11504673578581444894648973)
                ·
                  refine ⟨4314252591968041835493365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11504673578581444894648973 4314252591968041835493365)
                  ·
                    refine ⟨404461180497003922077503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4314252591968041835493365 404461180497003922077503)
                    ·
                      rfl

theorem cell23_2363056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_2363056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363056 prefixEnd_2363056 := by exact prefixLift 2363056
  have htrace : WordTrace (prefixWord ++ tailWord_2363056) baseStart_2363056 baseEnd_2363056 := by
    simpa [prefixWord, tailWord_2363056, baseEnd_2363056] using wordTrace_append hprefix tailTrace_2363056
  have hstable : (prefixWord ++ tailWord_2363056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363056).length < 2 ^ (prefixWord ++ tailWord_2363056).sum := by decide
  have hdescent : baseEnd_2363056 < baseStart_2363056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363080 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 2, 3, 2]
def baseStart_2363080 : Nat := 118140960795 + 2363080 * 2 ^ 59
def prefixEnd_2363080 : Nat := 4983230072969 + 3 ^ 40 * 2363080 * 2
def baseEnd_2363080 : Nat := 1213395865026719672332399

theorem tailTrace_2363080 : CollatzResearch.WordTrace tailWord_2363080 prefixEnd_2363080 1213395865026719672332399 := by
  unfold tailWord_2363080
  simp only [CollatzResearch.WordTrace]
  refine ⟨43094304139486108389155347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57459072185981477852207129 43094304139486108389155347)
  ·
    refine ⟨64641456209229162583733021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43094304139486108389155347 64641456209229162583733021)
    ·
      refine ⟨24240546078460935968899883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64641456209229162583733021 24240546078460935968899883)
      ·
        refine ⟨36360819117691403953349825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24240546078460935968899883 36360819117691403953349825)
        ·
          refine ⟨27270614338268552965012369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36360819117691403953349825 27270614338268552965012369)
          ·
            refine ⟨20452960753701414723759277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27270614338268552965012369 20452960753701414723759277)
            ·
              refine ⟨7669860282638030521409729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20452960753701414723759277 7669860282638030521409729)
              ·
                refine ⟨5752395211978522891057297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7669860282638030521409729 5752395211978522891057297)
                ·
                  refine ⟨4314296408983892168292973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5752395211978522891057297 4314296408983892168292973)
                  ·
                    refine ⟨1617861153368959563109865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4314296408983892168292973 1617861153368959563109865)
                    ·
                      refine ⟨1213395865026719672332399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617861153368959563109865 1213395865026719672332399)
                      ·
                        rfl

theorem cell23_2363080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_2363080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363080 prefixEnd_2363080 := by exact prefixLift 2363080
  have htrace : WordTrace (prefixWord ++ tailWord_2363080) baseStart_2363080 baseEnd_2363080 := by
    simpa [prefixWord, tailWord_2363080, baseEnd_2363080] using wordTrace_append hprefix tailTrace_2363080
  have hstable : (prefixWord ++ tailWord_2363080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363080).length < 2 ^ (prefixWord ++ tailWord_2363080).sum := by decide
  have hdescent : baseEnd_2363080 < baseStart_2363080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363107 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 1, 5]
def baseStart_2363107 : Nat := 118140960795 + 2363107 * 2 ^ 59
def prefixEnd_2363107 : Nat := 4983230072969 + 3 ^ 40 * 2363107 * 2
def baseEnd_2363107 : Nat := 404469909668130355564925

theorem tailTrace_2363107 : CollatzResearch.WordTrace tailWord_2363107 prefixEnd_2363107 404469909668130355564925 := by
  unfold tailWord_2363107
  simp only [CollatzResearch.WordTrace]
  refine ⟨86189593049874400389543575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57459728699916266926362383 86189593049874400389543575)
  ·
    refine ⟨129284389574811600584315363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86189593049874400389543575 129284389574811600584315363)
    ·
      refine ⟨193926584362217400876473045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129284389574811600584315363 193926584362217400876473045)
      ·
        refine ⟨4545154320989470333042337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 193926584362217400876473045 4545154320989470333042337)
        ·
          refine ⟨3408865740742102749781753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4545154320989470333042337 3408865740742102749781753)
          ·
            refine ⟨2556649305556577062336315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408865740742102749781753 2556649305556577062336315)
            ·
              refine ⟨3834973958334865593504473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556649305556577062336315 3834973958334865593504473)
              ·
                refine ⟨2876230468751149195128355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3834973958334865593504473 2876230468751149195128355)
                ·
                  refine ⟨4314345703126723792692533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876230468751149195128355 4314345703126723792692533)
                  ·
                    refine ⟨404469909668130355564925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4314345703126723792692533 404469909668130355564925)
                    ·
                      rfl

theorem cell23_2363107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 5].length) (baseStart_2363107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363107 prefixEnd_2363107 := by exact prefixLift 2363107
  have htrace : WordTrace (prefixWord ++ tailWord_2363107) baseStart_2363107 baseEnd_2363107 := by
    simpa [prefixWord, tailWord_2363107, baseEnd_2363107] using wordTrace_append hprefix tailTrace_2363107
  have hstable : (prefixWord ++ tailWord_2363107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363107).length < 2 ^ (prefixWord ++ tailWord_2363107).sum := by decide
  have hdescent : baseEnd_2363107 < baseStart_2363107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363116 : List Nat := [2, 2, 1, 1, 2, 2, 4, 9]
def baseStart_2363116 : Nat := 118140960795 + 2363116 * 2 ^ 59
def prefixEnd_2363116 : Nat := 4983230072969 + 3 ^ 40 * 2363116 * 2
def baseEnd_2363116 : Nat := 44941272234454871536379

theorem tailTrace_2363116 : CollatzResearch.WordTrace tailWord_2363116 prefixEnd_2363116 44941272234454871536379 := by
  unfold tailWord_2363116
  simp only [CollatzResearch.WordTrace]
  refine ⟨43094960653420897463310601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57459947537894529951080801 43094960653420897463310601)
  ·
    refine ⟨32321220490065673097482951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43094960653420897463310601 32321220490065673097482951)
    ·
      refine ⟨48481830735098509646224427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32321220490065673097482951 48481830735098509646224427)
      ·
        refine ⟨72722746102647764469336641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48481830735098509646224427 72722746102647764469336641)
        ·
          refine ⟨54542059576985823352002481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72722746102647764469336641 54542059576985823352002481)
          ·
            refine ⟨40906544682739367514001861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54542059576985823352002481 40906544682739367514001861)
            ·
              refine ⟨7669977128013631408875349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40906544682739367514001861 7669977128013631408875349)
              ·
                refine ⟨44941272234454871536379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7669977128013631408875349 44941272234454871536379)
                ·
                  rfl

theorem cell23_2363116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 9].length) (baseStart_2363116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363116 prefixEnd_2363116 := by exact prefixLift 2363116
  have htrace : WordTrace (prefixWord ++ tailWord_2363116) baseStart_2363116 baseEnd_2363116 := by
    simpa [prefixWord, tailWord_2363116, baseEnd_2363116] using wordTrace_append hprefix tailTrace_2363116
  have hstable : (prefixWord ++ tailWord_2363116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363116).length < 2 ^ (prefixWord ++ tailWord_2363116).sum := by decide
  have hdescent : baseEnd_2363116 < baseStart_2363116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363144 : List Nat := [2, 1, 3, 2, 2, 1, 3, 4, 1, 2, 2]
def baseStart_2363144 : Nat := 118140960795 + 2363144 * 2 ^ 59
def prefixEnd_2363144 : Nat := 4983230072969 + 3 ^ 40 * 2363144 * 2
def baseEnd_2363144 : Nat := 1213428727788607421932105

theorem tailTrace_2363144 : CollatzResearch.WordTrace tailWord_2363144 prefixEnd_2363144 1213428727788607421932105 := by
  unfold tailWord_2363144
  simp only [CollatzResearch.WordTrace]
  refine ⟨43095471275370177854320243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57460628367160237139093657 43095471275370177854320243)
  ·
    refine ⟨64643206913055266781480365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43095471275370177854320243 64643206913055266781480365)
    ·
      refine ⟨24241202592395725043055137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64643206913055266781480365 24241202592395725043055137)
      ·
        refine ⟨18180901944296793782291353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24241202592395725043055137 18180901944296793782291353)
        ·
          refine ⟨13635676458222595336718515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18180901944296793782291353 13635676458222595336718515)
          ·
            refine ⟨20453514687333893005077773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13635676458222595336718515 20453514687333893005077773)
            ·
              refine ⟨7670068007750209876904165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20453514687333893005077773 7670068007750209876904165)
              ·
                refine ⟨1438137751453164351919531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7670068007750209876904165 1438137751453164351919531)
                ·
                  refine ⟨2157206627179746527879297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438137751453164351919531 2157206627179746527879297)
                  ·
                    refine ⟨1617904970384809895909473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2157206627179746527879297 1617904970384809895909473)
                    ·
                      refine ⟨1213428727788607421932105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617904970384809895909473 1213428727788607421932105)
                      ·
                        rfl

theorem cell23_2363144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_2363144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363144 prefixEnd_2363144 := by exact prefixLift 2363144
  have htrace : WordTrace (prefixWord ++ tailWord_2363144) baseStart_2363144 baseEnd_2363144 := by
    simpa [prefixWord, tailWord_2363144, baseEnd_2363144] using wordTrace_append hprefix tailTrace_2363144
  have hstable : (prefixWord ++ tailWord_2363144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363144).length < 2 ^ (prefixWord ++ tailWord_2363144).sum := by decide
  have hdescent : baseEnd_2363144 < baseStart_2363144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363194 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3]
def baseStart_2363194 : Nat := 118140960795 + 2363194 * 2 ^ 59
def prefixEnd_2363194 : Nat := 4983230072969 + 3 ^ 40 * 2363194 * 2
def baseEnd_2363194 : Nat := 1213454401821332226306875

theorem tailTrace_2363194 : CollatzResearch.WordTrace tailWord_2363194 prefixEnd_2363194 1213454401821332226306875 := by
  unfold tailWord_2363194
  simp only [CollatzResearch.WordTrace]
  refine ⟨21548191550139803561990159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57461844133706142831973757 21548191550139803561990159)
  ·
    refine ⟨32322287325209705342985239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21548191550139803561990159 32322287325209705342985239)
    ·
      refine ⟨48483430987814558014477859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32322287325209705342985239 48483430987814558014477859)
      ·
        refine ⟨72725146481721837021716789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48483430987814558014477859 72725146481721837021716789)
        ·
          refine ⟨6817982482661422220785949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72725146481721837021716789 6817982482661422220785949)
          ·
            refine ⟨2556743430998033332794731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6817982482661422220785949 2556743430998033332794731)
            ·
              refine ⟨3835115146497049999192097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556743430998033332794731 3835115146497049999192097)
              ·
                refine ⟨2876336359872787499394073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3835115146497049999192097 2876336359872787499394073)
                ·
                  refine ⟨2157252269904590624545555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2876336359872787499394073 2157252269904590624545555)
                  ·
                    refine ⟨3235878404856885936818333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2157252269904590624545555 3235878404856885936818333)
                    ·
                      refine ⟨1213454401821332226306875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3235878404856885936818333 1213454401821332226306875)
                      ·
                        rfl

theorem cell23_2363194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_2363194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363194 prefixEnd_2363194 := by exact prefixLift 2363194
  have htrace : WordTrace (prefixWord ++ tailWord_2363194) baseStart_2363194 baseEnd_2363194 := by
    simpa [prefixWord, tailWord_2363194, baseEnd_2363194] using wordTrace_append hprefix tailTrace_2363194
  have hstable : (prefixWord ++ tailWord_2363194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363194).length < 2 ^ (prefixWord ++ tailWord_2363194).sum := by decide
  have hdescent : baseEnd_2363194 < baseStart_2363194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363217 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 1, 4, 2]
def baseStart_2363217 : Nat := 118140960795 + 2363217 * 2 ^ 59
def prefixEnd_2363217 : Nat := 4983230072969 + 3 ^ 40 * 2363217 * 2
def baseEnd_2363217 : Nat := 1213466211876385636319269

theorem tailTrace_2363217 : CollatzResearch.WordTrace tailWord_2363217 prefixEnd_2363217 1213466211876385636319269 := by
  unfold tailWord_2363217
  simp only [CollatzResearch.WordTrace]
  refine ⟨86193605079475889176047905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57462403386317259450698603 86193605079475889176047905)
  ·
    refine ⟨64645203809606916882035929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86193605079475889176047905 64645203809606916882035929)
    ·
      refine ⟨48483902857205187661526947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64645203809606916882035929 48483902857205187661526947)
      ·
        refine ⟨72725854285807781492290421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48483902857205187661526947 72725854285807781492290421)
        ·
          refine ⟨6818048839294479514902227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72725854285807781492290421 6818048839294479514902227)
          ·
            refine ⟨10227073258941719272353341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6818048839294479514902227 10227073258941719272353341)
            ·
              refine ⟨3835152472103144727132503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10227073258941719272353341 3835152472103144727132503)
              ·
                refine ⟨5752728708154717090698755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3835152472103144727132503 5752728708154717090698755)
                ·
                  refine ⟨8629093062232075636048133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5752728708154717090698755 8629093062232075636048133)
                  ·
                    refine ⟨1617954949168514181759025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8629093062232075636048133 1617954949168514181759025)
                    ·
                      refine ⟨1213466211876385636319269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617954949168514181759025 1213466211876385636319269)
                      ·
                        rfl

theorem cell23_2363217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 4, 2].length) (baseStart_2363217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363217 prefixEnd_2363217 := by exact prefixLift 2363217
  have htrace : WordTrace (prefixWord ++ tailWord_2363217) baseStart_2363217 baseEnd_2363217 := by
    simpa [prefixWord, tailWord_2363217, baseEnd_2363217] using wordTrace_append hprefix tailTrace_2363217
  have hstable : (prefixWord ++ tailWord_2363217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363217).length < 2 ^ (prefixWord ++ tailWord_2363217).sum := by decide
  have hdescent : baseEnd_2363217 < baseStart_2363217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363234 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_2363234 : Nat := 118140960795 + 2363234 * 2 ^ 59
def prefixEnd_2363234 : Nat := 4983230072969 + 3 ^ 40 * 2363234 * 2
def baseEnd_2363234 : Nat := 1213474941047512069806691

theorem tailTrace_2363234 : CollatzResearch.WordTrace tailWord_2363234 prefixEnd_2363234 1213474941047512069806691 := by
  unfold tailWord_2363234
  simp only [CollatzResearch.WordTrace]
  refine ⟨21548556280103575269854189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57462816746942867386277837 21548556280103575269854189)
  ·
    refine ⟨8080708605038840726195321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21548556280103575269854189 8080708605038840726195321)
    ·
      refine ⟨6060531453779130544646491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8080708605038840726195321 6060531453779130544646491)
      ·
        refine ⟨9090797180668695816969737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6060531453779130544646491 9090797180668695816969737)
        ·
          refine ⟨6818097885501521862727303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9090797180668695816969737 6818097885501521862727303)
          ·
            refine ⟨10227146828252282794090955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6818097885501521862727303 10227146828252282794090955)
            ·
              refine ⟨15340720242378424191136433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10227146828252282794090955 15340720242378424191136433)
              ·
                refine ⟨11505540181783818143352325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15340720242378424191136433 11505540181783818143352325)
                ·
                  refine ⟨2157288784084465901878561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11505540181783818143352325 2157288784084465901878561)
                  ·
                    refine ⟨1617966588063349426408921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2157288784084465901878561 1617966588063349426408921)
                    ·
                      refine ⟨1213474941047512069806691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1617966588063349426408921 1213474941047512069806691)
                      ·
                        rfl

theorem cell23_2363234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_2363234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363234 prefixEnd_2363234 := by exact prefixLift 2363234
  have htrace : WordTrace (prefixWord ++ tailWord_2363234) baseStart_2363234 baseEnd_2363234 := by
    simpa [prefixWord, tailWord_2363234, baseEnd_2363234] using wordTrace_append hprefix tailTrace_2363234
  have hstable : (prefixWord ++ tailWord_2363234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363234).length < 2 ^ (prefixWord ++ tailWord_2363234).sum := by decide
  have hdescent : baseEnd_2363234 < baseStart_2363234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363257 : List Nat := [1, 2, 1, 3, 2, 2, 5, 2, 5]
def baseStart_2363257 : Nat := 118140960795 + 2363257 * 2 ^ 59
def prefixEnd_2363257 : Nat := 4983230072969 + 3 ^ 40 * 2363257 * 2
def baseEnd_2363257 : Nat := 134831861233618386646565

theorem tailTrace_2363257 : CollatzResearch.WordTrace tailWord_2363257 prefixEnd_2363257 134831861233618386646565 := by
  unfold tailWord_2363257
  simp only [CollatzResearch.WordTrace]
  refine ⟨86195063999330976007504025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57463375999553984005002683 86195063999330976007504025)
  ·
    refine ⟨64646297999498232005628019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86195063999330976007504025 64646297999498232005628019)
    ·
      refine ⟨96969446999247348008442029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64646297999498232005628019 96969446999247348008442029)
      ·
        refine ⟨36363542624717755503165761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96969446999247348008442029 36363542624717755503165761)
        ·
          refine ⟨27272656968538316627374321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36363542624717755503165761 27272656968538316627374321)
          ·
            refine ⟨20454492726403737470530741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27272656968538316627374321 20454492726403737470530741)
            ·
              refine ⟨1917608693100350387862257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20454492726403737470530741 1917608693100350387862257)
              ·
                refine ⟨1438206519825262790896693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1917608693100350387862257 1438206519825262790896693)
                ·
                  refine ⟨134831861233618386646565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1438206519825262790896693 134831861233618386646565)
                  ·
                    rfl

theorem cell23_2363257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 2, 5].length) (baseStart_2363257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363257 prefixEnd_2363257 := by exact prefixLift 2363257
  have htrace : WordTrace (prefixWord ++ tailWord_2363257) baseStart_2363257 baseEnd_2363257 := by
    simpa [prefixWord, tailWord_2363257, baseEnd_2363257] using wordTrace_append hprefix tailTrace_2363257
  have hstable : (prefixWord ++ tailWord_2363257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363257).length < 2 ^ (prefixWord ++ tailWord_2363257).sum := by decide
  have hdescent : baseEnd_2363257 < baseStart_2363257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363333 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 6]
def baseStart_2363333 : Nat := 118140960795 + 2363333 * 2 ^ 59
def prefixEnd_2363333 : Nat := 4983230072969 + 3 ^ 40 * 2363333 * 2
def baseEnd_2363333 : Nat := 1213525775632307182468735

theorem tailTrace_2363333 : CollatzResearch.WordTrace tailWord_2363333 prefixEnd_2363333 1213525775632307182468735 := by
  unfold tailWord_2363333
  simp only [CollatzResearch.WordTrace]
  refine ⟨86197835947055640987270653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57465223964703760658180435 86197835947055640987270653)
  ·
    refine ⟨32324188480145865370226495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86197835947055640987270653 32324188480145865370226495)
    ·
      refine ⟨48486282720218798055339743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32324188480145865370226495 48486282720218798055339743)
      ·
        refine ⟨72729424080328197083009615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48486282720218798055339743 72729424080328197083009615)
        ·
          refine ⟨109094136120492295624514423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72729424080328197083009615 109094136120492295624514423)
          ·
            refine ⟨163641204180738443436771635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109094136120492295624514423 163641204180738443436771635)
            ·
              refine ⟨245461806271107665155157453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163641204180738443436771635 245461806271107665155157453)
              ·
                refine ⟨92048177351665374433184045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245461806271107665155157453 92048177351665374433184045)
                ·
                  refine ⟨34518066506874515412444017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92048177351665374433184045 34518066506874515412444017)
                  ·
                    refine ⟨25888549880155886559333013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 34518066506874515412444017 25888549880155886559333013)
                    ·
                      refine ⟨1213525775632307182468735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25888549880155886559333013 1213525775632307182468735)
                      ·
                        rfl

theorem cell23_2363333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_2363333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363333 prefixEnd_2363333 := by exact prefixLift 2363333
  have htrace : WordTrace (prefixWord ++ tailWord_2363333) baseStart_2363333 baseEnd_2363333 := by
    simpa [prefixWord, tailWord_2363333, baseEnd_2363333] using wordTrace_append hprefix tailTrace_2363333
  have hstable : (prefixWord ++ tailWord_2363333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363333).length < 2 ^ (prefixWord ++ tailWord_2363333).sum := by decide
  have hdescent : baseEnd_2363333 < baseStart_2363333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363374 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_2363374 : Nat := 118140960795 + 2363374 * 2 ^ 59
def prefixEnd_2363374 : Nat := 4983230072969 + 3 ^ 40 * 2363374 * 2
def baseEnd_2363374 : Nat := 1213546828339141522056047

theorem tailTrace_2363374 : CollatzResearch.WordTrace tailWord_2363374 prefixEnd_2363374 1213546828339141522056047 := by
  unfold tailWord_2363374
  simp only [CollatzResearch.WordTrace]
  refine ⟨10774916417488388123689147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57466220893271403326342117 10774916417488388123689147)
  ·
    refine ⟨16162374626232582185533721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10774916417488388123689147 16162374626232582185533721)
    ·
      refine ⟨12121780969674436639150291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16162374626232582185533721 12121780969674436639150291)
      ·
        refine ⟨18182671454511654958725437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12121780969674436639150291 18182671454511654958725437)
        ·
          refine ⟨6818501795441870609522039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18182671454511654958725437 6818501795441870609522039)
          ·
            refine ⟨10227752693162805914283059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6818501795441870609522039 10227752693162805914283059)
            ·
              refine ⟨15341629039744208871424589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10227752693162805914283059 15341629039744208871424589)
              ·
                refine ⟨5753110889904078326784221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15341629039744208871424589 5753110889904078326784221)
                ·
                  refine ⟨2157416583714029372544083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5753110889904078326784221 2157416583714029372544083)
                  ·
                    refine ⟨3236124875571044058816125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2157416583714029372544083 3236124875571044058816125)
                    ·
                      refine ⟨1213546828339141522056047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3236124875571044058816125 1213546828339141522056047)
                      ·
                        rfl

theorem cell23_2363374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_2363374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363374 prefixEnd_2363374 := by exact prefixLift 2363374
  have htrace : WordTrace (prefixWord ++ tailWord_2363374) baseStart_2363374 baseEnd_2363374 := by
    simpa [prefixWord, tailWord_2363374, baseEnd_2363374] using wordTrace_append hprefix tailTrace_2363374
  have hstable : (prefixWord ++ tailWord_2363374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363374).length < 2 ^ (prefixWord ++ tailWord_2363374).sum := by decide
  have hdescent : baseEnd_2363374 < baseStart_2363374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363397 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 4]
def baseStart_2363397 : Nat := 118140960795 + 2363397 * 2 ^ 59
def prefixEnd_2363397 : Nat := 4983230072969 + 3 ^ 40 * 2363397 * 2
def baseEnd_2363397 : Nat := 1213558638394194932068441

theorem tailTrace_2363397 : CollatzResearch.WordTrace tailWord_2363397 prefixEnd_2363397 1213558638394194932068441 := by
  unfold tailWord_2363397
  simp only [CollatzResearch.WordTrace]
  refine ⟨86200170218823779917600445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57466780145882519945066963 86200170218823779917600445)
  ·
    refine ⟨32325063832058917469100167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86200170218823779917600445 32325063832058917469100167)
    ·
      refine ⟨48487595748088376203650251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32325063832058917469100167 48487595748088376203650251)
      ·
        refine ⟨72731393622132564305475377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48487595748088376203650251 72731393622132564305475377)
        ·
          refine ⟨54548545216599423229106533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72731393622132564305475377 54548545216599423229106533)
          ·
            refine ⟨10227852228112391855457475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54548545216599423229106533 10227852228112391855457475)
            ·
              refine ⟨15341778342168587783186213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10227852228112391855457475 15341778342168587783186213)
              ·
                refine ⟨2876583439156610209347415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15341778342168587783186213 2876583439156610209347415)
                ·
                  refine ⟨4314875158734915314021123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876583439156610209347415 4314875158734915314021123)
                  ·
                    refine ⟨6472312738102372971031685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4314875158734915314021123 6472312738102372971031685)
                    ·
                      refine ⟨1213558638394194932068441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6472312738102372971031685 1213558638394194932068441)
                      ·
                        rfl

theorem cell23_2363397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 1, 4].length) (baseStart_2363397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363397 prefixEnd_2363397 := by exact prefixLift 2363397
  have htrace : WordTrace (prefixWord ++ tailWord_2363397) baseStart_2363397 baseEnd_2363397 := by
    simpa [prefixWord, tailWord_2363397, baseEnd_2363397] using wordTrace_append hprefix tailTrace_2363397
  have hstable : (prefixWord ++ tailWord_2363397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363397).length < 2 ^ (prefixWord ++ tailWord_2363397).sum := by decide
  have hdescent : baseEnd_2363397 < baseStart_2363397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363400 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_2363400 : Nat := 118140960795 + 2363400 * 2 ^ 59
def prefixEnd_2363400 : Nat := 4983230072969 + 3 ^ 40 * 2363400 * 2
def baseEnd_2363400 : Nat := 1213560178836158420330927

theorem tailTrace_2363400 : CollatzResearch.WordTrace tailWord_2363400 prefixEnd_2363400 1213560178836158420330927 := by
  unfold tailWord_2363400
  simp only [CollatzResearch.WordTrace]
  refine ⟨43100139818906455714979827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57466853091875274286639769 43100139818906455714979827)
  ·
    refine ⟨64650209728359683572469741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43100139818906455714979827 64650209728359683572469741)
    ·
      refine ⟨24243828648134881339676153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64650209728359683572469741 24243828648134881339676153)
      ·
        refine ⟨18182871486101161004757115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24243828648134881339676153 18182871486101161004757115)
        ·
          refine ⟨27274307229151741507135673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18182871486101161004757115 27274307229151741507135673)
          ·
            refine ⟨20455730421863806130351755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27274307229151741507135673 20455730421863806130351755)
            ·
              refine ⟨30683595632795709195527633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20455730421863806130351755 30683595632795709195527633)
              ·
                refine ⟨23012696724596781896645725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30683595632795709195527633 23012696724596781896645725)
                ·
                  refine ⟨8629761271723793211242147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23012696724596781896645725 8629761271723793211242147)
                  ·
                    refine ⟨12944641907585689816863221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8629761271723793211242147 12944641907585689816863221)
                    ·
                      refine ⟨1213560178836158420330927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12944641907585689816863221 1213560178836158420330927)
                      ·
                        rfl

theorem cell23_2363400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_2363400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363400 prefixEnd_2363400 := by exact prefixLift 2363400
  have htrace : WordTrace (prefixWord ++ tailWord_2363400) baseStart_2363400 baseEnd_2363400 := by
    simpa [prefixWord, tailWord_2363400, baseEnd_2363400] using wordTrace_append hprefix tailTrace_2363400
  have hstable : (prefixWord ++ tailWord_2363400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363400).length < 2 ^ (prefixWord ++ tailWord_2363400).sum := by decide
  have hdescent : baseEnd_2363400 < baseStart_2363400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363420 : List Nat := [2, 2, 3, 1, 3, 1, 11]
def baseStart_2363420 : Nat := 118140960795 + 2363420 * 2 ^ 59
def prefixEnd_2363420 : Nat := 4983230072969 + 3 ^ 40 * 2363420 * 2
def baseEnd_2363420 : Nat := 14982351215422819038035

theorem tailTrace_2363420 : CollatzResearch.WordTrace tailWord_2363420 prefixEnd_2363420 14982351215422819038035 := by
  unfold tailWord_2363420
  simp only [CollatzResearch.WordTrace]
  refine ⟨43100504548870227422843857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57467339398493636563791809 43100504548870227422843857)
  ·
    refine ⟨32325378411652670567132893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43100504548870227422843857 32325378411652670567132893)
    ·
      refine ⟨12122016904369751462674835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32325378411652670567132893 12122016904369751462674835)
      ·
        refine ⟨18183025356554627194012253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12122016904369751462674835 18183025356554627194012253)
        ·
          refine ⟨6818634508707985197754595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18183025356554627194012253 6818634508707985197754595)
          ·
            refine ⟨10227951763061977796631893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6818634508707985197754595 10227951763061977796631893)
            ·
              refine ⟨14982351215422819038035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10227951763061977796631893 14982351215422819038035)
              ·
                rfl

theorem cell23_2363420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 11].length) (baseStart_2363420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363420 prefixEnd_2363420 := by exact prefixLift 2363420
  have htrace : WordTrace (prefixWord ++ tailWord_2363420) baseStart_2363420 baseEnd_2363420 := by
    simpa [prefixWord, tailWord_2363420, baseEnd_2363420] using wordTrace_append hprefix tailTrace_2363420
  have hstable : (prefixWord ++ tailWord_2363420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363420).length < 2 ^ (prefixWord ++ tailWord_2363420).sum := by decide
  have hdescent : baseEnd_2363420 < baseStart_2363420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363441 : List Nat := [1, 2, 2, 3, 1, 5, 2, 1, 2, 4]
def baseStart_2363441 : Nat := 118140960795 + 2363441 * 2 ^ 59
def prefixEnd_2363441 : Nat := 4983230072969 + 3 ^ 40 * 2363441 * 2
def baseEnd_2363441 : Nat := 404527077180997586639413

theorem tailTrace_2363441 : CollatzResearch.WordTrace tailWord_2363441 prefixEnd_2363441 404527077180997586639413 := by
  unfold tailWord_2363441
  simp only [CollatzResearch.WordTrace]
  refine ⟨86201775030664375432202177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57467850020442916954801451 86201775030664375432202177)
  ·
    refine ⟨64651331272998281574151633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86201775030664375432202177 64651331272998281574151633)
    ·
      refine ⟨48488498454748711180613725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64651331272998281574151633 48488498454748711180613725)
      ·
        refine ⟨18183186920530766692730147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48488498454748711180613725 18183186920530766692730147)
        ·
          refine ⟨27274780380796150039095221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18183186920530766692730147 27274780380796150039095221)
          ·
            refine ⟨2557010660699639066165177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27274780380796150039095221 2557010660699639066165177)
            ·
              refine ⟨1917757995524729299623883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2557010660699639066165177 1917757995524729299623883)
              ·
                refine ⟨2876636993287093949435825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917757995524729299623883 2876636993287093949435825)
                ·
                  refine ⟨2157477744965320462076869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2876636993287093949435825 2157477744965320462076869)
                  ·
                    refine ⟨404527077180997586639413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2157477744965320462076869 404527077180997586639413)
                    ·
                      rfl

theorem cell23_2363441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 2, 1, 2, 4].length) (baseStart_2363441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363441 prefixEnd_2363441 := by exact prefixLift 2363441
  have htrace : WordTrace (prefixWord ++ tailWord_2363441) baseStart_2363441 baseEnd_2363441 := by
    simpa [prefixWord, tailWord_2363441, baseEnd_2363441] using wordTrace_append hprefix tailTrace_2363441
  have hstable : (prefixWord ++ tailWord_2363441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363441).length < 2 ^ (prefixWord ++ tailWord_2363441).sum := by decide
  have hdescent : baseEnd_2363441 < baseStart_2363441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363504 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 1, 4, 2]
def baseStart_2363504 : Nat := 118140960795 + 2363504 * 2 ^ 59
def prefixEnd_2363504 : Nat := 4983230072969 + 3 ^ 40 * 2363504 * 2
def baseEnd_2363504 : Nat := 1213613580824226013430449

theorem tailTrace_2363504 : CollatzResearch.WordTrace tailWord_2363504 prefixEnd_2363504 1213613580824226013430449 := by
  unfold tailWord_2363504
  simp only [CollatzResearch.WordTrace]
  refine ⟨43102036414718068595872783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57469381886290758127830377 43102036414718068595872783)
  ·
    refine ⟨64653054622077102893809175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43102036414718068595872783 64653054622077102893809175)
    ·
      refine ⟨96979581933115654340713763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64653054622077102893809175 96979581933115654340713763)
      ·
        refine ⟨145469372899673481511070645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96979581933115654340713763 145469372899673481511070645)
        ·
          refine ⟨13637753709344388891662873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 145469372899673481511070645 13637753709344388891662873)
          ·
            refine ⟨10228315282008291668747155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13637753709344388891662873 10228315282008291668747155)
            ·
              refine ⟨15342472923012437503120733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10228315282008291668747155 15342472923012437503120733)
              ·
                refine ⟨5753427346129664063670275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15342472923012437503120733 5753427346129664063670275)
                ·
                  refine ⟨8630141019194496095505413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5753427346129664063670275 8630141019194496095505413)
                  ·
                    refine ⟨1618151441098968017907265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8630141019194496095505413 1618151441098968017907265)
                    ·
                      refine ⟨1213613580824226013430449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618151441098968017907265 1213613580824226013430449)
                      ·
                        rfl

theorem cell23_2363504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 4, 2].length) (baseStart_2363504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363504 prefixEnd_2363504 := by exact prefixLift 2363504
  have htrace : WordTrace (prefixWord ++ tailWord_2363504) baseStart_2363504 baseEnd_2363504 := by
    simpa [prefixWord, tailWord_2363504, baseEnd_2363504] using wordTrace_append hprefix tailTrace_2363504
  have hstable : (prefixWord ++ tailWord_2363504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363504).length < 2 ^ (prefixWord ++ tailWord_2363504).sum := by decide
  have hdescent : baseEnd_2363504 < baseStart_2363504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363520 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_2363520 : Nat := 118140960795 + 2363520 * 2 ^ 59
def prefixEnd_2363520 : Nat := 4983230072969 + 3 ^ 40 * 2363520 * 2
def baseEnd_2363520 : Nat := 1213621796514697950830375

theorem tailTrace_2363520 : CollatzResearch.WordTrace tailWord_2363520 prefixEnd_2363520 1213621796514697950830375 := by
  unfold tailWord_2363520
  simp only [CollatzResearch.WordTrace]
  refine ⟨43102328198689085962164007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57469770931585447949552009 43102328198689085962164007)
  ·
    refine ⟨64653492298033628943246011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43102328198689085962164007 64653492298033628943246011)
    ·
      refine ⟨96980238447050443414869017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64653492298033628943246011 96980238447050443414869017)
      ·
        refine ⟨72735178835287832561151763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96980238447050443414869017 72735178835287832561151763)
        ·
          refine ⟨109102768252931748841727645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72735178835287832561151763 109102768252931748841727645)
          ·
            refine ⟨40913538094849405815647867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109102768252931748841727645 40913538094849405815647867)
            ·
              refine ⟨61370307142274108723471801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40913538094849405815647867 61370307142274108723471801)
              ·
                refine ⟨46027730356705581542603851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61370307142274108723471801 46027730356705581542603851)
                ·
                  refine ⟨69041595535058372313905777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46027730356705581542603851 69041595535058372313905777)
                  ·
                    refine ⟨51781196651293779235429333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 69041595535058372313905777 51781196651293779235429333)
                    ·
                      refine ⟨1213621796514697950830375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51781196651293779235429333 1213621796514697950830375)
                      ·
                        rfl

theorem cell23_2363520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_2363520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363520 prefixEnd_2363520 := by exact prefixLift 2363520
  have htrace : WordTrace (prefixWord ++ tailWord_2363520) baseStart_2363520 baseEnd_2363520 := by
    simpa [prefixWord, tailWord_2363520, baseEnd_2363520] using wordTrace_append hprefix tailTrace_2363520
  have hstable : (prefixWord ++ tailWord_2363520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363520).length < 2 ^ (prefixWord ++ tailWord_2363520).sum := by decide
  have hdescent : baseEnd_2363520 < baseStart_2363520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363544 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 7]
def baseStart_2363544 : Nat := 118140960795 + 2363544 * 2 ^ 59
def prefixEnd_2363544 : Nat := 4983230072969 + 3 ^ 40 * 2363544 * 2
def baseEnd_2363544 : Nat := 134848235561156206325585

theorem tailTrace_2363544 : CollatzResearch.WordTrace tailWord_2363544 prefixEnd_2363544 134848235561156206325585 := by
  unfold tailWord_2363544
  simp only [CollatzResearch.WordTrace]
  refine ⟨43102765874645612011600843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57470354499527482682134457 43102765874645612011600843)
  ·
    refine ⟨64654148811968418017401265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43102765874645612011600843 64654148811968418017401265)
    ·
      refine ⟨48490611608976313513050949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64654148811968418017401265 48490611608976313513050949)
      ·
        refine ⟨9091989676683058783697053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48490611608976313513050949 9091989676683058783697053)
        ·
          refine ⟨3409496128756147043886395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9091989676683058783697053 3409496128756147043886395)
          ·
            refine ⟨5114244193134220565829593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3409496128756147043886395 5114244193134220565829593)
            ·
              refine ⟨3835683144850665424372195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5114244193134220565829593 3835683144850665424372195)
              ·
                refine ⟨5753524717275998136558293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3835683144850665424372195 5753524717275998136558293)
                ·
                  refine ⟨134848235561156206325585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5753524717275998136558293 134848235561156206325585)
                  ·
                    rfl

theorem cell23_2363544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 7].length) (baseStart_2363544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363544 prefixEnd_2363544 := by exact prefixLift 2363544
  have htrace : WordTrace (prefixWord ++ tailWord_2363544) baseStart_2363544 baseEnd_2363544 := by
    simpa [prefixWord, tailWord_2363544, baseEnd_2363544] using wordTrace_append hprefix tailTrace_2363544
  have hstable : (prefixWord ++ tailWord_2363544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363544).length < 2 ^ (prefixWord ++ tailWord_2363544).sum := by decide
  have hdescent : baseEnd_2363544 < baseStart_2363544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363577 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2363577 : Nat := 118140960795 + 2363577 * 2 ^ 59
def prefixEnd_2363577 : Nat := 4983230072969 + 3 ^ 40 * 2363577 * 2
def baseEnd_2363577 : Nat := 1213651064912004227817613

theorem tailTrace_2363577 : CollatzResearch.WordTrace tailWord_2363577 prefixEnd_2363577 1213651064912004227817613 := by
  unfold tailWord_2363577
  simp only [CollatzResearch.WordTrace]
  refine ⟨86206735358171670659152985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57471156905447780439435323 86206735358171670659152985)
  ·
    refine ⟨64655051518628752994364739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86206735358171670659152985 64655051518628752994364739)
    ·
      refine ⟨96982577277943129491547109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64655051518628752994364739 96982577277943129491547109)
      ·
        refine ⟨18184233239614336779665083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96982577277943129491547109 18184233239614336779665083)
        ·
          refine ⟨27276349859421505169497625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18184233239614336779665083 27276349859421505169497625)
          ·
            refine ⟨20457262394566128877123219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27276349859421505169497625 20457262394566128877123219)
            ·
              refine ⟨30685893591849193315684829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20457262394566128877123219 30685893591849193315684829)
              ·
                refine ⟨11507210096943447493381811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30685893591849193315684829 11507210096943447493381811)
                ·
                  refine ⟨17260815145415171240072717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11507210096943447493381811 17260815145415171240072717)
                  ·
                    refine ⟨6472805679530689215027269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17260815145415171240072717 6472805679530689215027269)
                    ·
                      refine ⟨1213651064912004227817613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6472805679530689215027269 1213651064912004227817613)
                      ·
                        rfl

theorem cell23_2363577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2363577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363577 prefixEnd_2363577 := by exact prefixLift 2363577
  have htrace : WordTrace (prefixWord ++ tailWord_2363577) baseStart_2363577 baseEnd_2363577 := by
    simpa [prefixWord, tailWord_2363577, baseEnd_2363577] using wordTrace_append hprefix tailTrace_2363577
  have hstable : (prefixWord ++ tailWord_2363577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363577).length < 2 ^ (prefixWord ++ tailWord_2363577).sum := by decide
  have hdescent : baseEnd_2363577 < baseStart_2363577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363594 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_2363594 : Nat := 118140960795 + 2363594 * 2 ^ 59
def prefixEnd_2363594 : Nat := 4983230072969 + 3 ^ 40 * 2363594 * 2
def baseEnd_2363594 : Nat := 1213659794083130661305035

theorem tailTrace_2363594 : CollatzResearch.WordTrace tailWord_2363594 prefixEnd_2363594 1213659794083130661305035 := by
  unfold tailWord_2363594
  simp only [CollatzResearch.WordTrace]
  refine ⟨21551838849777520640630459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57471570266073388375014557 21551838849777520640630459)
  ·
    refine ⟨32327758274666280960945689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21551838849777520640630459 32327758274666280960945689)
    ·
      refine ⟨24245818705999710720709267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32327758274666280960945689 24245818705999710720709267)
      ·
        refine ⟨36368728058999566081063901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24245818705999710720709267 36368728058999566081063901)
        ·
          refine ⟨13638273022124837280398963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36368728058999566081063901 13638273022124837280398963)
          ·
            refine ⟨20457409533187255920598445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13638273022124837280398963 20457409533187255920598445)
            ·
              refine ⟨7671528574945220970224417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20457409533187255920598445 7671528574945220970224417)
              ·
                refine ⟨5753646431208915727668313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7671528574945220970224417 5753646431208915727668313)
                ·
                  refine ⟨4315234823406686795751235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5753646431208915727668313 4315234823406686795751235)
                  ·
                    refine ⟨6472852235110030193626853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4315234823406686795751235 6472852235110030193626853)
                    ·
                      refine ⟨1213659794083130661305035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6472852235110030193626853 1213659794083130661305035)
                      ·
                        rfl

theorem cell23_2363594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_2363594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363594 prefixEnd_2363594 := by exact prefixLift 2363594
  have htrace : WordTrace (prefixWord ++ tailWord_2363594) baseStart_2363594 baseEnd_2363594 := by
    simpa [prefixWord, tailWord_2363594, baseEnd_2363594] using wordTrace_append hprefix tailTrace_2363594
  have hstable : (prefixWord ++ tailWord_2363594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363594).length < 2 ^ (prefixWord ++ tailWord_2363594).sum := by decide
  have hdescent : baseEnd_2363594 < baseStart_2363594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363631 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 3]
def baseStart_2363631 : Nat := 118140960795 + 2363631 * 2 ^ 59
def prefixEnd_2363631 : Nat := 4983230072969 + 3 ^ 40 * 2363631 * 2
def baseEnd_2363631 : Nat := 1213678792867347016542365

theorem tailTrace_2363631 : CollatzResearch.WordTrace tailWord_2363631 prefixEnd_2363631 1213678792867347016542365 := by
  unfold tailWord_2363631
  simp only [CollatzResearch.WordTrace]
  refine ⟨86208704899976037881618747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57472469933317358587745831 86208704899976037881618747)
  ·
    refine ⟨129313057349964056822428121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86208704899976037881618747 129313057349964056822428121)
    ·
      refine ⟨96984793012473042616821091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129313057349964056822428121 96984793012473042616821091)
      ·
        refine ⟨145477189518709563925231637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96984793012473042616821091 145477189518709563925231637)
        ·
          refine ⟨6819243258689510808995233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145477189518709563925231637 6819243258689510808995233)
          ·
            refine ⟨5114432444017133106746425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6819243258689510808995233 5114432444017133106746425)
            ·
              refine ⟨3835824333012849830059819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5114432444017133106746425 3835824333012849830059819)
              ·
                refine ⟨5753736499519274745089729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3835824333012849830059819 5753736499519274745089729)
                ·
                  refine ⟨4315302374639456058817297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5753736499519274745089729 4315302374639456058817297)
                  ·
                    refine ⟨3236476780979592044112973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4315302374639456058817297 3236476780979592044112973)
                    ·
                      refine ⟨1213678792867347016542365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3236476780979592044112973 1213678792867347016542365)
                      ·
                        rfl

theorem cell23_2363631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 2, 3].length) (baseStart_2363631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363631 prefixEnd_2363631 := by exact prefixLift 2363631
  have htrace : WordTrace (prefixWord ++ tailWord_2363631) baseStart_2363631 baseEnd_2363631 := by
    simpa [prefixWord, tailWord_2363631, baseEnd_2363631] using wordTrace_append hprefix tailTrace_2363631
  have hstable : (prefixWord ++ tailWord_2363631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363631).length < 2 ^ (prefixWord ++ tailWord_2363631).sum := by decide
  have hdescent : baseEnd_2363631 < baseStart_2363631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363655 : List Nat := [1, 1, 4, 5, 1, 1, 1, 4, 1, 4]
def baseStart_2363655 : Nat := 118140960795 + 2363655 * 2 ^ 59
def prefixEnd_2363655 : Nat := 4983230072969 + 3 ^ 40 * 2363655 * 2
def baseEnd_2363655 : Nat := 404563705467684974214085

theorem tailTrace_2363655 : CollatzResearch.WordTrace tailWord_2363655 prefixEnd_2363655 404563705467684974214085 := by
  unfold tailWord_2363655
  simp only [CollatzResearch.WordTrace]
  refine ⟨86209580251889089980492419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57473053501259393320328279 86209580251889089980492419)
  ·
    refine ⟨129314370377833634970738629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86209580251889089980492419 129314370377833634970738629)
    ·
      refine ⟨24246444445843806557013493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129314370377833634970738629 24246444445843806557013493)
      ·
        refine ⟨2273104166797856864720015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24246444445843806557013493 2273104166797856864720015)
        ·
          refine ⟨3409656250196785297080023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273104166797856864720015 3409656250196785297080023)
          ·
            refine ⟨5114484375295177945620035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3409656250196785297080023 5114484375295177945620035)
            ·
              refine ⟨7671726562942766918430053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114484375295177945620035 7671726562942766918430053)
              ·
                refine ⟨1438448730551768797205635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7671726562942766918430053 1438448730551768797205635)
                ·
                  refine ⟨2157673095827653195808453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438448730551768797205635 2157673095827653195808453)
                  ·
                    refine ⟨404563705467684974214085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2157673095827653195808453 404563705467684974214085)
                    ·
                      rfl

theorem cell23_2363655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_2363655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363655 prefixEnd_2363655 := by exact prefixLift 2363655
  have htrace : WordTrace (prefixWord ++ tailWord_2363655) baseStart_2363655 baseEnd_2363655 := by
    simpa [prefixWord, tailWord_2363655, baseEnd_2363655] using wordTrace_append hprefix tailTrace_2363655
  have hstable : (prefixWord ++ tailWord_2363655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363655).length < 2 ^ (prefixWord ++ tailWord_2363655).sum := by decide
  have hdescent : baseEnd_2363655 < baseStart_2363655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363688 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_2363688 : Nat := 118140960795 + 2363688 * 2 ^ 59
def prefixEnd_2363688 : Nat := 4983230072969 + 3 ^ 40 * 2363688 * 2
def baseEnd_2363688 : Nat := 1213708061264653293529603

theorem tailTrace_2363688 : CollatzResearch.WordTrace tailWord_2363688 prefixEnd_2363688 1213708061264653293529603 := by
  unfold tailWord_2363688
  simp only [CollatzResearch.WordTrace]
  refine ⟨43105391930384768308221859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57473855907179691077629145 43105391930384768308221859)
  ·
    refine ⟨64658087895577152462332789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43105391930384768308221859 64658087895577152462332789)
    ·
      refine ⟨6061695740210358043343699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64658087895577152462332789 6061695740210358043343699)
      ·
        refine ⟨9092543610315537065015549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6061695740210358043343699 9092543610315537065015549)
        ·
          refine ⟨3409703853868326399380831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9092543610315537065015549 3409703853868326399380831)
          ·
            refine ⟨5114555780802489599071247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3409703853868326399380831 5114555780802489599071247)
            ·
              refine ⟨7671833671203734398606871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114555780802489599071247 7671833671203734398606871)
              ·
                refine ⟨11507750506805601597910307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7671833671203734398606871 11507750506805601597910307)
                ·
                  refine ⟨17261625760208402396865461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11507750506805601597910307 17261625760208402396865461)
                  ·
                    refine ⟨1618277415019537724706137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17261625760208402396865461 1618277415019537724706137)
                    ·
                      refine ⟨1213708061264653293529603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618277415019537724706137 1213708061264653293529603)
                      ·
                        rfl

theorem cell23_2363688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_2363688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363688 prefixEnd_2363688 := by exact prefixLift 2363688
  have htrace : WordTrace (prefixWord ++ tailWord_2363688) baseStart_2363688 baseEnd_2363688 := by
    simpa [prefixWord, tailWord_2363688, baseEnd_2363688] using wordTrace_append hprefix tailTrace_2363688
  have hstable : (prefixWord ++ tailWord_2363688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363688).length < 2 ^ (prefixWord ++ tailWord_2363688).sum := by decide
  have hdescent : baseEnd_2363688 < baseStart_2363688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363701 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 4]
def baseStart_2363701 : Nat := 118140960795 + 2363701 * 2 ^ 59
def prefixEnd_2363701 : Nat := 4983230072969 + 3 ^ 40 * 2363701 * 2
def baseEnd_2363701 : Nat := 1213714736513161742667043

theorem tailTrace_2363701 : CollatzResearch.WordTrace tailWord_2363701 prefixEnd_2363701 1213714736513161742667043 := by
  unfold tailWord_2363701
  simp only [CollatzResearch.WordTrace]
  refine ⟨86211258009722439836666957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57474172006481626557777971 86211258009722439836666957)
  ·
    refine ⟨32329221753645914938750109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86211258009722439836666957 32329221753645914938750109)
    ·
      refine ⟨12123458157617218102031291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32329221753645914938750109 12123458157617218102031291)
      ·
        refine ⟨18185187236425827153046937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12123458157617218102031291 18185187236425827153046937)
        ·
          refine ⟨13638890427319370364785203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18185187236425827153046937 13638890427319370364785203)
          ·
            refine ⟨20458335640979055547177805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13638890427319370364785203 20458335640979055547177805)
            ·
              refine ⟨7671875865367145830191677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20458335640979055547177805 7671875865367145830191677)
              ·
                refine ⟨2876953449512679686321879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7671875865367145830191677 2876953449512679686321879)
                ·
                  refine ⟨4315430174269019529482819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2876953449512679686321879 4315430174269019529482819)
                  ·
                    refine ⟨6473145261403529294224229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4315430174269019529482819 6473145261403529294224229)
                    ·
                      refine ⟨1213714736513161742667043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6473145261403529294224229 1213714736513161742667043)
                      ·
                        rfl

theorem cell23_2363701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_2363701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363701 prefixEnd_2363701 := by exact prefixLift 2363701
  have htrace : WordTrace (prefixWord ++ tailWord_2363701) baseStart_2363701 baseEnd_2363701 := by
    simpa [prefixWord, tailWord_2363701, baseEnd_2363701] using wordTrace_append hprefix tailTrace_2363701
  have hstable : (prefixWord ++ tailWord_2363701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363701).length < 2 ^ (prefixWord ++ tailWord_2363701).sum := by decide
  have hdescent : baseEnd_2363701 < baseStart_2363701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363717 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 7]
def baseStart_2363717 : Nat := 118140960795 + 2363717 * 2 ^ 59
def prefixEnd_2363717 : Nat := 4983230072969 + 3 ^ 40 * 2363717 * 2
def baseEnd_2363717 : Nat := 1213722952203633680066969

theorem tailTrace_2363717 : CollatzResearch.WordTrace tailWord_2363717 prefixEnd_2363717 1213722952203633680066969 := by
  unfold tailWord_2363717
  simp only [CollatzResearch.WordTrace]
  refine ⟨86211841577664474569249405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57474561051776316379499603 86211841577664474569249405)
  ·
    refine ⟨32329440591624177963468527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86211841577664474569249405 32329440591624177963468527)
    ·
      refine ⟨48494160887436266945202791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32329440591624177963468527 48494160887436266945202791)
      ·
        refine ⟨72741241331154400417804187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48494160887436266945202791 72741241331154400417804187)
        ·
          refine ⟨109111861996731600626706281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72741241331154400417804187 109111861996731600626706281)
          ·
            refine ⟨81833896497548700470029711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109111861996731600626706281 81833896497548700470029711)
            ·
              refine ⟨122750844746323050705044567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81833896497548700470029711 122750844746323050705044567)
              ·
                refine ⟨184126267119484576057566851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122750844746323050705044567 184126267119484576057566851)
                ·
                  refine ⟨276189400679226864086350277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184126267119484576057566851 276189400679226864086350277)
                  ·
                    refine ⟨51785512627355037016190677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 276189400679226864086350277 51785512627355037016190677)
                    ·
                      refine ⟨1213722952203633680066969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51785512627355037016190677 1213722952203633680066969)
                      ·
                        rfl

theorem cell23_2363717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_2363717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363717 prefixEnd_2363717 := by exact prefixLift 2363717
  have htrace : WordTrace (prefixWord ++ tailWord_2363717) baseStart_2363717 baseEnd_2363717 := by
    simpa [prefixWord, tailWord_2363717, baseEnd_2363717] using wordTrace_append hprefix tailTrace_2363717
  have hstable : (prefixWord ++ tailWord_2363717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363717).length < 2 ^ (prefixWord ++ tailWord_2363717).sum := by decide
  have hdescent : baseEnd_2363717 < baseStart_2363717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363727 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_2363727 : Nat := 118140960795 + 2363727 * 2 ^ 59
def prefixEnd_2363727 : Nat := 4983230072969 + 3 ^ 40 * 2363727 * 2
def baseEnd_2363727 : Nat := 1213728087010178640941923

theorem tailTrace_2363727 : CollatzResearch.WordTrace tailWord_2363727 prefixEnd_2363727 1213728087010178640941923 := by
  unfold tailWord_2363727
  simp only [CollatzResearch.WordTrace]
  refine ⟨86212206307628246277113435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57474804205085497518075623 86212206307628246277113435)
  ·
    refine ⟨129318309461442369415670153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86212206307628246277113435 129318309461442369415670153)
    ·
      refine ⟨96988732096081777061752615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129318309461442369415670153 96988732096081777061752615)
      ·
        refine ⟨145483098144122665592628923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96988732096081777061752615 145483098144122665592628923)
        ·
          refine ⟨218224647216183998388943385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145483098144122665592628923 218224647216183998388943385)
          ·
            refine ⟨163668485412137998791707539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218224647216183998388943385 163668485412137998791707539)
            ·
              refine ⟨245502728118206998187561309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163668485412137998791707539 245502728118206998187561309)
              ·
                refine ⟨92063523044327624320335491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 245502728118206998187561309 92063523044327624320335491)
                ·
                  refine ⟨138095284566491436480503237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92063523044327624320335491 138095284566491436480503237)
                  ·
                    refine ⟨25892865856217144340094357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 138095284566491436480503237 25892865856217144340094357)
                    ·
                      refine ⟨1213728087010178640941923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25892865856217144340094357 1213728087010178640941923)
                      ·
                        rfl

theorem cell23_2363727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_2363727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363727 prefixEnd_2363727 := by exact prefixLift 2363727
  have htrace : WordTrace (prefixWord ++ tailWord_2363727) baseStart_2363727 baseEnd_2363727 := by
    simpa [prefixWord, tailWord_2363727, baseEnd_2363727] using wordTrace_append hprefix tailTrace_2363727
  have hstable : (prefixWord ++ tailWord_2363727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363727).length < 2 ^ (prefixWord ++ tailWord_2363727).sum := by decide
  have hdescent : baseEnd_2363727 < baseStart_2363727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363728 : List Nat := [2, 1, 1, 1, 1, 7, 3, 1, 2, 4]
def baseStart_2363728 : Nat := 118140960795 + 2363728 * 2 ^ 59
def prefixEnd_2363728 : Nat := 4983230072969 + 3 ^ 40 * 2363728 * 2
def baseEnd_2363728 : Nat := 404576200163611045676473

theorem tailTrace_2363728 : CollatzResearch.WordTrace tailWord_2363728 prefixEnd_2363728 404576200163611045676473 := by
  unfold tailWord_2363728
  simp only [CollatzResearch.WordTrace]
  refine ⟨43106121390312311723949919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57474828520416415631933225 43106121390312311723949919)
  ·
    refine ⟨64659182085468467585924879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43106121390312311723949919 64659182085468467585924879)
    ·
      refine ⟨96988773128202701378887319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64659182085468467585924879 96988773128202701378887319)
      ·
        refine ⟨145483159692304052068330979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96988773128202701378887319 145483159692304052068330979)
        ·
          refine ⟨218224739538456078102496469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145483159692304052068330979 218224739538456078102496469)
          ·
            refine ⟨5114642332932564330527261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 218224739538456078102496469 5114642332932564330527261)
            ·
              refine ⟨1917990874849711623947723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5114642332932564330527261 1917990874849711623947723)
              ·
                refine ⟨2876986312274567435921585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917990874849711623947723 2876986312274567435921585)
                ·
                  refine ⟨2157739734205925576941189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2876986312274567435921585 2157739734205925576941189)
                  ·
                    refine ⟨404576200163611045676473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2157739734205925576941189 404576200163611045676473)
                    ·
                      rfl

theorem cell23_2363728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 3, 1, 2, 4].length) (baseStart_2363728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363728 prefixEnd_2363728 := by exact prefixLift 2363728
  have htrace : WordTrace (prefixWord ++ tailWord_2363728) baseStart_2363728 baseEnd_2363728 := by
    simpa [prefixWord, tailWord_2363728, baseEnd_2363728] using wordTrace_append hprefix tailTrace_2363728
  have hstable : (prefixWord ++ tailWord_2363728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363728).length < 2 ^ (prefixWord ++ tailWord_2363728).sum := by decide
  have hdescent : baseEnd_2363728 < baseStart_2363728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363752 : List Nat := [2, 1, 4, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_2363752 : Nat := 118140960795 + 2363752 * 2 ^ 59
def prefixEnd_2363752 : Nat := 4983230072969 + 3 ^ 40 * 2363752 * 2
def baseEnd_2363752 : Nat := 1213740924026541043129309

theorem tailTrace_2363752 : CollatzResearch.WordTrace tailWord_2363752 prefixEnd_2363752 1213740924026541043129309 := by
  unfold tailWord_2363752
  simp only [CollatzResearch.WordTrace]
  refine ⟨43106559066268837773386755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57475412088358450364515673 43106559066268837773386755)
  ·
    refine ⟨64659838599403256660080133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43106559066268837773386755 64659838599403256660080133)
    ·
      refine ⟨12123719737388110623765025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64659838599403256660080133 12123719737388110623765025)
      ·
        refine ⟨9092789803041082967823769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12123719737388110623765025 9092789803041082967823769)
        ·
          refine ⟨6819592352280812225867827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9092789803041082967823769 6819592352280812225867827)
          ·
            refine ⟨10229388528421218338801741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6819592352280812225867827 10229388528421218338801741)
            ·
              refine ⟨3836020698157956877050653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10229388528421218338801741 3836020698157956877050653)
              ·
                refine ⟨1438507761809233828893995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3836020698157956877050653 1438507761809233828893995)
                ·
                  refine ⟨2157761642713850743340993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438507761809233828893995 2157761642713850743340993)
                  ·
                    refine ⟨1618321232035388057505745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2157761642713850743340993 1618321232035388057505745)
                    ·
                      refine ⟨1213740924026541043129309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618321232035388057505745 1213740924026541043129309)
                      ·
                        rfl

theorem cell23_2363752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_2363752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363752 prefixEnd_2363752 := by exact prefixLift 2363752
  have htrace : WordTrace (prefixWord ++ tailWord_2363752) baseStart_2363752 baseEnd_2363752 := by
    simpa [prefixWord, tailWord_2363752, baseEnd_2363752] using wordTrace_append hprefix tailTrace_2363752
  have hstable : (prefixWord ++ tailWord_2363752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363752).length < 2 ^ (prefixWord ++ tailWord_2363752).sum := by decide
  have hdescent : baseEnd_2363752 < baseStart_2363752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363761 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 5, 3, 2]
def baseStart_2363761 : Nat := 118140960795 + 2363761 * 2 ^ 59
def prefixEnd_2363761 : Nat := 4983230072969 + 3 ^ 40 * 2363761 * 2
def baseEnd_2363761 : Nat := 1213745545352431507916767

theorem tailTrace_2363761 : CollatzResearch.WordTrace tailWord_2363761 prefixEnd_2363761 1213745545352431507916767 := by
  unfold tailWord_2363761
  simp only [CollatzResearch.WordTrace]
  refine ⟨86213446389505070083851137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57475630926336713389234091 86213446389505070083851137)
  ·
    refine ⟨64660084792128802562888353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86213446389505070083851137 64660084792128802562888353)
    ·
      refine ⟨48495063594096601922166265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64660084792128802562888353 48495063594096601922166265)
      ·
        refine ⟨36371297695572451441624699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48495063594096601922166265 36371297695572451441624699)
        ·
          refine ⟨54556946543358677162437049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36371297695572451441624699 54556946543358677162437049)
          ·
            refine ⟨40917709907519007871827787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54556946543358677162437049 40917709907519007871827787)
            ·
              refine ⟨61376564861278511807741681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40917709907519007871827787 61376564861278511807741681)
              ·
                refine ⟨46032423645958883855806261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61376564861278511807741681 46032423645958883855806261)
                ·
                  refine ⟨4315539716808645361481837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46032423645958883855806261 4315539716808645361481837)
                  ·
                    refine ⟨1618327393803242010555689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4315539716808645361481837 1618327393803242010555689)
                    ·
                      refine ⟨1213745545352431507916767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618327393803242010555689 1213745545352431507916767)
                      ·
                        rfl

theorem cell23_2363761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_2363761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363761 prefixEnd_2363761 := by exact prefixLift 2363761
  have htrace : WordTrace (prefixWord ++ tailWord_2363761) baseStart_2363761 baseEnd_2363761 := by
    simpa [prefixWord, tailWord_2363761, baseEnd_2363761] using wordTrace_append hprefix tailTrace_2363761
  have hstable : (prefixWord ++ tailWord_2363761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363761).length < 2 ^ (prefixWord ++ tailWord_2363761).sum := by decide
  have hdescent : baseEnd_2363761 < baseStart_2363761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363784 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 1, 8]
def baseStart_2363784 : Nat := 118140960795 + 2363784 * 2 ^ 59
def prefixEnd_2363784 : Nat := 4983230072969 + 3 ^ 40 * 2363784 * 2
def baseEnd_2363784 : Nat := 404585785135828305976387

theorem tailTrace_2363784 : CollatzResearch.WordTrace tailWord_2363784 prefixEnd_2363784 404585785135828305976387 := by
  unfold tailWord_2363784
  simp only [CollatzResearch.WordTrace]
  refine ⟨43107142634210872505969203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57476190178947830007958937 43107142634210872505969203)
  ·
    refine ⟨64660713951316308758953805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43107142634210872505969203 64660713951316308758953805)
    ·
      refine ⟨24247767731743615784607677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64660713951316308758953805 24247767731743615784607677)
      ·
        refine ⟨9092912899403855919227879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24247767731743615784607677 9092912899403855919227879)
        ·
          refine ⟨13639369349105783878841819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9092912899403855919227879 13639369349105783878841819)
          ·
            refine ⟨20459054023658675818262729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13639369349105783878841819 20459054023658675818262729)
            ·
              refine ⟨15344290517744006863697047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20459054023658675818262729 15344290517744006863697047)
              ·
                refine ⟨23016435776616010295545571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15344290517744006863697047 23016435776616010295545571)
                ·
                  refine ⟨34524653664924015443318357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23016435776616010295545571 34524653664924015443318357)
                  ·
                    refine ⟨404585785135828305976387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 34524653664924015443318357 404585785135828305976387)
                    ·
                      rfl

theorem cell23_2363784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_2363784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363784 prefixEnd_2363784 := by exact prefixLift 2363784
  have htrace : WordTrace (prefixWord ++ tailWord_2363784) baseStart_2363784 baseEnd_2363784 := by
    simpa [prefixWord, tailWord_2363784, baseEnd_2363784] using wordTrace_append hprefix tailTrace_2363784
  have hstable : (prefixWord ++ tailWord_2363784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363784).length < 2 ^ (prefixWord ++ tailWord_2363784).sum := by decide
  have hdescent : baseEnd_2363784 < baseStart_2363784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363785 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 2, 1, 3]
def baseStart_2363785 : Nat := 118140960795 + 2363785 * 2 ^ 59
def prefixEnd_2363785 : Nat := 4983230072969 + 3 ^ 40 * 2363785 * 2
def baseEnd_2363785 : Nat := 1213757868888139414016657

theorem tailTrace_2363785 : CollatzResearch.WordTrace tailWord_2363785 prefixEnd_2363785 1213757868888139414016657 := by
  unfold tailWord_2363785
  simp only [CollatzResearch.WordTrace]
  refine ⟨86214321741418122182724809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57476214494278748121816539 86214321741418122182724809)
  ·
    refine ⟨64660741306063591637043607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86214321741418122182724809 64660741306063591637043607)
    ·
      refine ⟨96991111959095387455565411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64660741306063591637043607 96991111959095387455565411)
      ·
        refine ⟨145486667938643081183348117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96991111959095387455565411 145486667938643081183348117)
        ·
          refine ⟨6819687559623894430469443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 145486667938643081183348117 6819687559623894430469443)
          ·
            refine ⟨10229531339435841645704165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6819687559623894430469443 10229531339435841645704165)
            ·
              refine ⟨1918037126144220308569531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10229531339435841645704165 1918037126144220308569531)
              ·
                refine ⟨2877055689216330462854297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918037126144220308569531 2877055689216330462854297)
                ·
                  refine ⟨2157791766912247847140723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2877055689216330462854297 2157791766912247847140723)
                  ·
                    refine ⟨3236687650368371770711085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2157791766912247847140723 3236687650368371770711085)
                    ·
                      refine ⟨1213757868888139414016657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3236687650368371770711085 1213757868888139414016657)
                      ·
                        rfl

theorem cell23_2363785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 2, 1, 3].length) (baseStart_2363785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363785 prefixEnd_2363785 := by exact prefixLift 2363785
  have htrace : WordTrace (prefixWord ++ tailWord_2363785) baseStart_2363785 baseEnd_2363785 := by
    simpa [prefixWord, tailWord_2363785, baseEnd_2363785] using wordTrace_append hprefix tailTrace_2363785
  have hstable : (prefixWord ++ tailWord_2363785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363785).length < 2 ^ (prefixWord ++ tailWord_2363785).sum := by decide
  have hdescent : baseEnd_2363785 < baseStart_2363785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363808 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 1, 4, 2]
def baseStart_2363808 : Nat := 118140960795 + 2363808 * 2 ^ 59
def prefixEnd_2363808 : Nat := 4983230072969 + 3 ^ 40 * 2363808 * 2
def baseEnd_2363808 : Nat := 1213769678943192824029051

theorem tailTrace_2363808 : CollatzResearch.WordTrace tailWord_2363808 prefixEnd_2363808 1213769678943192824029051 := by
  unfold tailWord_2363808
  simp only [CollatzResearch.WordTrace]
  refine ⟨43107580310167398555406039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57476773746889864740541385 43107580310167398555406039)
  ·
    refine ⟨64661370465251097833109059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43107580310167398555406039 64661370465251097833109059)
    ·
      refine ⟨96992055697876646749663589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64661370465251097833109059 96992055697876646749663589)
      ·
        refine ⟨18186010443351871265561923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96992055697876646749663589 18186010443351871265561923)
        ·
          refine ⟨27279015665027806898342885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18186010443351871265561923 27279015665027806898342885)
          ·
            refine ⟨5114815437192713793439291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27279015665027806898342885 5114815437192713793439291)
            ·
              refine ⟨7672223155789070690158937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114815437192713793439291 7672223155789070690158937)
              ·
                refine ⟨5754167366841803017619203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7672223155789070690158937 5754167366841803017619203)
                ·
                  refine ⟨8631251050262704526428805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5754167366841803017619203 8631251050262704526428805)
                  ·
                    refine ⟨1618359571924257098705401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8631251050262704526428805 1618359571924257098705401)
                    ·
                      refine ⟨1213769678943192824029051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618359571924257098705401 1213769678943192824029051)
                      ·
                        rfl

theorem cell23_2363808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_2363808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363808 prefixEnd_2363808 := by exact prefixLift 2363808
  have htrace : WordTrace (prefixWord ++ tailWord_2363808) baseStart_2363808 baseEnd_2363808 := by
    simpa [prefixWord, tailWord_2363808, baseEnd_2363808] using wordTrace_append hprefix tailTrace_2363808
  have hstable : (prefixWord ++ tailWord_2363808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363808).length < 2 ^ (prefixWord ++ tailWord_2363808).sum := by decide
  have hdescent : baseEnd_2363808 < baseStart_2363808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363825 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 2, 2, 2]
def baseStart_2363825 : Nat := 118140960795 + 2363825 * 2 ^ 59
def prefixEnd_2363825 : Nat := 4983230072969 + 3 ^ 40 * 2363825 * 2
def baseEnd_2363825 : Nat := 1213778408114319257516473

theorem tailTrace_2363825 : CollatzResearch.WordTrace tailWord_2363825 prefixEnd_2363825 1213778408114319257516473 := by
  unfold tailWord_2363825
  simp only [CollatzResearch.WordTrace]
  refine ⟨86215780661273209014180929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57477187107515472676120619 86215780661273209014180929)
  ·
    refine ⟨64661835495954906760635697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86215780661273209014180929 64661835495954906760635697)
    ·
      refine ⟨48496376621966180070476773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64661835495954906760635697 48496376621966180070476773)
      ·
        refine ⟨9093070616618658763214395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48496376621966180070476773 9093070616618658763214395)
        ·
          refine ⟨13639605924927988144821593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9093070616618658763214395 13639605924927988144821593)
          ·
            refine ⟨10229704443695991108616195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13639605924927988144821593 10229704443695991108616195)
            ·
              refine ⟨15344556665543986662924293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10229704443695991108616195 15344556665543986662924293)
              ·
                refine ⟨2877104374789497499298305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15344556665543986662924293 2877104374789497499298305)
                ·
                  refine ⟨2157828281092123124473729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2877104374789497499298305 2157828281092123124473729)
                  ·
                    refine ⟨1618371210819092343355297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2157828281092123124473729 1618371210819092343355297)
                    ·
                      refine ⟨1213778408114319257516473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618371210819092343355297 1213778408114319257516473)
                      ·
                        rfl

theorem cell23_2363825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_2363825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363825 prefixEnd_2363825 := by exact prefixLift 2363825
  have htrace : WordTrace (prefixWord ++ tailWord_2363825) baseStart_2363825 baseEnd_2363825 := by
    simpa [prefixWord, tailWord_2363825, baseEnd_2363825] using wordTrace_append hprefix tailTrace_2363825
  have hstable : (prefixWord ++ tailWord_2363825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363825).length < 2 ^ (prefixWord ++ tailWord_2363825).sum := by decide
  have hdescent : baseEnd_2363825 < baseStart_2363825 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363851 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 4, 5, 2]
def baseStart_2363851 : Nat := 118140960795 + 2363851 * 2 ^ 59
def prefixEnd_2363851 : Nat := 4983230072969 + 3 ^ 40 * 2363851 * 2
def baseEnd_2363851 : Nat := 1213791758611336155791353

theorem tailTrace_2363851 : CollatzResearch.WordTrace tailWord_2363851 prefixEnd_2363851 1213791758611336155791353 := by
  unfold tailWord_2363851
  simp only [CollatzResearch.WordTrace]
  refine ⟨86216728959179015454627407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57477819306119343636418271 86216728959179015454627407)
  ·
    refine ⟨129325093438768523181941111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86216728959179015454627407 129325093438768523181941111)
    ·
      refine ⟨193987640158152784772911667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129325093438768523181941111 193987640158152784772911667)
      ·
        refine ⟨290981460237229177159367501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193987640158152784772911667 290981460237229177159367501)
        ·
          refine ⟨109118047588960941434762813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 290981460237229177159367501 109118047588960941434762813)
          ·
            refine ⟨40919267845860353038036055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109118047588960941434762813 40919267845860353038036055)
            ·
              refine ⟨61378901768790529557054083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40919267845860353038036055 61378901768790529557054083)
              ·
                refine ⟨92068352653185794335581125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61378901768790529557054083 92068352653185794335581125)
                ·
                  refine ⟨17262816122472336437921461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92068352653185794335581125 17262816122472336437921461)
                  ·
                    refine ⟨1618389011481781541055137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17262816122472336437921461 1618389011481781541055137)
                    ·
                      refine ⟨1213791758611336155791353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618389011481781541055137 1213791758611336155791353)
                      ·
                        rfl

theorem cell23_2363851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 5, 2].length) (baseStart_2363851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363851 prefixEnd_2363851 := by exact prefixLift 2363851
  have htrace : WordTrace (prefixWord ++ tailWord_2363851) baseStart_2363851 baseEnd_2363851 := by
    simpa [prefixWord, tailWord_2363851, baseEnd_2363851] using wordTrace_append hprefix tailTrace_2363851
  have hstable : (prefixWord ++ tailWord_2363851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363851).length < 2 ^ (prefixWord ++ tailWord_2363851).sum := by decide
  have hdescent : baseEnd_2363851 < baseStart_2363851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363861 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 1, 7]
def baseStart_2363861 : Nat := 118140960795 + 2363861 * 2 ^ 59
def prefixEnd_2363861 : Nat := 4983230072969 + 3 ^ 40 * 2363861 * 2
def baseEnd_2363861 : Nat := 404598964472627038888769

theorem tailTrace_2363861 : CollatzResearch.WordTrace tailWord_2363861 prefixEnd_2363861 404598964472627038888769 := by
  unfold tailWord_2363861
  simp only [CollatzResearch.WordTrace]
  refine ⟨86217093689142787162491437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57478062459428524774994291 86217093689142787162491437)
  ·
    refine ⟨32331410133428545185934289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86217093689142787162491437 32331410133428545185934289)
    ·
      refine ⟨24248557600071408889450717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32331410133428545185934289 24248557600071408889450717)
      ·
        refine ⟨9093209100026778333544019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24248557600071408889450717 9093209100026778333544019)
        ·
          refine ⟨13639813650040167500316029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9093209100026778333544019 13639813650040167500316029)
          ·
            refine ⟨5114930118765062812618511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13639813650040167500316029 5114930118765062812618511)
            ·
              refine ⟨7672395178147594218927767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5114930118765062812618511 7672395178147594218927767)
              ·
                refine ⟨11508592767221391328391651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7672395178147594218927767 11508592767221391328391651)
                ·
                  refine ⟨17262889150832086992587477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11508592767221391328391651 17262889150832086992587477)
                  ·
                    refine ⟨404598964472627038888769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17262889150832086992587477 404598964472627038888769)
                    ·
                      rfl

theorem cell23_2363861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_2363861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363861 prefixEnd_2363861 := by exact prefixLift 2363861
  have htrace : WordTrace (prefixWord ++ tailWord_2363861) baseStart_2363861 baseEnd_2363861 := by
    simpa [prefixWord, tailWord_2363861, baseEnd_2363861] using wordTrace_append hprefix tailTrace_2363861
  have hstable : (prefixWord ++ tailWord_2363861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363861).length < 2 ^ (prefixWord ++ tailWord_2363861).sum := by decide
  have hdescent : baseEnd_2363861 < baseStart_2363861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363901 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_2363901 : Nat := 118140960795 + 2363901 * 2 ^ 59
def prefixEnd_2363901 : Nat := 4983230072969 + 3 ^ 40 * 2363901 * 2
def baseEnd_2363901 : Nat := 1213817432644060960166123

theorem tailTrace_2363901 : CollatzResearch.WordTrace tailWord_2363901 prefixEnd_2363901 1213817432644060960166123 := by
  unfold tailWord_2363901
  simp only [CollatzResearch.WordTrace]
  refine ⟨86218552608997873993947557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57479035072665249329298371 86218552608997873993947557)
  ·
    refine ⟨16165978614187101373865167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86218552608997873993947557 16165978614187101373865167)
    ·
      refine ⟨24248967921280652060797751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16165978614187101373865167 24248967921280652060797751)
      ·
        refine ⟨36373451881920978091196627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24248967921280652060797751 36373451881920978091196627)
        ·
          refine ⟨54560177822881467136794941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36373451881920978091196627 54560177822881467136794941)
          ·
            refine ⟨20460066683580550176298103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54560177822881467136794941 20460066683580550176298103)
            ·
              refine ⟨30690100025370825264447155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20460066683580550176298103 30690100025370825264447155)
              ·
                refine ⟨46035150038056237896670733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30690100025370825264447155 46035150038056237896670733)
                ·
                  refine ⟨17263181264271089211251525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46035150038056237896670733 17263181264271089211251525)
                  ·
                    refine ⟨3236846487050829227109661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17263181264271089211251525 3236846487050829227109661)
                    ·
                      refine ⟨1213817432644060960166123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3236846487050829227109661 1213817432644060960166123)
                      ·
                        rfl

theorem cell23_2363901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_2363901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363901 prefixEnd_2363901 := by exact prefixLift 2363901
  have htrace : WordTrace (prefixWord ++ tailWord_2363901) baseStart_2363901 baseEnd_2363901 := by
    simpa [prefixWord, tailWord_2363901, baseEnd_2363901] using wordTrace_append hprefix tailTrace_2363901
  have hstable : (prefixWord ++ tailWord_2363901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363901).length < 2 ^ (prefixWord ++ tailWord_2363901).sum := by decide
  have hdescent : baseEnd_2363901 < baseStart_2363901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363918 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_2363918 : Nat := 118140960795 + 2363918 * 2 ^ 59
def prefixEnd_2363918 : Nat := 4983230072969 + 3 ^ 40 * 2363918 * 2
def baseEnd_2363918 : Nat := 1213826161815187393653545

theorem tailTrace_2363918 : CollatzResearch.WordTrace tailWord_2363918 prefixEnd_2363918 1213826161815187393653545 := by
  unfold tailWord_2363918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10777396581242035737164551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57479448433290857264877605 10777396581242035737164551)
  ·
    refine ⟨16166094871863053605746827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10777396581242035737164551 16166094871863053605746827)
    ·
      refine ⟨24249142307794580408620241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16166094871863053605746827 24249142307794580408620241)
      ·
        refine ⟨18186856730845935306465181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24249142307794580408620241 18186856730845935306465181)
        ·
          refine ⟨6820071274067225739924443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18186856730845935306465181 6820071274067225739924443)
          ·
            refine ⟨10230106911100838609886665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6820071274067225739924443 10230106911100838609886665)
            ·
              refine ⟨7672580183325628957414999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10230106911100838609886665 7672580183325628957414999)
              ·
                refine ⟨11508870274988443436122499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7672580183325628957414999 11508870274988443436122499)
                ·
                  refine ⟨17263305412482665154183749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11508870274988443436122499 17263305412482665154183749)
                  ·
                    refine ⟨3236869764840499716409453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17263305412482665154183749 3236869764840499716409453)
                    ·
                      refine ⟨1213826161815187393653545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3236869764840499716409453 1213826161815187393653545)
                      ·
                        rfl

theorem cell23_2363918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_2363918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363918 prefixEnd_2363918 := by exact prefixLift 2363918
  have htrace : WordTrace (prefixWord ++ tailWord_2363918) baseStart_2363918 baseEnd_2363918 := by
    simpa [prefixWord, tailWord_2363918, baseEnd_2363918] using wordTrace_append hprefix tailTrace_2363918
  have hstable : (prefixWord ++ tailWord_2363918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363918).length < 2 ^ (prefixWord ++ tailWord_2363918).sum := by decide
  have hdescent : baseEnd_2363918 < baseStart_2363918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363968 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 1, 5]
def baseStart_2363968 : Nat := 118140960795 + 2363968 * 2 ^ 59
def prefixEnd_2363968 : Nat := 4983230072969 + 3 ^ 40 * 2363968 * 2
def baseEnd_2363968 : Nat := 404617278615970732676105

theorem tailTrace_2363968 : CollatzResearch.WordTrace tailWord_2363968 prefixEnd_2363968 404617278615970732676105 := by
  unfold tailWord_2363968
  simp only [CollatzResearch.WordTrace]
  refine ⟨43110498149877572218318279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57480664199836762957757705 43110498149877572218318279)
  ·
    refine ⟨64665747224816358327477419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43110498149877572218318279 64665747224816358327477419)
    ·
      refine ⟨96998620837224537491216129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64665747224816358327477419 96998620837224537491216129)
      ·
        refine ⟨72748965627918403118412097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96998620837224537491216129 72748965627918403118412097)
        ·
          refine ⟨54561724220938802338809073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72748965627918403118412097 54561724220938802338809073)
          ·
            refine ⟨40921293165704101754106805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54561724220938802338809073 40921293165704101754106805)
            ·
              refine ⟨3836371234284759539447513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40921293165704101754106805 3836371234284759539447513)
              ·
                refine ⟨2877278425713569654585635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3836371234284759539447513 2877278425713569654585635)
                ·
                  refine ⟨4315917638570354481878453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877278425713569654585635 4315917638570354481878453)
                  ·
                    refine ⟨404617278615970732676105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4315917638570354481878453 404617278615970732676105)
                    ·
                      rfl

theorem cell23_2363968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 1, 5].length) (baseStart_2363968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363968 prefixEnd_2363968 := by exact prefixLift 2363968
  have htrace : WordTrace (prefixWord ++ tailWord_2363968) baseStart_2363968 baseEnd_2363968 := by
    simpa [prefixWord, tailWord_2363968, baseEnd_2363968] using wordTrace_append hprefix tailTrace_2363968
  have hstable : (prefixWord ++ tailWord_2363968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363968).length < 2 ^ (prefixWord ++ tailWord_2363968).sum := by decide
  have hdescent : baseEnd_2363968 < baseStart_2363968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363975 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 2, 3, 2]
def baseStart_2363975 : Nat := 118140960795 + 2363975 * 2 ^ 59
def prefixEnd_2363975 : Nat := 4983230072969 + 3 ^ 40 * 2363975 * 2
def baseEnd_2363975 : Nat := 1213855430212493670640783

theorem tailTrace_2363975 : CollatzResearch.WordTrace tailWord_2363975 prefixEnd_2363975 1213855430212493670640783 := by
  unfold tailWord_2363975
  simp only [CollatzResearch.WordTrace]
  refine ⟨86221251610729784632141379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57480834407153189754760919 86221251610729784632141379)
  ·
    refine ⟨129331877416094676948212069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86221251610729784632141379 129331877416094676948212069)
    ·
      refine ⟨24249727015517751927789763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129331877416094676948212069 24249727015517751927789763)
      ·
        refine ⟨36374590523276627891684645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24249727015517751927789763 36374590523276627891684645)
        ·
          refine ⟨6820235723114367729690871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36374590523276627891684645 6820235723114367729690871)
          ·
            refine ⟨10230353584671551594536307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6820235723114367729690871 10230353584671551594536307)
            ·
              refine ⟨15345530377007327391804461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10230353584671551594536307 15345530377007327391804461)
              ·
                refine ⟨5754573891377747771926673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15345530377007327391804461 5754573891377747771926673)
                ·
                  refine ⟨4315930418533310828945005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5754573891377747771926673 4315930418533310828945005)
                  ·
                    refine ⟨1618473906949991560854377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4315930418533310828945005 1618473906949991560854377)
                    ·
                      refine ⟨1213855430212493670640783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618473906949991560854377 1213855430212493670640783)
                      ·
                        rfl

theorem cell23_2363975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_2363975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363975 prefixEnd_2363975 := by exact prefixLift 2363975
  have htrace : WordTrace (prefixWord ++ tailWord_2363975) baseStart_2363975 baseEnd_2363975 := by
    simpa [prefixWord, tailWord_2363975, baseEnd_2363975] using wordTrace_append hprefix tailTrace_2363975
  have hstable : (prefixWord ++ tailWord_2363975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363975).length < 2 ^ (prefixWord ++ tailWord_2363975).sum := by decide
  have hdescent : baseEnd_2363975 < baseStart_2363975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2363985 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 1, 5]
def baseStart_2363985 : Nat := 118140960795 + 2363985 * 2 ^ 59
def prefixEnd_2363985 : Nat := 4983230072969 + 3 ^ 40 * 2363985 * 2
def baseEnd_2363985 : Nat := 404620188339679543838579

theorem tailTrace_2363985 : CollatzResearch.WordTrace tailWord_2363985 prefixEnd_2363985 404620188339679543838579 := by
  unfold tailWord_2363985
  simp only [CollatzResearch.WordTrace]
  refine ⟨86221616340693556340005409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57481077560462370893336939 86221616340693556340005409)
  ·
    refine ⟨64666212255520167255004057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86221616340693556340005409 64666212255520167255004057)
    ·
      refine ⟨48499659191640125441253043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64666212255520167255004057 48499659191640125441253043)
      ·
        refine ⟨72749488787460188161879565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48499659191640125441253043 72749488787460188161879565)
        ·
          refine ⟨27281058295297570560704837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72749488787460188161879565 27281058295297570560704837)
          ·
            refine ⟨5115198430368294480132157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27281058295297570560704837 5115198430368294480132157)
            ·
              refine ⟨1918199411388110430049559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5115198430368294480132157 1918199411388110430049559)
              ·
                refine ⟨2877299117082165645074339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918199411388110430049559 2877299117082165645074339)
                ·
                  refine ⟨4315948675623248467611509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877299117082165645074339 4315948675623248467611509)
                  ·
                    refine ⟨404620188339679543838579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4315948675623248467611509 404620188339679543838579)
                    ·
                      rfl

theorem cell23_2363985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 1, 5].length) (baseStart_2363985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2363985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2363985 prefixEnd_2363985 := by exact prefixLift 2363985
  have htrace : WordTrace (prefixWord ++ tailWord_2363985) baseStart_2363985 baseEnd_2363985 := by
    simpa [prefixWord, tailWord_2363985, baseEnd_2363985] using wordTrace_append hprefix tailTrace_2363985
  have hstable : (prefixWord ++ tailWord_2363985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2363985).length < 2 ^ (prefixWord ++ tailWord_2363985).sum := by decide
  have hdescent : baseEnd_2363985 < baseStart_2363985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2363985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364039 : List Nat := [1, 1, 4, 2, 1, 2, 4, 3, 1, 2, 2]
def baseStart_2364039 : Nat := 118140960795 + 2364039 * 2 ^ 59
def prefixEnd_2364039 : Nat := 4983230072969 + 3 ^ 40 * 2364039 * 2
def baseEnd_2364039 : Nat := 1213888292974381420240489

theorem tailTrace_2364039 : CollatzResearch.WordTrace tailWord_2364039 prefixEnd_2364039 1213888292974381420240489 := by
  unfold tailWord_2364039
  simp only [CollatzResearch.WordTrace]
  refine ⟨86223585882497923562471171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57482390588331949041647447 86223585882497923562471171)
  ·
    refine ⟨129335378823746885343706757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86223585882497923562471171 129335378823746885343706757)
    ·
      refine ⟨24250383529452541001945017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129335378823746885343706757 24250383529452541001945017)
      ·
        refine ⟨18187787647089405751458763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24250383529452541001945017 18187787647089405751458763)
        ·
          refine ⟨27281681470634108627188145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18187787647089405751458763 27281681470634108627188145)
          ·
            refine ⟨20461261102975581470391109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27281681470634108627188145 20461261102975581470391109)
            ·
              refine ⟨3836486456807921525698333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20461261102975581470391109 3836486456807921525698333)
              ·
                refine ⟨1438682421302970572136875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3836486456807921525698333 1438682421302970572136875)
                ·
                  refine ⟨2158023631954455858205313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438682421302970572136875 2158023631954455858205313)
                  ·
                    refine ⟨1618517723965841893653985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2158023631954455858205313 1618517723965841893653985)
                    ·
                      refine ⟨1213888292974381420240489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618517723965841893653985 1213888292974381420240489)
                      ·
                        rfl

theorem cell23_2364039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_2364039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364039 prefixEnd_2364039 := by exact prefixLift 2364039
  have htrace : WordTrace (prefixWord ++ tailWord_2364039) baseStart_2364039 baseEnd_2364039 := by
    simpa [prefixWord, tailWord_2364039, baseEnd_2364039] using wordTrace_append hprefix tailTrace_2364039
  have hstable : (prefixWord ++ tailWord_2364039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364039).length < 2 ^ (prefixWord ++ tailWord_2364039).sum := by decide
  have hdescent : baseEnd_2364039 < baseStart_2364039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364042 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_2364042 : Nat := 118140960795 + 2364042 * 2 ^ 59
def prefixEnd_2364042 : Nat := 4983230072969 + 3 ^ 40 * 2364042 * 2
def baseEnd_2364042 : Nat := 1213889833416344908502975

theorem tailTrace_2364042 : CollatzResearch.WordTrace tailWord_2364042 prefixEnd_2364042 1213889833416344908502975 := by
  unfold tailWord_2364042
  simp only [CollatzResearch.WordTrace]
  refine ⟨21555923825371763768707595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57482463534324703383220253 21555923825371763768707595)
  ·
    refine ⟨32333885738057645653061393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21555923825371763768707595 32333885738057645653061393)
    ·
      refine ⟨24250414303543234239796045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32333885738057645653061393 24250414303543234239796045)
      ·
        refine ⟨9093905363828712839923517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24250414303543234239796045 9093905363828712839923517)
        ·
          refine ⟨3410214511435767314971319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9093905363828712839923517 3410214511435767314971319)
          ·
            refine ⟨5115321767153650972456979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410214511435767314971319 5115321767153650972456979)
            ·
              refine ⟨7672982650730476458685469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5115321767153650972456979 7672982650730476458685469)
              ·
                refine ⟨2877368494023928672007051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7672982650730476458685469 2877368494023928672007051)
                ·
                  refine ⟨4316052741035893008010577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877368494023928672007051 4316052741035893008010577)
                  ·
                    refine ⟨3237039555776919756007933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4316052741035893008010577 3237039555776919756007933)
                    ·
                      refine ⟨1213889833416344908502975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3237039555776919756007933 1213889833416344908502975)
                      ·
                        rfl

theorem cell23_2364042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_2364042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364042 prefixEnd_2364042 := by exact prefixLift 2364042
  have htrace : WordTrace (prefixWord ++ tailWord_2364042) baseStart_2364042 baseEnd_2364042 := by
    simpa [prefixWord, tailWord_2364042, baseEnd_2364042] using wordTrace_append hprefix tailTrace_2364042
  have hstable : (prefixWord ++ tailWord_2364042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364042).length < 2 ^ (prefixWord ++ tailWord_2364042).sum := by decide
  have hdescent : baseEnd_2364042 < baseStart_2364042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364051 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 5]
def baseStart_2364051 : Nat := 118140960795 + 2364051 * 2 ^ 59
def prefixEnd_2364051 : Nat := 4983230072969 + 3 ^ 40 * 2364051 * 2
def baseEnd_2364051 : Nat := 1213894454742235373290433

theorem tailTrace_2364051 : CollatzResearch.WordTrace tailWord_2364051 prefixEnd_2364051 1213894454742235373290433 := by
  unfold tailWord_2364051
  simp only [CollatzResearch.WordTrace]
  refine ⟨86224023558454449611908007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57482682372302966407938671 86224023558454449611908007)
  ·
    refine ⟨129336035337681674417862011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86224023558454449611908007 129336035337681674417862011)
    ·
      refine ⟨194004053006522511626793017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129336035337681674417862011 194004053006522511626793017)
      ·
        refine ⟨145503039754891883720094763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 194004053006522511626793017 145503039754891883720094763)
        ·
          refine ⟨218254559632337825580142145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145503039754891883720094763 218254559632337825580142145)
          ·
            refine ⟨163690919724253369185106609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218254559632337825580142145 163690919724253369185106609)
            ·
              refine ⟨122768189793190026888829957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163690919724253369185106609 122768189793190026888829957)
              ·
                refine ⟨23019035586223130041655617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122768189793190026888829957 23019035586223130041655617)
                ·
                  refine ⟨17264276689667347531241713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23019035586223130041655617 17264276689667347531241713)
                  ·
                    refine ⟨12948207517250510648431285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17264276689667347531241713 12948207517250510648431285)
                    ·
                      refine ⟨1213894454742235373290433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12948207517250510648431285 1213894454742235373290433)
                      ·
                        rfl

theorem cell23_2364051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_2364051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364051 prefixEnd_2364051 := by exact prefixLift 2364051
  have htrace : WordTrace (prefixWord ++ tailWord_2364051) baseStart_2364051 baseEnd_2364051 := by
    simpa [prefixWord, tailWord_2364051, baseEnd_2364051] using wordTrace_append hprefix tailTrace_2364051
  have hstable : (prefixWord ++ tailWord_2364051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364051).length < 2 ^ (prefixWord ++ tailWord_2364051).sum := by decide
  have hdescent : baseEnd_2364051 < baseStart_2364051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364055 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 4, 1, 3]
def baseStart_2364055 : Nat := 118140960795 + 2364055 * 2 ^ 59
def prefixEnd_2364055 : Nat := 4983230072969 + 3 ^ 40 * 2364055 * 2
def baseEnd_2364055 : Nat := 1213896508664853357640415

theorem tailTrace_2364055 : CollatzResearch.WordTrace tailWord_2364055 prefixEnd_2364055 1213896508664853357640415 := by
  unfold tailWord_2364055
  simp only [CollatzResearch.WordTrace]
  refine ⟨86224169450439958295053619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57482779633626638863369079 86224169450439958295053619)
  ·
    refine ⟨129336254175659937442580429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86224169450439958295053619 129336254175659937442580429)
    ·
      refine ⟨48501095315872476540967661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129336254175659937442580429 48501095315872476540967661)
      ·
        refine ⟨18187910743452178702862873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48501095315872476540967661 18187910743452178702862873)
        ·
          refine ⟨13640933057589134027147155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18187910743452178702862873 13640933057589134027147155)
          ·
            refine ⟨20461399586383701040720733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13640933057589134027147155 20461399586383701040720733)
            ·
              refine ⟨7673024844893887890270275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20461399586383701040720733 7673024844893887890270275)
              ·
                refine ⟨11509537267340831835405413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7673024844893887890270275 11509537267340831835405413)
                ·
                  refine ⟨2158038237626405969138515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11509537267340831835405413 2158038237626405969138515)
                  ·
                    refine ⟨3237057356439608953707773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2158038237626405969138515 3237057356439608953707773)
                    ·
                      refine ⟨1213896508664853357640415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3237057356439608953707773 1213896508664853357640415)
                      ·
                        rfl

theorem cell23_2364055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_2364055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364055 prefixEnd_2364055 := by exact prefixLift 2364055
  have htrace : WordTrace (prefixWord ++ tailWord_2364055) baseStart_2364055 baseEnd_2364055 := by
    simpa [prefixWord, tailWord_2364055, baseEnd_2364055] using wordTrace_append hprefix tailTrace_2364055
  have hstable : (prefixWord ++ tailWord_2364055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364055).length < 2 ^ (prefixWord ++ tailWord_2364055).sum := by decide
  have hdescent : baseEnd_2364055 < baseStart_2364055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364128 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 3]
def baseStart_2364128 : Nat := 118140960795 + 2364128 * 2 ^ 59
def prefixEnd_2364128 : Nat := 4983230072969 + 3 ^ 40 * 2364128 * 2
def baseEnd_2364128 : Nat := 1213933992752631572027579

theorem tailTrace_2364128 : CollatzResearch.WordTrace tailWord_2364128 prefixEnd_2364128 1213933992752631572027579 := by
  unfold tailWord_2364128
  simp only [CollatzResearch.WordTrace]
  refine ⟨43113415989587745881230519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57484554652783661174974025 43113415989587745881230519)
  ·
    refine ⟨64670123984381618821845779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43113415989587745881230519 64670123984381618821845779)
    ·
      refine ⟨97005185976572428232768669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64670123984381618821845779 97005185976572428232768669)
      ·
        refine ⟨36376944741214660587288251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97005185976572428232768669 36376944741214660587288251)
        ·
          refine ⟨54565417111821990880932377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36376944741214660587288251 54565417111821990880932377)
          ·
            refine ⟨40924062833866493160699283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54565417111821990880932377 40924062833866493160699283)
            ·
              refine ⟨61386094250799739741048925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40924062833866493160699283 61386094250799739741048925)
              ·
                refine ⟨23019785344049902402893347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61386094250799739741048925 23019785344049902402893347)
                ·
                  refine ⟨34529678016074853604340021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23019785344049902402893347 34529678016074853604340021)
                  ·
                    refine ⟨3237157314007017525406877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34529678016074853604340021 3237157314007017525406877)
                    ·
                      refine ⟨1213933992752631572027579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3237157314007017525406877 1213933992752631572027579)
                      ·
                        rfl

theorem cell23_2364128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_2364128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364128 prefixEnd_2364128 := by exact prefixLift 2364128
  have htrace : WordTrace (prefixWord ++ tailWord_2364128) baseStart_2364128 baseEnd_2364128 := by
    simpa [prefixWord, tailWord_2364128, baseEnd_2364128] using wordTrace_append hprefix tailTrace_2364128
  have hstable : (prefixWord ++ tailWord_2364128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364128).length < 2 ^ (prefixWord ++ tailWord_2364128).sum := by decide
  have hdescent : baseEnd_2364128 < baseStart_2364128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364129 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 2, 2, 2]
def baseStart_2364129 : Nat := 118140960795 + 2364129 * 2 ^ 59
def prefixEnd_2364129 : Nat := 4983230072969 + 3 ^ 40 * 2364129 * 2
def baseEnd_2364129 : Nat := 1213934506233286068115075

theorem tailTrace_2364129 : CollatzResearch.WordTrace tailWord_2364129 prefixEnd_2364129 1213934506233286068115075 := by
  unfold tailWord_2364129
  simp only [CollatzResearch.WordTrace]
  refine ⟨86226868452171868933247441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57484578968114579288831627 86226868452171868933247441)
  ·
    refine ⟨64670151339128901699935581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86226868452171868933247441 64670151339128901699935581)
    ·
      refine ⟨24251306752173338137475843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64670151339128901699935581 24251306752173338137475843)
      ·
        refine ⟨36376960128260007206213765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24251306752173338137475843 36376960128260007206213765)
        ·
          refine ⟨6820680024048751351165081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36376960128260007206213765 6820680024048751351165081)
          ·
            refine ⟨5115510018036563513373811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6820680024048751351165081 5115510018036563513373811)
            ·
              refine ⟨7673265027054845270060717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5115510018036563513373811 7673265027054845270060717)
              ·
                refine ⟨2877474385145566976272769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7673265027054845270060717 2877474385145566976272769)
                ·
                  refine ⟨2158105788859175232204577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2877474385145566976272769 2158105788859175232204577)
                  ·
                    refine ⟨1618579341644381424153433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2158105788859175232204577 1618579341644381424153433)
                    ·
                      refine ⟨1213934506233286068115075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618579341644381424153433 1213934506233286068115075)
                      ·
                        rfl

theorem cell23_2364129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_2364129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364129 prefixEnd_2364129 := by exact prefixLift 2364129
  have htrace : WordTrace (prefixWord ++ tailWord_2364129) baseStart_2364129 baseEnd_2364129 := by
    simpa [prefixWord, tailWord_2364129, baseEnd_2364129] using wordTrace_append hprefix tailTrace_2364129
  have hstable : (prefixWord ++ tailWord_2364129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364129).length < 2 ^ (prefixWord ++ tailWord_2364129).sum := by decide
  have hdescent : baseEnd_2364129 < baseStart_2364129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364242 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 6]
def baseStart_2364242 : Nat := 118140960795 + 2364242 * 2 ^ 59
def prefixEnd_2364242 : Nat := 4983230072969 + 3 ^ 40 * 2364242 * 2
def baseEnd_2364242 : Nat := 134888058838582680666895

theorem tailTrace_2364242 : CollatzResearch.WordTrace tailWord_2364242 prefixEnd_2364242 134888058838582680666895 := by
  unfold tailWord_2364242
  simp only [CollatzResearch.WordTrace]
  refine ⟨21557747475190622308027745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57487326600508326154740653 21557747475190622308027745)
  ·
    refine ⟨16168310606392966731020809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21557747475190622308027745 16168310606392966731020809)
    ·
      refine ⟨12126232954794725048265607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16168310606392966731020809 12126232954794725048265607)
      ·
        refine ⟨18189349432192087572398411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12126232954794725048265607 18189349432192087572398411)
        ·
          refine ⟨27284024148288131358597617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18189349432192087572398411 27284024148288131358597617)
          ·
            refine ⟨20463018111216098518948213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27284024148288131358597617 20463018111216098518948213)
            ·
              refine ⟨1918407947926509236151395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20463018111216098518948213 1918407947926509236151395)
              ·
                refine ⟨2877611921889763854227093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918407947926509236151395 2877611921889763854227093)
                ·
                  refine ⟨134888058838582680666895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2877611921889763854227093 134888058838582680666895)
                  ·
                    rfl

theorem cell23_2364242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_2364242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364242 prefixEnd_2364242 := by exact prefixLift 2364242
  have htrace : WordTrace (prefixWord ++ tailWord_2364242) baseStart_2364242 baseEnd_2364242 := by
    simpa [prefixWord, tailWord_2364242, baseEnd_2364242] using wordTrace_append hprefix tailTrace_2364242
  have hstable : (prefixWord ++ tailWord_2364242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364242).length < 2 ^ (prefixWord ++ tailWord_2364242).sum := by decide
  have hdescent : baseEnd_2364242 < baseStart_2364242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364248 : List Nat := [2, 1, 2, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2364248 : Nat := 118140960795 + 2364248 * 2 ^ 59
def prefixEnd_2364248 : Nat := 4983230072969 + 3 ^ 40 * 2364248 * 2
def baseEnd_2364248 : Nat := 1213995610431171102527027

theorem tailTrace_2364248 : CollatzResearch.WordTrace tailWord_2364248 prefixEnd_2364248 1213995610431171102527027 := by
  unfold tailWord_2364248
  simp only [CollatzResearch.WordTrace]
  refine ⟨43115604369370376128414699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57487472492493834837886265 43115604369370376128414699)
  ·
    refine ⟨64673406554055564192622049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43115604369370376128414699 64673406554055564192622049)
    ·
      refine ⟨48505054915541673144466537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64673406554055564192622049 48505054915541673144466537)
      ·
        refine ⟨36378791186656254858349903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48505054915541673144466537 36378791186656254858349903)
        ·
          refine ⟨54568186779984382287524855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36378791186656254858349903 54568186779984382287524855)
          ·
            refine ⟨81852280169976573431287283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54568186779984382287524855 81852280169976573431287283)
            ·
              refine ⟨122778420254964860146930925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81852280169976573431287283 122778420254964860146930925)
              ·
                refine ⟨46041907595611822555099097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122778420254964860146930925 46041907595611822555099097)
                ·
                  refine ⟨34531430696708866916324323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46041907595611822555099097 34531430696708866916324323)
                  ·
                    refine ⟨51797146045063300374486485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 34531430696708866916324323 51797146045063300374486485)
                    ·
                      refine ⟨1213995610431171102527027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 51797146045063300374486485 1213995610431171102527027)
                      ·
                        rfl

theorem cell23_2364248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2364248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364248 prefixEnd_2364248 := by exact prefixLift 2364248
  have htrace : WordTrace (prefixWord ++ tailWord_2364248) baseStart_2364248 baseEnd_2364248 := by
    simpa [prefixWord, tailWord_2364248, baseEnd_2364248] using wordTrace_append hprefix tailTrace_2364248
  have hstable : (prefixWord ++ tailWord_2364248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364248).length < 2 ^ (prefixWord ++ tailWord_2364248).sum := by decide
  have hdescent : baseEnd_2364248 < baseStart_2364248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364305 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 4]
def baseStart_2364305 : Nat := 118140960795 + 2364305 * 2 ^ 59
def prefixEnd_2364305 : Nat := 4983230072969 + 3 ^ 40 * 2364305 * 2
def baseEnd_2364305 : Nat := 1214024878828477379514265

theorem tailTrace_2364305 : CollatzResearch.WordTrace tailWord_2364305 prefixEnd_2364305 1214024878828477379514265 := by
  unfold tailWord_2364305
  simp only [CollatzResearch.WordTrace]
  refine ⟨86233287699534250991654369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57488858466356167327769579 86233287699534250991654369)
  ·
    refine ⟨64674965774650688243740777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86233287699534250991654369 64674965774650688243740777)
    ·
      refine ⟨48506224330988016182805583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64674965774650688243740777 48506224330988016182805583)
      ·
        refine ⟨72759336496482024274208375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48506224330988016182805583 72759336496482024274208375)
        ·
          refine ⟨109139004744723036411312563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72759336496482024274208375 109139004744723036411312563)
          ·
            refine ⟨163708507117084554616968845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109139004744723036411312563 163708507117084554616968845)
            ·
              refine ⟨61390690168906707981363317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163708507117084554616968845 61390690168906707981363317)
              ·
                refine ⟨5755377203335003873252811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61390690168906707981363317 5755377203335003873252811)
                ·
                  refine ⟨8633065805002505809879217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5755377203335003873252811 8633065805002505809879217)
                  ·
                    refine ⟨6474799353751879357409413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8633065805002505809879217 6474799353751879357409413)
                    ·
                      refine ⟨1214024878828477379514265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6474799353751879357409413 1214024878828477379514265)
                      ·
                        rfl

theorem cell23_2364305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 4].length) (baseStart_2364305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364305 prefixEnd_2364305 := by exact prefixLift 2364305
  have htrace : WordTrace (prefixWord ++ tailWord_2364305) baseStart_2364305 baseEnd_2364305 := by
    simpa [prefixWord, tailWord_2364305, baseEnd_2364305] using wordTrace_append hprefix tailTrace_2364305
  have hstable : (prefixWord ++ tailWord_2364305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364305).length < 2 ^ (prefixWord ++ tailWord_2364305).sum := by decide
  have hdescent : baseEnd_2364305 < baseStart_2364305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364306 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2364306 : Nat := 118140960795 + 2364306 * 2 ^ 59
def prefixEnd_2364306 : Nat := 4983230072969 + 3 ^ 40 * 2364306 * 2
def baseEnd_2364306 : Nat := 404675130769710625200587

theorem tailTrace_2364306 : CollatzResearch.WordTrace tailWord_2364306 prefixEnd_2364306 404675130769710625200587 := by
  unfold tailWord_2364306
  simp only [CollatzResearch.WordTrace]
  refine ⟨21558331043132657040610193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57488882781687085441627181 21558331043132657040610193)
  ·
    refine ⟨16168748282349492780457645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21558331043132657040610193 16168748282349492780457645)
    ·
      refine ⟨6063280605881059792671617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16168748282349492780457645 6063280605881059792671617)
      ·
        refine ⟨4547460454410794844503713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6063280605881059792671617 4547460454410794844503713)
        ·
          refine ⟨3410595340808096133377785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4547460454410794844503713 3410595340808096133377785)
          ·
            refine ⟨2557946505606072100033339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3410595340808096133377785 2557946505606072100033339)
            ·
              refine ⟨3836919758409108150050009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2557946505606072100033339 3836919758409108150050009)
              ·
                refine ⟨2877689818806831112537507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3836919758409108150050009 2877689818806831112537507)
                ·
                  refine ⟨4316534728210246668806261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877689818806831112537507 4316534728210246668806261)
                  ·
                    refine ⟨404675130769710625200587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4316534728210246668806261 404675130769710625200587)
                    ·
                      rfl

theorem cell23_2364306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2364306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364306 prefixEnd_2364306 := by exact prefixLift 2364306
  have htrace : WordTrace (prefixWord ++ tailWord_2364306) baseStart_2364306 baseEnd_2364306 := by
    simpa [prefixWord, tailWord_2364306, baseEnd_2364306] using wordTrace_append hprefix tailTrace_2364306
  have hstable : (prefixWord ++ tailWord_2364306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364306).length < 2 ^ (prefixWord ++ tailWord_2364306).sum := by decide
  have hdescent : baseEnd_2364306 < baseStart_2364306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364309 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 4]
def baseStart_2364309 : Nat := 118140960795 + 2364309 * 2 ^ 59
def prefixEnd_2364309 : Nat := 4983230072969 + 3 ^ 40 * 2364309 * 2
def baseEnd_2364309 : Nat := 1214026932751095363864247

theorem tailTrace_2364309 : CollatzResearch.WordTrace tailWord_2364309 prefixEnd_2364309 1214026932751095363864247 := by
  unfold tailWord_2364309
  simp only [CollatzResearch.WordTrace]
  refine ⟨86233433591519759674799981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57488955727679839783199987 86233433591519759674799981)
  ·
    refine ⟨32337537596819909878049993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86233433591519759674799981 32337537596819909878049993)
    ·
      refine ⟨24253153197614932408537495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32337537596819909878049993 24253153197614932408537495)
      ·
        refine ⟨36379729796422398612806243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24253153197614932408537495 36379729796422398612806243)
        ·
          refine ⟨54569594694633597919209365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36379729796422398612806243 54569594694633597919209365)
          ·
            refine ⟨2557949751310949902462939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54569594694633597919209365 2557949751310949902462939)
            ·
              refine ⟨3836924626966424853694409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2557949751310949902462939 3836924626966424853694409)
              ·
                refine ⟨2877693470224818640270807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3836924626966424853694409 2877693470224818640270807)
                ·
                  refine ⟨4316540205337227960406211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877693470224818640270807 4316540205337227960406211)
                  ·
                    refine ⟨6474810308005841940609317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4316540205337227960406211 6474810308005841940609317)
                    ·
                      refine ⟨1214026932751095363864247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6474810308005841940609317 1214026932751095363864247)
                      ·
                        rfl

theorem cell23_2364309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_2364309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364309 prefixEnd_2364309 := by exact prefixLift 2364309
  have htrace : WordTrace (prefixWord ++ tailWord_2364309) baseStart_2364309 baseEnd_2364309 := by
    simpa [prefixWord, tailWord_2364309, baseEnd_2364309] using wordTrace_append hprefix tailTrace_2364309
  have hstable : (prefixWord ++ tailWord_2364309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364309).length < 2 ^ (prefixWord ++ tailWord_2364309).sum := by decide
  have hdescent : baseEnd_2364309 < baseStart_2364309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364322 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2364322 : Nat := 118140960795 + 2364322 * 2 ^ 59
def prefixEnd_2364322 : Nat := 4983230072969 + 3 ^ 40 * 2364322 * 2
def baseEnd_2364322 : Nat := 1214033607999603813001687

theorem tailTrace_2364322 : CollatzResearch.WordTrace tailWord_2364322 prefixEnd_2364322 1214033607999603813001687 := by
  unfold tailWord_2364322
  simp only [CollatzResearch.WordTrace]
  refine ⟨21558476935118165723755805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57489271826981775263348813 21558476935118165723755805)
  ·
    refine ⟨8084428850669312146408427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21558476935118165723755805 8084428850669312146408427)
    ·
      refine ⟨12126643276003968219612641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8084428850669312146408427 12126643276003968219612641)
      ·
        refine ⟨9094982457002976164709481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12126643276003968219612641 9094982457002976164709481)
        ·
          refine ⟨6821236842752232123532111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9094982457002976164709481 6821236842752232123532111)
          ·
            refine ⟨10231855264128348185298167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6821236842752232123532111 10231855264128348185298167)
            ·
              refine ⟨15347782896192522277947251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10231855264128348185298167 15347782896192522277947251)
              ·
                refine ⟨23021674344288783416920877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15347782896192522277947251 23021674344288783416920877)
                ·
                  refine ⟨8633127879108293781345329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23021674344288783416920877 8633127879108293781345329)
                  ·
                    refine ⟨6474845909331220336008997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8633127879108293781345329 6474845909331220336008997)
                    ·
                      refine ⟨1214033607999603813001687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6474845909331220336008997 1214033607999603813001687)
                      ·
                        rfl

theorem cell23_2364322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2364322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364322 prefixEnd_2364322 := by exact prefixLift 2364322
  have htrace : WordTrace (prefixWord ++ tailWord_2364322) baseStart_2364322 baseEnd_2364322 := by
    simpa [prefixWord, tailWord_2364322, baseEnd_2364322] using wordTrace_append hprefix tailTrace_2364322
  have hstable : (prefixWord ++ tailWord_2364322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364322).length < 2 ^ (prefixWord ++ tailWord_2364322).sum := by decide
  have hdescent : baseEnd_2364322 < baseStart_2364322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364329 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 1, 2, 3]
def baseStart_2364329 : Nat := 118140960795 + 2364329 * 2 ^ 59
def prefixEnd_2364329 : Nat := 4983230072969 + 3 ^ 40 * 2364329 * 2
def baseEnd_2364329 : Nat := 1214037202364185285614155

theorem tailTrace_2364329 : CollatzResearch.WordTrace tailWord_2364329 prefixEnd_2364329 1214037202364185285614155 := by
  unfold tailWord_2364329
  simp only [CollatzResearch.WordTrace]
  refine ⟨86234163051447303090528041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57489442034298202060352027 86234163051447303090528041)
  ·
    refine ⟨64675622288585477317896031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86234163051447303090528041 64675622288585477317896031)
    ·
      refine ⟨97013433432878215976844047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64675622288585477317896031 97013433432878215976844047)
      ·
        refine ⟨145520150149317323965266071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97013433432878215976844047 145520150149317323965266071)
        ·
          refine ⟨218280225223975985947899107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145520150149317323965266071 218280225223975985947899107)
          ·
            refine ⟨327420337835963978921848661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 218280225223975985947899107 327420337835963978921848661)
            ·
              refine ⟨1918478542007601438995207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 327420337835963978921848661 1918478542007601438995207)
              ·
                refine ⟨2877717813011402158492811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1918478542007601438995207 2877717813011402158492811)
                ·
                  refine ⟨4316576719517103237739217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877717813011402158492811 4316576719517103237739217)
                  ·
                    refine ⟨3237432539637827428304413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4316576719517103237739217 3237432539637827428304413)
                    ·
                      refine ⟨1214037202364185285614155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3237432539637827428304413 1214037202364185285614155)
                      ·
                        rfl

theorem cell23_2364329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 1, 2, 3].length) (baseStart_2364329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364329 prefixEnd_2364329 := by exact prefixLift 2364329
  have htrace : WordTrace (prefixWord ++ tailWord_2364329) baseStart_2364329 baseEnd_2364329 := by
    simpa [prefixWord, tailWord_2364329, baseEnd_2364329] using wordTrace_append hprefix tailTrace_2364329
  have hstable : (prefixWord ++ tailWord_2364329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364329).length < 2 ^ (prefixWord ++ tailWord_2364329).sum := by decide
  have hdescent : baseEnd_2364329 < baseStart_2364329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364343 : List Nat := [1, 1, 3, 1, 3, 1, 6, 2, 1, 2, 2]
def baseStart_2364343 : Nat := 118140960795 + 2364343 * 2 ^ 59
def prefixEnd_2364343 : Nat := 4983230072969 + 3 ^ 40 * 2364343 * 2
def baseEnd_2364343 : Nat := 1214044391093348230839091

theorem tailTrace_2364343 : CollatzResearch.WordTrace tailWord_2364343 prefixEnd_2364343 1214044391093348230839091 := by
  unfold tailWord_2364343
  simp only [CollatzResearch.WordTrace]
  refine ⟨86234673673396583481537683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57489782448931055654358455 86234673673396583481537683)
  ·
    refine ⟨129352010510094875222306525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86234673673396583481537683 129352010510094875222306525)
    ·
      refine ⟨48507003941285578208364947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 129352010510094875222306525 48507003941285578208364947)
      ·
        refine ⟨72760505911928367312547421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48507003941285578208364947 72760505911928367312547421)
        ·
          refine ⟨27285189716973137742205283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72760505911928367312547421 27285189716973137742205283)
          ·
            refine ⟨40927784575459706613307925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27285189716973137742205283 40927784575459706613307925)
            ·
              refine ⟨1918489901974673747498809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 40927784575459706613307925 1918489901974673747498809)
              ·
                refine ⟨1438867426481005310624107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1918489901974673747498809 1438867426481005310624107)
                ·
                  refine ⟨2158301139721507965936161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1438867426481005310624107 2158301139721507965936161)
                  ·
                    refine ⟨1618725854791130974452121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2158301139721507965936161 1618725854791130974452121)
                    ·
                      refine ⟨1214044391093348230839091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618725854791130974452121 1214044391093348230839091)
                      ·
                        rfl

theorem cell23_2364343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 1, 2, 2].length) (baseStart_2364343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364343 prefixEnd_2364343 := by exact prefixLift 2364343
  have htrace : WordTrace (prefixWord ++ tailWord_2364343) baseStart_2364343 baseEnd_2364343 := by
    simpa [prefixWord, tailWord_2364343, baseEnd_2364343] using wordTrace_append hprefix tailTrace_2364343
  have hstable : (prefixWord ++ tailWord_2364343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364343).length < 2 ^ (prefixWord ++ tailWord_2364343).sum := by decide
  have hdescent : baseEnd_2364343 < baseStart_2364343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364345 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 2, 7]
def baseStart_2364345 : Nat := 118140960795 + 2364345 * 2 ^ 59
def prefixEnd_2364345 : Nat := 4983230072969 + 3 ^ 40 * 2364345 * 2
def baseEnd_2364345 : Nat := 404681806018219074338027

theorem tailTrace_2364345 : CollatzResearch.WordTrace tailWord_2364345 prefixEnd_2364345 404681806018219074338027 := by
  unfold tailWord_2364345
  simp only [CollatzResearch.WordTrace]
  refine ⟨86234746619389337823110489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57489831079592891882073659 86234746619389337823110489)
  ·
    refine ⟨64676059964542003367332867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86234746619389337823110489 64676059964542003367332867)
    ·
      refine ⟨97014089946813005050999301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64676059964542003367332867 97014089946813005050999301)
      ·
        refine ⟨18190141865027438447062369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97014089946813005050999301 18190141865027438447062369)
        ·
          refine ⟨13642606398770578835296777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18190141865027438447062369 13642606398770578835296777)
          ·
            refine ⟨10231954799077934126472583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13642606398770578835296777 10231954799077934126472583)
            ·
              refine ⟨15347932198616901189708875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10231954799077934126472583 15347932198616901189708875)
              ·
                refine ⟨23021898297925351784563313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15347932198616901189708875 23021898297925351784563313)
                ·
                  refine ⟨17266423723444013838422485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23021898297925351784563313 17266423723444013838422485)
                  ·
                    refine ⟨404681806018219074338027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17266423723444013838422485 404681806018219074338027)
                    ·
                      rfl

theorem cell23_2364345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 7].length) (baseStart_2364345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364345 prefixEnd_2364345 := by exact prefixLift 2364345
  have htrace : WordTrace (prefixWord ++ tailWord_2364345) baseStart_2364345 baseEnd_2364345 := by
    simpa [prefixWord, tailWord_2364345, baseEnd_2364345] using wordTrace_append hprefix tailTrace_2364345
  have hstable : (prefixWord ++ tailWord_2364345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364345).length < 2 ^ (prefixWord ++ tailWord_2364345).sum := by decide
  have hdescent : baseEnd_2364345 < baseStart_2364345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364349 : List Nat := [1, 4, 1, 2, 5, 1, 1, 8]
def baseStart_2364349 : Nat := 118140960795 + 2364349 * 2 ^ 59
def prefixEnd_2364349 : Nat := 4983230072969 + 3 ^ 40 * 2364349 * 2
def baseEnd_2364349 : Nat := 44964721184343526198669

theorem tailTrace_2364349 : CollatzResearch.WordTrace tailWord_2364349 prefixEnd_2364349 44964721184343526198669 := by
  unfold tailWord_2364349
  simp only [CollatzResearch.WordTrace]
  refine ⟨86234892511374846506256101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57489928340916564337504067 86234892511374846506256101)
  ·
    refine ⟨16169042345882783719923019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86234892511374846506256101 16169042345882783719923019)
    ·
      refine ⟨24253563518824175579884529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16169042345882783719923019 24253563518824175579884529)
      ·
        refine ⟨18190172639118131684913397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24253563518824175579884529 18190172639118131684913397)
        ·
          refine ⟨1705328684917324845460631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18190172639118131684913397 1705328684917324845460631)
          ·
            refine ⟨2557993027375987268190947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705328684917324845460631 2557993027375987268190947)
            ·
              refine ⟨3836989541063980902286421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2557993027375987268190947 3836989541063980902286421)
              ·
                refine ⟨44964721184343526198669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3836989541063980902286421 44964721184343526198669)
                ·
                  rfl

theorem cell23_2364349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 8].length) (baseStart_2364349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364349 prefixEnd_2364349 := by exact prefixLift 2364349
  have htrace : WordTrace (prefixWord ++ tailWord_2364349) baseStart_2364349 baseEnd_2364349 := by
    simpa [prefixWord, tailWord_2364349, baseEnd_2364349] using wordTrace_append hprefix tailTrace_2364349
  have hstable : (prefixWord ++ tailWord_2364349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364349).length < 2 ^ (prefixWord ++ tailWord_2364349).sum := by decide
  have hdescent : baseEnd_2364349 < baseStart_2364349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364356 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_2364356 : Nat := 118140960795 + 2364356 * 2 ^ 59
def prefixEnd_2364356 : Nat := 4983230072969 + 3 ^ 40 * 2364356 * 2
def baseEnd_2364356 : Nat := 1214051066341856679976531

theorem tailTrace_2364356 : CollatzResearch.WordTrace tailWord_2364356 prefixEnd_2364356 1214051066341856679976531 := by
  unfold tailWord_2364356
  simp only [CollatzResearch.WordTrace]
  refine ⟨43117573911174743350880461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57490098548232991134507281 43117573911174743350880461)
  ·
    refine ⟨16169090216690528756580173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43117573911174743350880461 16169090216690528756580173)
    ·
      refine ⟨6063408831258948283717565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16169090216690528756580173 6063408831258948283717565)
      ·
        refine ⟨2273778311722105606394087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6063408831258948283717565 2273778311722105606394087)
        ·
          refine ⟨3410667467583158409591131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273778311722105606394087 3410667467583158409591131)
          ·
            refine ⟨5116001201374737614386697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410667467583158409591131 5116001201374737614386697)
            ·
              refine ⟨3837000901031053210790023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5116001201374737614386697 3837000901031053210790023)
              ·
                refine ⟨5755501351546579816185035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3837000901031053210790023 5755501351546579816185035)
                ·
                  refine ⟨8633252027319869724277553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5755501351546579816185035 8633252027319869724277553)
                  ·
                    refine ⟨6474939020489902293208165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8633252027319869724277553 6474939020489902293208165)
                    ·
                      refine ⟨1214051066341856679976531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6474939020489902293208165 1214051066341856679976531)
                      ·
                        rfl

theorem cell23_2364356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_2364356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364356 prefixEnd_2364356 := by exact prefixLift 2364356
  have htrace : WordTrace (prefixWord ++ tailWord_2364356) baseStart_2364356 baseEnd_2364356 := by
    simpa [prefixWord, tailWord_2364356, baseEnd_2364356] using wordTrace_append hprefix tailTrace_2364356
  have hstable : (prefixWord ++ tailWord_2364356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364356).length < 2 ^ (prefixWord ++ tailWord_2364356).sum := by decide
  have hdescent : baseEnd_2364356 < baseStart_2364356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364359 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 2, 1, 3]
def baseStart_2364359 : Nat := 118140960795 + 2364359 * 2 ^ 59
def prefixEnd_2364359 : Nat := 4983230072969 + 3 ^ 40 * 2364359 * 2
def baseEnd_2364359 : Nat := 1214052606783820168239017

theorem tailTrace_2364359 : CollatzResearch.WordTrace tailWord_2364359 prefixEnd_2364359 1214052606783820168239017 := by
  unfold tailWord_2364359
  simp only [CollatzResearch.WordTrace]
  refine ⟨86235257241338618214120131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57490171494225745476080087 86235257241338618214120131)
  ·
    refine ⟨129352885862007927321180197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86235257241338618214120131 129352885862007927321180197)
    ·
      refine ⟨24253666099126486372721287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 129352885862007927321180197 24253666099126486372721287)
      ·
        refine ⟨36380499148689729559081931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24253666099126486372721287 36380499148689729559081931)
        ·
          refine ⟨54570748723034594338622897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36380499148689729559081931 54570748723034594338622897)
          ·
            refine ⟨40928061542275945753967173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54570748723034594338622897 40928061542275945753967173)
            ·
              refine ⟨7674011539176739828868845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40928061542275945753967173 7674011539176739828868845)
              ·
                refine ⟨2877754327191277435825817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7674011539176739828868845 2877754327191277435825817)
                ·
                  refine ⟨2158315745393458076869363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2877754327191277435825817 2158315745393458076869363)
                  ·
                    refine ⟨3237473618090187115304045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2158315745393458076869363 3237473618090187115304045)
                    ·
                      refine ⟨1214052606783820168239017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3237473618090187115304045 1214052606783820168239017)
                      ·
                        rfl

theorem cell23_2364359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_2364359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364359 prefixEnd_2364359 := by exact prefixLift 2364359
  have htrace : WordTrace (prefixWord ++ tailWord_2364359) baseStart_2364359 baseEnd_2364359 := by
    simpa [prefixWord, tailWord_2364359, baseEnd_2364359] using wordTrace_append hprefix tailTrace_2364359
  have hstable : (prefixWord ++ tailWord_2364359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364359).length < 2 ^ (prefixWord ++ tailWord_2364359).sum := by decide
  have hdescent : baseEnd_2364359 < baseStart_2364359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364369 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 1, 3, 2]
def baseStart_2364369 : Nat := 118140960795 + 2364369 * 2 ^ 59
def prefixEnd_2364369 : Nat := 4983230072969 + 3 ^ 40 * 2364369 * 2
def baseEnd_2364369 : Nat := 1214057741590365129113971

theorem tailTrace_2364369 : CollatzResearch.WordTrace tailWord_2364369 prefixEnd_2364369 1214057741590365129113971 := by
  unfold tailWord_2364369
  simp only [CollatzResearch.WordTrace]
  refine ⟨86235621971302389921984161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57490414647534926614656107 86235621971302389921984161)
  ·
    refine ⟨64676716478476792441488121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86235621971302389921984161 64676716478476792441488121)
    ·
      refine ⟨48507537358857594331116091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64676716478476792441488121 48507537358857594331116091)
      ·
        refine ⟨72761306038286391496674137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48507537358857594331116091 72761306038286391496674137)
        ·
          refine ⟨54570979528714793622505603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72761306038286391496674137 54570979528714793622505603)
          ·
            refine ⟨81856469293072190433758405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54570979528714793622505603 81856469293072190433758405)
            ·
              refine ⟨15348087992451035706329701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81856469293072190433758405 15348087992451035706329701)
              ·
                refine ⟨2877766498584569194936819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15348087992451035706329701 2877766498584569194936819)
                ·
                  refine ⟨4316649747876853792405229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2877766498584569194936819 4316649747876853792405229)
                  ·
                    refine ⟨1618743655453820172151961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4316649747876853792405229 1618743655453820172151961)
                    ·
                      refine ⟨1214057741590365129113971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618743655453820172151961 1214057741590365129113971)
                      ·
                        rfl

theorem cell23_2364369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 3, 2].length) (baseStart_2364369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364369 prefixEnd_2364369 := by exact prefixLift 2364369
  have htrace : WordTrace (prefixWord ++ tailWord_2364369) baseStart_2364369 baseEnd_2364369 := by
    simpa [prefixWord, tailWord_2364369, baseEnd_2364369] using wordTrace_append hprefix tailTrace_2364369
  have hstable : (prefixWord ++ tailWord_2364369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364369).length < 2 ^ (prefixWord ++ tailWord_2364369).sum := by decide
  have hdescent : baseEnd_2364369 < baseStart_2364369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364385 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 5]
def baseStart_2364385 : Nat := 118140960795 + 2364385 * 2 ^ 59
def prefixEnd_2364385 : Nat := 4983230072969 + 3 ^ 40 * 2364385 * 2
def baseEnd_2364385 : Nat := 1214065957280837066513897

theorem tailTrace_2364385 : CollatzResearch.WordTrace tailWord_2364385 prefixEnd_2364385 1214065957280837066513897 := by
  unfold tailWord_2364385
  simp only [CollatzResearch.WordTrace]
  refine ⟨86236205539244424654566609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57490803692829616436377739 86236205539244424654566609)
  ·
    refine ⟨64677154154433318490924957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86236205539244424654566609 64677154154433318490924957)
    ·
      refine ⟨24253932807912494434096859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64677154154433318490924957 24253932807912494434096859)
      ·
        refine ⟨36380899211868741651145289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24253932807912494434096859 36380899211868741651145289)
        ·
          refine ⟨27285674408901556238358967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36380899211868741651145289 27285674408901556238358967)
          ·
            refine ⟨40928511613352334357538451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27285674408901556238358967 40928511613352334357538451)
            ·
              refine ⟨61392767420028501536307677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40928511613352334357538451 61392767420028501536307677)
              ·
                refine ⟨23022287782510688076115379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61392767420028501536307677 23022287782510688076115379)
                ·
                  refine ⟨34533431673766032114173069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23022287782510688076115379 34533431673766032114173069)
                  ·
                    refine ⟨12950036877662262042814901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 34533431673766032114173069 12950036877662262042814901)
                    ·
                      refine ⟨1214065957280837066513897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12950036877662262042814901 1214065957280837066513897)
                      ·
                        rfl

theorem cell23_2364385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_2364385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364385 prefixEnd_2364385 := by exact prefixLift 2364385
  have htrace : WordTrace (prefixWord ++ tailWord_2364385) baseStart_2364385 baseEnd_2364385 := by
    simpa [prefixWord, tailWord_2364385, baseEnd_2364385] using wordTrace_append hprefix tailTrace_2364385
  have hstable : (prefixWord ++ tailWord_2364385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364385).length < 2 ^ (prefixWord ++ tailWord_2364385).sum := by decide
  have hdescent : baseEnd_2364385 < baseStart_2364385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364412 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_2364412 : Nat := 118140960795 + 2364412 * 2 ^ 59
def prefixEnd_2364412 : Nat := 4983230072969 + 3 ^ 40 * 2364412 * 2
def baseEnd_2364412 : Nat := 1214079821258508460876273

theorem tailTrace_2364412 : CollatzResearch.WordTrace tailWord_2364412 prefixEnd_2364412 1214079821258508460876273 := by
  unfold tailWord_2364412
  simp only [CollatzResearch.WordTrace]
  refine ⟨43118595155073304132899745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57491460206764405510532993 43118595155073304132899745)
  ·
    refine ⟨32338946366304978099674809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43118595155073304132899745 32338946366304978099674809)
    ·
      refine ⟨24254209774728733574756107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32338946366304978099674809 24254209774728733574756107)
      ·
        refine ⟨36381314662093100362134161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24254209774728733574756107 36381314662093100362134161)
        ·
          refine ⟨27285985996569825271600621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36381314662093100362134161 27285985996569825271600621)
          ·
            refine ⟨10232244748713684476850233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27285985996569825271600621 10232244748713684476850233)
            ·
              refine ⟨7674183561535263357637675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10232244748713684476850233 7674183561535263357637675)
              ·
                refine ⟨11511275342302895036456513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7674183561535263357637675 11511275342302895036456513)
                ·
                  refine ⟨8633456506727171277342385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11511275342302895036456513 8633456506727171277342385)
                  ·
                    refine ⟨6475092380045378458006789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8633456506727171277342385 6475092380045378458006789)
                    ·
                      refine ⟨1214079821258508460876273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6475092380045378458006789 1214079821258508460876273)
                      ·
                        rfl

theorem cell23_2364412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_2364412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364412 prefixEnd_2364412 := by exact prefixLift 2364412
  have htrace : WordTrace (prefixWord ++ tailWord_2364412) baseStart_2364412 baseEnd_2364412 := by
    simpa [prefixWord, tailWord_2364412, baseEnd_2364412] using wordTrace_append hprefix tailTrace_2364412
  have hstable : (prefixWord ++ tailWord_2364412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364412).length < 2 ^ (prefixWord ++ tailWord_2364412).sum := by decide
  have hdescent : baseEnd_2364412 < baseStart_2364412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364486 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_2364486 : Nat := 118140960795 + 2364486 * 2 ^ 59
def prefixEnd_2364486 : Nat := 4983230072969 + 3 ^ 40 * 2364486 * 2
def baseEnd_2364486 : Nat := 404705939608980390450311

theorem tailTrace_2364486 : CollatzResearch.WordTrace tailWord_2364486 prefixEnd_2364486 404705939608980390450311 := by
  unfold tailWord_2364486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2694996540996203715749791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57493259541252345935995541 2694996540996203715749791)
  ·
    refine ⟨4042494811494305573624687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2694996540996203715749791 4042494811494305573624687)
    ·
      refine ⟨6063742217241458360437031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4042494811494305573624687 6063742217241458360437031)
      ·
        refine ⟨9095613325862187540655547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6063742217241458360437031 9095613325862187540655547)
        ·
          refine ⟨13643419988793281310983321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9095613325862187540655547 13643419988793281310983321)
          ·
            refine ⟨10232564991594960983237491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13643419988793281310983321 10232564991594960983237491)
            ·
              refine ⟨15348847487392441474856237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10232564991594960983237491 15348847487392441474856237)
              ·
                refine ⟨5755817807772165553071089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15348847487392441474856237 5755817807772165553071089)
                ·
                  refine ⟨4316863355829124164803317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5755817807772165553071089 4316863355829124164803317)
                  ·
                    refine ⟨404705939608980390450311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4316863355829124164803317 404705939608980390450311)
                    ·
                      rfl

theorem cell23_2364486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_2364486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364486 prefixEnd_2364486 := by exact prefixLift 2364486
  have htrace : WordTrace (prefixWord ++ tailWord_2364486) baseStart_2364486 baseEnd_2364486 := by
    simpa [prefixWord, tailWord_2364486, baseEnd_2364486] using wordTrace_append hprefix tailTrace_2364486
  have hstable : (prefixWord ++ tailWord_2364486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364486).length < 2 ^ (prefixWord ++ tailWord_2364486).sum := by decide
  have hdescent : baseEnd_2364486 < baseStart_2364486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364533 : List Nat := [1, 3, 4, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2364533 : Nat := 118140960795 + 2364533 * 2 ^ 59
def prefixEnd_2364533 : Nat := 4983230072969 + 3 ^ 40 * 2364533 * 2
def baseEnd_2364533 : Nat := 404713984139234162487739

theorem tailTrace_2364533 : CollatzResearch.WordTrace tailWord_2364533 prefixEnd_2364533 404713984139234162487739 := by
  unfold tailWord_2364533
  simp only [CollatzResearch.WordTrace]
  refine ⟨86241603542708245930954253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57494402361805497287302835 86241603542708245930954253)
  ·
    refine ⟨32340601328515592224107845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86241603542708245930954253 32340601328515592224107845)
    ·
      refine ⟨6063862749096673542020221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32340601328515592224107845 6063862749096673542020221)
      ·
        refine ⟨2273948530911252578257583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6063862749096673542020221 2273948530911252578257583)
        ·
          refine ⟨3410922796366878867386375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273948530911252578257583 3410922796366878867386375)
          ·
            refine ⟨5116384194550318301079563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410922796366878867386375 5116384194550318301079563)
            ·
              refine ⟨7674576291825477451619345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5116384194550318301079563 7674576291825477451619345)
              ·
                refine ⟨5755932218869108088714509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7674576291825477451619345 5755932218869108088714509)
                ·
                  refine ⟨2158474582075915533267941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5755932218869108088714509 2158474582075915533267941)
                  ·
                    refine ⟨404713984139234162487739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2158474582075915533267941 404713984139234162487739)
                    ·
                      rfl

theorem cell23_2364533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2364533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364533 prefixEnd_2364533 := by exact prefixLift 2364533
  have htrace : WordTrace (prefixWord ++ tailWord_2364533) baseStart_2364533 baseEnd_2364533 := by
    simpa [prefixWord, tailWord_2364533, baseEnd_2364533] using wordTrace_append hprefix tailTrace_2364533
  have hstable : (prefixWord ++ tailWord_2364533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364533).length < 2 ^ (prefixWord ++ tailWord_2364533).sum := by decide
  have hdescent : baseEnd_2364533 < baseStart_2364533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364573 : List Nat := [1, 4, 2, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_2364573 : Nat := 118140960795 + 2364573 * 2 ^ 59
def prefixEnd_2364573 : Nat := 4983230072969 + 3 ^ 40 * 2364573 * 2
def baseEnd_2364573 : Nat := 1214162491643882330963033

theorem tailTrace_2364573 : CollatzResearch.WordTrace tailWord_2364573 prefixEnd_2364573 1214162491643882330963033 := by
  unfold tailWord_2364573
  simp only [CollatzResearch.WordTrace]
  refine ⟨86243062462563332762410373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57495374975042221841606915 86243062462563332762410373)
  ·
    refine ⟨16170574211730624892951945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86243062462563332762410373 16170574211730624892951945)
    ·
      refine ⟨12127930658797968669713959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16170574211730624892951945 12127930658797968669713959)
      ·
        refine ⟨18191895988196953004570939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12127930658797968669713959 18191895988196953004570939)
        ·
          refine ⟨27287843982295429506856409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18191895988196953004570939 27287843982295429506856409)
          ·
            refine ⟨20465882986721572130142307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27287843982295429506856409 20465882986721572130142307)
            ·
              refine ⟨30698824480082358195213461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20465882986721572130142307 30698824480082358195213461)
              ·
                refine ⟨1439007397503860540400631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30698824480082358195213461 1439007397503860540400631)
                ·
                  refine ⟨2158511096255790810600947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1439007397503860540400631 2158511096255790810600947)
                  ·
                    refine ⟨3237766644383686215901421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2158511096255790810600947 3237766644383686215901421)
                    ·
                      refine ⟨1214162491643882330963033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3237766644383686215901421 1214162491643882330963033)
                      ·
                        rfl

theorem cell23_2364573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_2364573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364573 prefixEnd_2364573 := by exact prefixLift 2364573
  have htrace : WordTrace (prefixWord ++ tailWord_2364573) baseStart_2364573 baseEnd_2364573 := by
    simpa [prefixWord, tailWord_2364573, baseEnd_2364573] using wordTrace_append hprefix tailTrace_2364573
  have hstable : (prefixWord ++ tailWord_2364573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364573).length < 2 ^ (prefixWord ++ tailWord_2364573).sum := by decide
  have hdescent : baseEnd_2364573 < baseStart_2364573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364592 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 6]
def baseStart_2364592 : Nat := 118140960795 + 2364592 * 2 ^ 59
def prefixEnd_2364592 : Nat := 4983230072969 + 3 ^ 40 * 2364592 * 2
def baseEnd_2364592 : Nat := 1214172247776317756625445

theorem tailTrace_2364592 : CollatzResearch.WordTrace tailWord_2364592 prefixEnd_2364592 1214172247776317756625445 := by
  unfold tailWord_2364592
  simp only [CollatzResearch.WordTrace]
  refine ⟨43121877724747249503676015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57495836966329666004901353 43121877724747249503676015)
  ·
    refine ⟨64682816587120874255514023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43121877724747249503676015 64682816587120874255514023)
    ·
      refine ⟨97024224880681311383271035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64682816587120874255514023 97024224880681311383271035)
      ·
        refine ⟨145536337321021967074906553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97024224880681311383271035 145536337321021967074906553)
        ·
          refine ⟨109152252990766475306179915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145536337321021967074906553 109152252990766475306179915)
          ·
            refine ⟨163728379486149712959269873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109152252990766475306179915 163728379486149712959269873)
            ·
              refine ⟨122796284614612284719452405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163728379486149712959269873 122796284614612284719452405)
              ·
                refine ⟨11512151682619901692448663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122796284614612284719452405 11512151682619901692448663)
                ·
                  refine ⟨17268227523929852538672995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11512151682619901692448663 17268227523929852538672995)
                  ·
                    refine ⟨25902341285894778808009493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17268227523929852538672995 25902341285894778808009493)
                    ·
                      refine ⟨1214172247776317756625445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25902341285894778808009493 1214172247776317756625445)
                      ·
                        rfl

theorem cell23_2364592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_2364592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364592 prefixEnd_2364592 := by exact prefixLift 2364592
  have htrace : WordTrace (prefixWord ++ tailWord_2364592) baseStart_2364592 baseEnd_2364592 := by
    simpa [prefixWord, tailWord_2364592, baseEnd_2364592] using wordTrace_append hprefix tailTrace_2364592
  have hstable : (prefixWord ++ tailWord_2364592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364592).length < 2 ^ (prefixWord ++ tailWord_2364592).sum := by decide
  have hdescent : baseEnd_2364592 < baseStart_2364592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364606 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_2364606 : Nat := 118140960795 + 2364606 * 2 ^ 59
def prefixEnd_2364606 : Nat := 4983230072969 + 3 ^ 40 * 2364606 * 2
def baseEnd_2364606 : Nat := 404726478835160233950127

theorem tailTrace_2364606 : CollatzResearch.WordTrace tailWord_2364606 prefixEnd_2364606 404726478835160233950127 := by
  unfold tailWord_2364606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10780533258930472424795209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57496177380962519598907781 10780533258930472424795209)
  ·
    refine ⟨8085399944197854318596407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10780533258930472424795209 8085399944197854318596407)
    ·
      refine ⟨12128099916296781477894611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8085399944197854318596407 12128099916296781477894611)
      ·
        refine ⟨18192149874445172216841917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12128099916296781477894611 18192149874445172216841917)
        ·
          refine ⟨6822056202916939581315719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18192149874445172216841917 6822056202916939581315719)
          ·
            refine ⟨10233084304375409371973579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6822056202916939581315719 10233084304375409371973579)
            ·
              refine ⟨15349626456563114057960369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10233084304375409371973579 15349626456563114057960369)
              ·
                refine ⟨11512219842422335543470277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15349626456563114057960369 11512219842422335543470277)
                ·
                  refine ⟨2158541220454187914400677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11512219842422335543470277 2158541220454187914400677)
                  ·
                    refine ⟨404726478835160233950127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2158541220454187914400677 404726478835160233950127)
                    ·
                      rfl

theorem cell23_2364606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_2364606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364606 prefixEnd_2364606 := by exact prefixLift 2364606
  have htrace : WordTrace (prefixWord ++ tailWord_2364606) baseStart_2364606 baseEnd_2364606 := by
    simpa [prefixWord, tailWord_2364606, baseEnd_2364606] using wordTrace_append hprefix tailTrace_2364606
  have hstable : (prefixWord ++ tailWord_2364606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364606).length < 2 ^ (prefixWord ++ tailWord_2364606).sum := by decide
  have hdescent : baseEnd_2364606 < baseStart_2364606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364616 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_2364616 : Nat := 118140960795 + 2364616 * 2 ^ 59
def prefixEnd_2364616 : Nat := 4983230072969 + 3 ^ 40 * 2364616 * 2
def baseEnd_2364616 : Nat := 1214184571312025662725335

theorem tailTrace_2364616 : CollatzResearch.WordTrace tailWord_2364616 prefixEnd_2364616 1214184571312025662725335 := by
  unfold tailWord_2364616
  simp only [CollatzResearch.WordTrace]
  refine ⟨43122315400703775553112851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57496420534271700737483801 43122315400703775553112851)
  ·
    refine ⟨64683473101055663329669277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43122315400703775553112851 64683473101055663329669277)
    ·
      refine ⟨24256302412895873748625979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64683473101055663329669277 24256302412895873748625979)
      ·
        refine ⟨36384453619343810622938969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24256302412895873748625979 36384453619343810622938969)
        ·
          refine ⟨27288340214507857967204227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36384453619343810622938969 27288340214507857967204227)
          ·
            refine ⟨40932510321761786950806341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27288340214507857967204227 40932510321761786950806341)
            ·
              refine ⟨7674845685330335053276189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40932510321761786950806341 7674845685330335053276189)
              ·
                refine ⟨2878067131998875644978571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7674845685330335053276189 2878067131998875644978571)
                ·
                  refine ⟨4317100697998313467467857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2878067131998875644978571 4317100697998313467467857)
                  ·
                    refine ⟨3237825523498735100600893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4317100697998313467467857 3237825523498735100600893)
                    ·
                      refine ⟨1214184571312025662725335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3237825523498735100600893 1214184571312025662725335)
                      ·
                        rfl

theorem cell23_2364616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_2364616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364616 prefixEnd_2364616 := by exact prefixLift 2364616
  have htrace : WordTrace (prefixWord ++ tailWord_2364616) baseStart_2364616 baseEnd_2364616 := by
    simpa [prefixWord, tailWord_2364616, baseEnd_2364616] using wordTrace_append hprefix tailTrace_2364616
  have hstable : (prefixWord ++ tailWord_2364616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364616).length < 2 ^ (prefixWord ++ tailWord_2364616).sum := by decide
  have hdescent : baseEnd_2364616 < baseStart_2364616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364680 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_2364680 : Nat := 118140960795 + 2364680 * 2 ^ 59
def prefixEnd_2364680 : Nat := 4983230072969 + 3 ^ 40 * 2364680 * 2
def baseEnd_2364680 : Nat := 1214217434073913412325041

theorem tailTrace_2364680 : CollatzResearch.WordTrace tailWord_2364680 prefixEnd_2364680 1214217434073913412325041 := by
  unfold tailWord_2364680
  simp only [CollatzResearch.WordTrace]
  refine ⟨43123482536587845018277747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57497976715450460024370329 43123482536587845018277747)
  ·
    refine ⟨64685223804881767527416621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43123482536587845018277747 64685223804881767527416621)
    ·
      refine ⟨24256958926830662822781233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64685223804881767527416621 24256958926830662822781233)
      ·
        refine ⟨18192719195122997117085925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24256958926830662822781233 18192719195122997117085925)
        ·
          refine ⟨3411134849085561959453611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18192719195122997117085925 3411134849085561959453611)
          ·
            refine ⟨5116702273628342939180417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3411134849085561959453611 5116702273628342939180417)
            ·
              refine ⟨3837526705221257204385313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5116702273628342939180417 3837526705221257204385313)
              ·
                refine ⟨2878145028915942903288985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3837526705221257204385313 2878145028915942903288985)
                ·
                  refine ⟨2158608771686957177466739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2878145028915942903288985 2158608771686957177466739)
                  ·
                    refine ⟨3237913157530435766200109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2158608771686957177466739 3237913157530435766200109)
                    ·
                      refine ⟨1214217434073913412325041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3237913157530435766200109 1214217434073913412325041)
                      ·
                        rfl

theorem cell23_2364680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_2364680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364680 prefixEnd_2364680 := by exact prefixLift 2364680
  have htrace : WordTrace (prefixWord ++ tailWord_2364680) baseStart_2364680 baseEnd_2364680 := by
    simpa [prefixWord, tailWord_2364680, baseEnd_2364680] using wordTrace_append hprefix tailTrace_2364680
  have hstable : (prefixWord ++ tailWord_2364680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364680).length < 2 ^ (prefixWord ++ tailWord_2364680).sum := by decide
  have hdescent : baseEnd_2364680 < baseStart_2364680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364689 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 3]
def baseStart_2364689 : Nat := 118140960795 + 2364689 * 2 ^ 59
def prefixEnd_2364689 : Nat := 4983230072969 + 3 ^ 40 * 2364689 * 2
def baseEnd_2364689 : Nat := 1214222055399803877112499

theorem tailTrace_2364689 : CollatzResearch.WordTrace tailWord_2364689 prefixEnd_2364689 1214222055399803877112499 := by
  unfold tailWord_2364689
  simp only [CollatzResearch.WordTrace]
  refine ⟨86247293330143084573633121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57498195553428723049088747 86247293330143084573633121)
  ·
    refine ⟨64685469997607313430224841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86247293330143084573633121 64685469997607313430224841)
    ·
      refine ⟨48514102498205485072668631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64685469997607313430224841 48514102498205485072668631)
      ·
        refine ⟨72771153747308227609002947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48514102498205485072668631 72771153747308227609002947)
        ·
          refine ⟨109156730620962341413504421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72771153747308227609002947 109156730620962341413504421)
          ·
            refine ⟨20466886991430439015032079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109156730620962341413504421 20466886991430439015032079)
            ·
              refine ⟨30700330487145658522548119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20466886991430439015032079 30700330487145658522548119)
              ·
                refine ⟨46050495730718487783822179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30700330487145658522548119 46050495730718487783822179)
                ·
                  refine ⟨69075743596077731675733269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46050495730718487783822179 69075743596077731675733269)
                  ·
                    refine ⟨3237925481066143672299997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 69075743596077731675733269 3237925481066143672299997)
                    ·
                      refine ⟨1214222055399803877112499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3237925481066143672299997 1214222055399803877112499)
                      ·
                        rfl

theorem cell23_2364689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 3].length) (baseStart_2364689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364689 prefixEnd_2364689 := by exact prefixLift 2364689
  have htrace : WordTrace (prefixWord ++ tailWord_2364689) baseStart_2364689 baseEnd_2364689 := by
    simpa [prefixWord, tailWord_2364689, baseEnd_2364689] using wordTrace_append hprefix tailTrace_2364689
  have hstable : (prefixWord ++ tailWord_2364689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364689).length < 2 ^ (prefixWord ++ tailWord_2364689).sum := by decide
  have hdescent : baseEnd_2364689 < baseStart_2364689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364709 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 9]
def baseStart_2364709 : Nat := 118140960795 + 2364709 * 2 ^ 59
def prefixEnd_2364709 : Nat := 4983230072969 + 3 ^ 40 * 2364709 * 2
def baseEnd_2364709 : Nat := 134914702779210422095823

theorem tailTrace_2364709 : CollatzResearch.WordTrace tailWord_2364709 prefixEnd_2364709 134914702779210422095823 := by
  unfold tailWord_2364709
  simp only [CollatzResearch.WordTrace]
  refine ⟨86248022790070627989361181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57498681860047085326240787 86248022790070627989361181)
  ·
    refine ⟨32343008546276485496010443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86248022790070627989361181 32343008546276485496010443)
    ·
      refine ⟨48514512819414728244015665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32343008546276485496010443 48514512819414728244015665)
      ·
        refine ⟨36385884614561046183011749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48514512819414728244015665 36385884614561046183011749)
        ·
          refine ⟨6822353365230196159314703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36385884614561046183011749 6822353365230196159314703)
          ·
            refine ⟨10233530047845294238972055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6822353365230196159314703 10233530047845294238972055)
            ·
              refine ⟨15350295071767941358458083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10233530047845294238972055 15350295071767941358458083)
              ·
                refine ⟨23025442607651912037687125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15350295071767941358458083 23025442607651912037687125)
                ·
                  refine ⟨134914702779210422095823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23025442607651912037687125 134914702779210422095823)
                  ·
                    rfl

theorem cell23_2364709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 9].length) (baseStart_2364709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364709 prefixEnd_2364709 := by exact prefixLift 2364709
  have htrace : WordTrace (prefixWord ++ tailWord_2364709) baseStart_2364709 baseEnd_2364709 := by
    simpa [prefixWord, tailWord_2364709, baseEnd_2364709] using wordTrace_append hprefix tailTrace_2364709
  have hstable : (prefixWord ++ tailWord_2364709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364709).length < 2 ^ (prefixWord ++ tailWord_2364709).sum := by decide
  have hdescent : baseEnd_2364709 < baseStart_2364709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364719 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 3]
def baseStart_2364719 : Nat := 118140960795 + 2364719 * 2 ^ 59
def prefixEnd_2364719 : Nat := 4983230072969 + 3 ^ 40 * 2364719 * 2
def baseEnd_2364719 : Nat := 1214237459819438759737361

theorem tailTrace_2364719 : CollatzResearch.WordTrace tailWord_2364719 prefixEnd_2364719 1214237459819438759737361 := by
  unfold tailWord_2364719
  simp only [CollatzResearch.WordTrace]
  refine ⟨86248387520034399697225211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57498925013356266464816807 86248387520034399697225211)
  ·
    refine ⟨129372581280051599545837817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86248387520034399697225211 129372581280051599545837817)
    ·
      refine ⟨97029435960038699659378363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 129372581280051599545837817 97029435960038699659378363)
      ·
        refine ⟨145544153940058049489067545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97029435960038699659378363 145544153940058049489067545)
        ·
          refine ⟨109158115455043537116800659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145544153940058049489067545 109158115455043537116800659)
          ·
            refine ⟨163737173182565305675200989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109158115455043537116800659 163737173182565305675200989)
            ·
              refine ⟨61401439943461989628200371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 163737173182565305675200989 61401439943461989628200371)
              ·
                refine ⟨92102159915192984442300557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61401439943461989628200371 92102159915192984442300557)
                ·
                  refine ⟨34538309968197369165862709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92102159915192984442300557 34538309968197369165862709)
                  ·
                    refine ⟨3237966559518503359299629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 34538309968197369165862709 3237966559518503359299629)
                    ·
                      refine ⟨1214237459819438759737361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3237966559518503359299629 1214237459819438759737361)
                      ·
                        rfl

theorem cell23_2364719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 3].length) (baseStart_2364719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364719 prefixEnd_2364719 := by exact prefixLift 2364719
  have htrace : WordTrace (prefixWord ++ tailWord_2364719) baseStart_2364719 baseEnd_2364719 := by
    simpa [prefixWord, tailWord_2364719, baseEnd_2364719] using wordTrace_append hprefix tailTrace_2364719
  have hstable : (prefixWord ++ tailWord_2364719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364719).length < 2 ^ (prefixWord ++ tailWord_2364719).sum := by decide
  have hdescent : baseEnd_2364719 < baseStart_2364719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364737 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2364737 : Nat := 118140960795 + 2364737 * 2 ^ 59
def prefixEnd_2364737 : Nat := 4983230072969 + 3 ^ 40 * 2364737 * 2
def baseEnd_2364737 : Nat := 1214246702471219689312279

theorem tailTrace_2364737 : CollatzResearch.WordTrace tailWord_2364737 prefixEnd_2364737 1214246702471219689312279 := by
  unfold tailWord_2364737
  simp only [CollatzResearch.WordTrace]
  refine ⟨86249044033969188771380465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57499362689312792514253643 86249044033969188771380465)
  ·
    refine ⟨64686783025476891578535349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86249044033969188771380465 64686783025476891578535349)
    ·
      refine ⟨6064385908638458585487689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64686783025476891578535349 6064385908638458585487689)
      ·
        refine ⟨4548289431478843939115767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6064385908638458585487689 4548289431478843939115767)
        ·
          refine ⟨6822434147218265908673651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4548289431478843939115767 6822434147218265908673651)
          ·
            refine ⟨10233651220827398863010477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6822434147218265908673651 10233651220827398863010477)
            ·
              refine ⟨3837619207810274573628929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10233651220827398863010477 3837619207810274573628929)
              ·
                refine ⟨2878214405857705930221697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3837619207810274573628929 2878214405857705930221697)
                ·
                  refine ⟨2158660804393279447666273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2878214405857705930221697 2158660804393279447666273)
                  ·
                    refine ⟨1618995603294959585749705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2158660804393279447666273 1618995603294959585749705)
                    ·
                      refine ⟨1214246702471219689312279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1618995603294959585749705 1214246702471219689312279)
                      ·
                        rfl

theorem cell23_2364737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2364737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364737 prefixEnd_2364737 := by exact prefixLift 2364737
  have htrace : WordTrace (prefixWord ++ tailWord_2364737) baseStart_2364737 baseEnd_2364737 := by
    simpa [prefixWord, tailWord_2364737, baseEnd_2364737] using wordTrace_append hprefix tailTrace_2364737
  have hstable : (prefixWord ++ tailWord_2364737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364737).length < 2 ^ (prefixWord ++ tailWord_2364737).sum := by decide
  have hdescent : baseEnd_2364737 < baseStart_2364737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364739 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 4, 5]
def baseStart_2364739 : Nat := 118140960795 + 2364739 * 2 ^ 59
def prefixEnd_2364739 : Nat := 4983230072969 + 3 ^ 40 * 2364739 * 2
def baseEnd_2364739 : Nat := 404749243144176227162423

theorem tailTrace_2364739 : CollatzResearch.WordTrace tailWord_2364739 prefixEnd_2364739 404749243144176227162423 := by
  unfold tailWord_2364739
  simp only [CollatzResearch.WordTrace]
  refine ⟨86249116979961943112953271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57499411319974628741968847 86249116979961943112953271)
  ·
    refine ⟨129373675469942914669429907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86249116979961943112953271 129373675469942914669429907)
    ·
      refine ⟨194060513204914372004144861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129373675469942914669429907 194060513204914372004144861)
      ·
        refine ⟨72772692451842889501554323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194060513204914372004144861 72772692451842889501554323)
        ·
          refine ⟨109159038677764334252331485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72772692451842889501554323 109159038677764334252331485)
          ·
            refine ⟨40934639504161625344624307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109159038677764334252331485 40934639504161625344624307)
            ·
              refine ⟨61401959256242438016936461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40934639504161625344624307 61401959256242438016936461)
              ·
                refine ⟨23025734721090914256351173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61401959256242438016936461 23025734721090914256351173)
                ·
                  refine ⟨4317325260204546423065845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23025734721090914256351173 4317325260204546423065845)
                  ·
                    refine ⟨404749243144176227162423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4317325260204546423065845 404749243144176227162423)
                    ·
                      rfl

theorem cell23_2364739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 4, 5].length) (baseStart_2364739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364739 prefixEnd_2364739 := by exact prefixLift 2364739
  have htrace : WordTrace (prefixWord ++ tailWord_2364739) baseStart_2364739 baseEnd_2364739 := by
    simpa [prefixWord, tailWord_2364739, baseEnd_2364739] using wordTrace_append hprefix tailTrace_2364739
  have hstable : (prefixWord ++ tailWord_2364739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364739).length < 2 ^ (prefixWord ++ tailWord_2364739).sum := by decide
  have hdescent : baseEnd_2364739 < baseStart_2364739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364746 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2]
def baseStart_2364746 : Nat := 118140960795 + 2364746 * 2 ^ 59
def prefixEnd_2364746 : Nat := 4983230072969 + 3 ^ 40 * 2364746 * 2
def baseEnd_2364746 : Nat := 1214251323797110154099737

theorem tailTrace_2364746 : CollatzResearch.WordTrace tailWord_2364746 prefixEnd_2364746 1214251323797110154099737 := by
  unfold tailWord_2364746
  simp only [CollatzResearch.WordTrace]
  refine ⟨21562343072734145827114523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57499581527291055538972061 21562343072734145827114523)
  ·
    refine ⟨32343514609101218740671785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21562343072734145827114523 32343514609101218740671785)
    ·
      refine ⟨24257635956825914055503839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32343514609101218740671785 24257635956825914055503839)
      ·
        refine ⟨36386453935238871083255759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24257635956825914055503839 36386453935238871083255759)
        ·
          refine ⟨54579680902858306624883639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36386453935238871083255759 54579680902858306624883639)
          ·
            refine ⟨81869521354287459937325459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54579680902858306624883639 81869521354287459937325459)
            ·
              refine ⟨122804282031431189905988189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81869521354287459937325459 122804282031431189905988189)
              ·
                refine ⟨46051605761786696214745571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122804282031431189905988189 46051605761786696214745571)
                ·
                  refine ⟨69077408642680044322118357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46051605761786696214745571 69077408642680044322118357)
                  ·
                    refine ⟨1619001765062813538799649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 69077408642680044322118357 1619001765062813538799649)
                    ·
                      refine ⟨1214251323797110154099737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1619001765062813538799649 1214251323797110154099737)
                      ·
                        rfl

theorem cell23_2364746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_2364746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364746 prefixEnd_2364746 := by exact prefixLift 2364746
  have htrace : WordTrace (prefixWord ++ tailWord_2364746) baseStart_2364746 baseEnd_2364746 := by
    simpa [prefixWord, tailWord_2364746, baseEnd_2364746] using wordTrace_append hprefix tailTrace_2364746
  have hstable : (prefixWord ++ tailWord_2364746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364746).length < 2 ^ (prefixWord ++ tailWord_2364746).sum := by decide
  have hdescent : baseEnd_2364746 < baseStart_2364746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364803 : List Nat := [1, 1, 1, 3, 5, 1, 3, 1, 3, 4]
def baseStart_2364803 : Nat := 118140960795 + 2364803 * 2 ^ 59
def prefixEnd_2364803 : Nat := 4983230072969 + 3 ^ 40 * 2364803 * 2
def baseEnd_2364803 : Nat := 404760197398138810362325

theorem tailTrace_2364803 : CollatzResearch.WordTrace tailWord_2364803 prefixEnd_2364803 404760197398138810362325 := by
  unfold tailWord_2364803
  simp only [CollatzResearch.WordTrace]
  refine ⟨86251451251730082043283063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57500967501153388028855375 86251451251730082043283063)
  ·
    refine ⟨129377176877595123064924595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86251451251730082043283063 129377176877595123064924595)
    ·
      refine ⟨194065765316392684597386893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129377176877595123064924595 194065765316392684597386893)
      ·
        refine ⟨72774661993647256724020085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 194065765316392684597386893 72774661993647256724020085)
        ·
          refine ⟨6822624561904430317876883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72774661993647256724020085 6822624561904430317876883)
          ·
            refine ⟨10233936842856645476815325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6822624561904430317876883 10233936842856645476815325)
            ·
              refine ⟨3837726316071242053805747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10233936842856645476815325 3837726316071242053805747)
              ·
                refine ⟨5756589474106863080708621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3837726316071242053805747 5756589474106863080708621)
                ·
                  refine ⟨2158721052790073655265733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5756589474106863080708621 2158721052790073655265733)
                  ·
                    refine ⟨404760197398138810362325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2158721052790073655265733 404760197398138810362325)
                    ·
                      rfl

theorem cell23_2364803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 1, 3, 4].length) (baseStart_2364803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364803 prefixEnd_2364803 := by exact prefixLift 2364803
  have htrace : WordTrace (prefixWord ++ tailWord_2364803) baseStart_2364803 baseEnd_2364803 := by
    simpa [prefixWord, tailWord_2364803, baseEnd_2364803] using wordTrace_append hprefix tailTrace_2364803
  have hstable : (prefixWord ++ tailWord_2364803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364803).length < 2 ^ (prefixWord ++ tailWord_2364803).sum := by decide
  have hdescent : baseEnd_2364803 < baseStart_2364803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364859 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 1, 12]
def baseStart_2364859 : Nat := 118140960795 + 2364859 * 2 ^ 59
def prefixEnd_2364859 : Nat := 4983230072969 + 3 ^ 40 * 2364859 * 2
def baseEnd_2364859 : Nat := 404769782370356070662239

theorem tailTrace_2364859 : CollatzResearch.WordTrace tailWord_2364859 prefixEnd_2364859 404769782370356070662239 := by
  unfold tailWord_2364859
  simp only [CollatzResearch.WordTrace]
  refine ⟨86253493739527203607321631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57502329159684802404881087 86253493739527203607321631)
  ·
    refine ⟨129380240609290805410982447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86253493739527203607321631 129380240609290805410982447)
    ·
      refine ⟨194070360913936208116473671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129380240609290805410982447 194070360913936208116473671)
      ·
        refine ⟨291105541370904312174710507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194070360913936208116473671 291105541370904312174710507)
        ·
          refine ⟨436658312056356468262065761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291105541370904312174710507 436658312056356468262065761)
          ·
            refine ⟨327493734042267351196549321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 436658312056356468262065761 327493734042267351196549321)
            ·
              refine ⟨245620300531700513397411991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 327493734042267351196549321 245620300531700513397411991)
              ·
                refine ⟨368430450797550770096117987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245620300531700513397411991 368430450797550770096117987)
                ·
                  refine ⟨552645676196326155144176981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 368430450797550770096117987 552645676196326155144176981)
                  ·
                    refine ⟨404769782370356070662239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 552645676196326155144176981 404769782370356070662239)
                    ·
                      rfl

theorem cell23_2364859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 12].length) (baseStart_2364859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364859 prefixEnd_2364859 := by exact prefixLift 2364859
  have htrace : WordTrace (prefixWord ++ tailWord_2364859) baseStart_2364859 baseEnd_2364859 := by
    simpa [prefixWord, tailWord_2364859, baseEnd_2364859] using wordTrace_append hprefix tailTrace_2364859
  have hstable : (prefixWord ++ tailWord_2364859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364859).length < 2 ^ (prefixWord ++ tailWord_2364859).sum := by decide
  have hdescent : baseEnd_2364859 < baseStart_2364859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2364893 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2364893 : Nat := 118140960795 + 2364893 * 2 ^ 59
def prefixEnd_2364893 : Nat := 4983230072969 + 3 ^ 40 * 2364893 * 2
def baseEnd_2364893 : Nat := 404775601817773692987187

theorem tailTrace_2364893 : CollatzResearch.WordTrace tailWord_2364893 prefixEnd_2364893 404775601817773692987187 := by
  unfold tailWord_2364893
  simp only [CollatzResearch.WordTrace]
  refine ⟨86254733821404027414059333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57503155880936018276039555 86254733821404027414059333)
  ·
    refine ⟨16172762591513255140136125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86254733821404027414059333 16172762591513255140136125)
    ·
      refine ⟨6064785971817470677551047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16172762591513255140136125 6064785971817470677551047)
      ·
        refine ⟨9097178957726206016326571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6064785971817470677551047 9097178957726206016326571)
        ·
          refine ⟨13645768436589309024489857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9097178957726206016326571 13645768436589309024489857)
          ·
            refine ⟨10234326327441981768367393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13645768436589309024489857 10234326327441981768367393)
            ·
              refine ⟨7675744745581486326275545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10234326327441981768367393 7675744745581486326275545)
              ·
                refine ⟨5756808559186114744706659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7675744745581486326275545 5756808559186114744706659)
                ·
                  refine ⟨8635212838779172117059989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5756808559186114744706659 8635212838779172117059989)
                  ·
                    refine ⟨404775601817773692987187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8635212838779172117059989 404775601817773692987187)
                    ·
                      rfl

theorem cell23_2364893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2364893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2364893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2364893 prefixEnd_2364893 := by exact prefixLift 2364893
  have htrace : WordTrace (prefixWord ++ tailWord_2364893) baseStart_2364893 baseEnd_2364893 := by
    simpa [prefixWord, tailWord_2364893, baseEnd_2364893] using wordTrace_append hprefix tailTrace_2364893
  have hstable : (prefixWord ++ tailWord_2364893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2364893).length < 2 ^ (prefixWord ++ tailWord_2364893).sum := by decide
  have hdescent : baseEnd_2364893 < baseStart_2364893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2364893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
