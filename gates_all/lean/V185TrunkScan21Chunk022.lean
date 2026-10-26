import V185TrunkScan21Chunk021

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_266686 : List Nat := [4, 2, 1, 1, 1, 1, 5, 6]
def baseStart_266686 : Nat := 118140960795 + 266686 * 2 ^ 59
def prefixEnd_266686 : Nat := 4983230072969 + 3 ^ 40 * 266686 * 2
def baseEnd_266686 : Nat := 20287126196303529407191

theorem tailTrace_266686 : CollatzResearch.WordTrace tailWord_266686 prefixEnd_266686 20287126196303529407191 := by
  unfold tailWord_266686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1215854688981205398472489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6484558341233095458519941 1215854688981205398472489)
  ·
    refine ⟨911891016735904048854367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1215854688981205398472489 911891016735904048854367)
    ·
      refine ⟨1367836525103856073281551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 911891016735904048854367 1367836525103856073281551)
      ·
        refine ⟨2051754787655784109922327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1367836525103856073281551 2051754787655784109922327)
        ·
          refine ⟨3077632181483676164883491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2051754787655784109922327 3077632181483676164883491)
          ·
            refine ⟨4616448272225514247325237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3077632181483676164883491 4616448272225514247325237)
            ·
              refine ⟨432792025521141960686741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4616448272225514247325237 432792025521141960686741)
              ·
                refine ⟨20287126196303529407191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 432792025521141960686741 20287126196303529407191)
                ·
                  rfl

theorem cell21_266686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_266686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266686 prefixEnd_266686 := by exact prefixLift 266686
  have htrace : WordTrace (prefixWord ++ tailWord_266686) baseStart_266686 baseEnd_266686 := by
    simpa [prefixWord, tailWord_266686, baseEnd_266686] using wordTrace_append hprefix tailTrace_266686
  have hstable : (prefixWord ++ tailWord_266686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266686).length < 2 ^ (prefixWord ++ tailWord_266686).sum := by decide
  have hdescent : baseEnd_266686 < baseStart_266686 := by decide
  rcases family_descends (prefixWord ++ tailWord_266686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266734 : List Nat := [4, 1, 2, 1, 2, 2, 2, 4, 3]
def baseStart_266734 : Nat := 118140960795 + 266734 * 2 ^ 59
def prefixEnd_266734 : Nat := 4983230072969 + 3 ^ 40 * 266734 * 2
def baseEnd_266734 : Nat := 60872332842873171421475

theorem tailTrace_266734 : CollatzResearch.WordTrace tailWord_266734 prefixEnd_266734 60872332842873171421475 := by
  unfold tailWord_266734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216073526959468423190907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6485725477117164923684837 1216073526959468423190907)
  ·
    refine ⟨1824110290439202634786361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1216073526959468423190907 1824110290439202634786361)
    ·
      refine ⟨1368082717829401976089771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1824110290439202634786361 1368082717829401976089771)
      ·
        refine ⟨2052124076744102964134657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1368082717829401976089771 2052124076744102964134657)
        ·
          refine ⟨1539093057558077223100993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2052124076744102964134657 1539093057558077223100993)
          ·
            refine ⟨1154319793168557917325745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1539093057558077223100993 1154319793168557917325745)
            ·
              refine ⟨865739844876418437994309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1154319793168557917325745 865739844876418437994309)
              ·
                refine ⟨162326220914328457123933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 865739844876418437994309 162326220914328457123933)
                ·
                  refine ⟨60872332842873171421475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162326220914328457123933 60872332842873171421475)
                  ·
                    rfl

theorem cell21_266734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_266734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266734 prefixEnd_266734 := by exact prefixLift 266734
  have htrace : WordTrace (prefixWord ++ tailWord_266734) baseStart_266734 baseEnd_266734 := by
    simpa [prefixWord, tailWord_266734, baseEnd_266734] using wordTrace_append hprefix tailTrace_266734
  have hstable : (prefixWord ++ tailWord_266734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266734).length < 2 ^ (prefixWord ++ tailWord_266734).sum := by decide
  have hdescent : baseEnd_266734 < baseStart_266734 := by decide
  rcases family_descends (prefixWord ++ tailWord_266734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266765 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 6]
def baseStart_266765 : Nat := 118140960795 + 266765 * 2 ^ 59
def prefixEnd_266765 : Nat := 4983230072969 + 3 ^ 40 * 266765 * 2
def baseEnd_266765 : Nat := 60879407465224006404745

theorem tailTrace_266765 : CollatzResearch.WordTrace tailWord_266765 prefixEnd_266765 60879407465224006404745 := by
  unfold tailWord_266765
  simp only [CollatzResearch.WordTrace]
  refine ⟨9729718878563439679905749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6486479252375626453270499 9729718878563439679905749)
  ·
    refine ⟨228040286216330617497791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 9729718878563439679905749 228040286216330617497791)
    ·
      refine ⟨342060429324495926246687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 228040286216330617497791 342060429324495926246687)
      ·
        refine ⟨513090643986743889370031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342060429324495926246687 513090643986743889370031)
        ·
          refine ⟨769635965980115834055047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513090643986743889370031 769635965980115834055047)
          ·
            refine ⟨1154453948970173751082571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769635965980115834055047 1154453948970173751082571)
            ·
              refine ⟨1731680923455260626623857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1154453948970173751082571 1731680923455260626623857)
              ·
                refine ⟨1298760692591445469967893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1731680923455260626623857 1298760692591445469967893)
                ·
                  refine ⟨60879407465224006404745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1298760692591445469967893 60879407465224006404745)
                  ·
                    rfl

theorem cell21_266765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_266765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266765 prefixEnd_266765 := by exact prefixLift 266765
  have htrace : WordTrace (prefixWord ++ tailWord_266765) baseStart_266765 baseEnd_266765 := by
    simpa [prefixWord, tailWord_266765, baseEnd_266765] using wordTrace_append hprefix tailTrace_266765
  have hstable : (prefixWord ++ tailWord_266765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266765).length < 2 ^ (prefixWord ++ tailWord_266765).sum := by decide
  have hdescent : baseEnd_266765 < baseStart_266765 := by decide
  rcases family_descends (prefixWord ++ tailWord_266765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266807 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 4]
def baseStart_266807 : Nat := 118140960795 + 266807 * 2 ^ 59
def prefixEnd_266807 : Nat := 4983230072969 + 3 ^ 40 * 266807 * 2
def baseEnd_266807 : Nat := 60888992437441266704659

theorem tailTrace_266807 : CollatzResearch.WordTrace tailWord_266807 prefixEnd_266807 60888992437441266704659 := by
  unfold tailWord_266807
  simp only [CollatzResearch.WordTrace]
  refine ⟨9731250744411280852934675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6487500496274187235289783 9731250744411280852934675)
  ·
    refine ⟨14596876116616921279402013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9731250744411280852934675 14596876116616921279402013)
    ·
      refine ⟨5473828543731345479775755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14596876116616921279402013 5473828543731345479775755)
      ·
        refine ⟨8210742815597018219663633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5473828543731345479775755 8210742815597018219663633)
        ·
          refine ⟨6158057111697763664747725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8210742815597018219663633 6158057111697763664747725)
          ·
            refine ⟨2309271416886661374280397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6158057111697763664747725 2309271416886661374280397)
            ·
              refine ⟨865976781332498015355149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2309271416886661374280397 865976781332498015355149)
              ·
                refine ⟨324741292999686755758181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 865976781332498015355149 324741292999686755758181)
                ·
                  refine ⟨60888992437441266704659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 324741292999686755758181 60888992437441266704659)
                  ·
                    rfl

theorem cell21_266807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 4].length) (baseStart_266807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266807 prefixEnd_266807 := by exact prefixLift 266807
  have htrace : WordTrace (prefixWord ++ tailWord_266807) baseStart_266807 baseEnd_266807 := by
    simpa [prefixWord, tailWord_266807, baseEnd_266807] using wordTrace_append hprefix tailTrace_266807
  have hstable : (prefixWord ++ tailWord_266807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266807).length < 2 ^ (prefixWord ++ tailWord_266807).sum := by decide
  have hdescent : baseEnd_266807 < baseStart_266807 := by decide
  rcases family_descends (prefixWord ++ tailWord_266807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266821 : List Nat := [1, 3, 1, 1, 1, 5, 2, 7]
def baseStart_266821 : Nat := 118140960795 + 266821 * 2 ^ 59
def prefixEnd_266821 : Nat := 4983230072969 + 3 ^ 40 * 266821 * 2
def baseEnd_266821 : Nat := 20297395809393451157099

theorem tailTrace_266821 : CollatzResearch.WordTrace tailWord_266821 prefixEnd_266821 20297395809393451157099 := by
  unfold tailWord_266821
  simp only [CollatzResearch.WordTrace]
  refine ⟨9731761366360561243944317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6487840910907040829296211 9731761366360561243944317)
  ·
    refine ⟨3649410512385210466479119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9731761366360561243944317 3649410512385210466479119)
    ·
      refine ⟨5474115768577815699718679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3649410512385210466479119 5474115768577815699718679)
      ·
        refine ⟨8211173652866723549578019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5474115768577815699718679 8211173652866723549578019)
        ·
          refine ⟨12316760479300085324367029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8211173652866723549578019 12316760479300085324367029)
          ·
            refine ⟨1154696294934382999159409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12316760479300085324367029 1154696294934382999159409)
            ·
              refine ⟨866022221200787249369557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1154696294934382999159409 866022221200787249369557)
              ·
                refine ⟨20297395809393451157099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 866022221200787249369557 20297395809393451157099)
                ·
                  rfl

theorem cell21_266821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 7].length) (baseStart_266821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266821 prefixEnd_266821 := by exact prefixLift 266821
  have htrace : WordTrace (prefixWord ++ tailWord_266821) baseStart_266821 baseEnd_266821 := by
    simpa [prefixWord, tailWord_266821, baseEnd_266821] using wordTrace_append hprefix tailTrace_266821
  have hstable : (prefixWord ++ tailWord_266821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266821).length < 2 ^ (prefixWord ++ tailWord_266821).sum := by decide
  have hdescent : baseEnd_266821 < baseStart_266821 := by decide
  rcases family_descends (prefixWord ++ tailWord_266821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266838 : List Nat := [5, 2, 2, 12]
def baseStart_266838 : Nat := 118140960795 + 266838 * 2 ^ 59
def prefixEnd_266838 : Nat := 4983230072969 + 3 ^ 40 * 266838 * 2
def baseEnd_266838 : Nat := 250601099011490130403

theorem tailTrace_266838 : CollatzResearch.WordTrace tailWord_266838 prefixEnd_266838 250601099011490130403 := by
  unfold tailWord_266838
  simp only [CollatzResearch.WordTrace]
  refine ⟨608273837956185821707073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6488254271532648764875445 608273837956185821707073)
  ·
    refine ⟨456205378467139366280305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 608273837956185821707073 456205378467139366280305)
    ·
      refine ⟨342154033850354524710229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456205378467139366280305 342154033850354524710229)
      ·
        refine ⟨250601099011490130403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 342154033850354524710229 250601099011490130403)
        ·
          rfl

theorem cell21_266838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 12].length) (baseStart_266838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266838 prefixEnd_266838 := by exact prefixLift 266838
  have htrace : WordTrace (prefixWord ++ tailWord_266838) baseStart_266838 baseEnd_266838 := by
    simpa [prefixWord, tailWord_266838, baseEnd_266838] using wordTrace_append hprefix tailTrace_266838
  have hstable : (prefixWord ++ tailWord_266838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266838).length < 2 ^ (prefixWord ++ tailWord_266838).sum := by decide
  have hdescent : baseEnd_266838 < baseStart_266838 := by decide
  rcases family_descends (prefixWord ++ tailWord_266838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266844 : List Nat := [2, 2, 4, 1, 3, 2, 2, 2, 3]
def baseStart_266844 : Nat := 118140960795 + 266844 * 2 ^ 59
def prefixEnd_266844 : Nat := 4983230072969 + 3 ^ 40 * 266844 * 2
def baseEnd_266844 : Nat := 60897436341537424587917

theorem tailTrace_266844 : CollatzResearch.WordTrace tailWord_266844 prefixEnd_266844 60897436341537424587917 := by
  unfold tailWord_266844
  simp only [CollatzResearch.WordTrace]
  refine ⟨4866300122638618086015793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6488400163518157448021057 4866300122638618086015793)
  ·
    refine ⟨3649725091978963564511845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4866300122638618086015793 3649725091978963564511845)
    ·
      refine ⟨684323454746055668345971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3649725091978963564511845 684323454746055668345971)
      ·
        refine ⟨1026485182119083502518957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684323454746055668345971 1026485182119083502518957)
        ·
          refine ⟨384931943294656313444609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1026485182119083502518957 384931943294656313444609)
          ·
            refine ⟨288698957470992235083457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384931943294656313444609 288698957470992235083457)
            ·
              refine ⟨216524218103244176312593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288698957470992235083457 216524218103244176312593)
              ·
                refine ⟨162393163577433132234445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216524218103244176312593 162393163577433132234445)
                ·
                  refine ⟨60897436341537424587917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162393163577433132234445 60897436341537424587917)
                  ·
                    rfl

theorem cell21_266844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_266844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266844 prefixEnd_266844 := by exact prefixLift 266844
  have htrace : WordTrace (prefixWord ++ tailWord_266844) baseStart_266844 baseEnd_266844 := by
    simpa [prefixWord, tailWord_266844, baseEnd_266844] using wordTrace_append hprefix tailTrace_266844
  have hstable : (prefixWord ++ tailWord_266844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266844).length < 2 ^ (prefixWord ++ tailWord_266844).sum := by decide
  have hdescent : baseEnd_266844 < baseStart_266844 := by decide
  rcases family_descends (prefixWord ++ tailWord_266844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266852 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_266852 : Nat := 118140960795 + 266852 * 2 ^ 59
def prefixEnd_266852 : Nat := 4983230072969 + 3 ^ 40 * 266852 * 2
def baseEnd_266852 : Nat := 60899262050531188454567

theorem tailTrace_266852 : CollatzResearch.WordTrace tailWord_266852 prefixEnd_266852 60899262050531188454567 := by
  unfold tailWord_266852
  simp only [CollatzResearch.WordTrace]
  refine ⟨4866446014624126769161405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6488594686165502358881873 4866446014624126769161405)
  ·
    refine ⟨1824917255484047538435527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4866446014624126769161405 1824917255484047538435527)
    ·
      refine ⟨2737375883226071307653291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1824917255484047538435527 2737375883226071307653291)
      ·
        refine ⟨4106063824839106961479937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2737375883226071307653291 4106063824839106961479937)
        ·
          refine ⟨3079547868629330221109953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4106063824839106961479937 3079547868629330221109953)
          ·
            refine ⟨2309660901471997665832465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3079547868629330221109953 2309660901471997665832465)
            ·
              refine ⟨1732245676103998249374349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2309660901471997665832465 1732245676103998249374349)
              ·
                refine ⟨649592128538999343515381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1732245676103998249374349 649592128538999343515381)
                ·
                  refine ⟨60899262050531188454567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 649592128538999343515381 60899262050531188454567)
                  ·
                    rfl

theorem cell21_266852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_266852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266852 prefixEnd_266852 := by exact prefixLift 266852
  have htrace : WordTrace (prefixWord ++ tailWord_266852) baseStart_266852 baseEnd_266852 := by
    simpa [prefixWord, tailWord_266852, baseEnd_266852] using wordTrace_append hprefix tailTrace_266852
  have hstable : (prefixWord ++ tailWord_266852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266852).length < 2 ^ (prefixWord ++ tailWord_266852).sum := by decide
  have hdescent : baseEnd_266852 < baseStart_266852 := by decide
  rcases family_descends (prefixWord ++ tailWord_266852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266900 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 6]
def baseStart_266900 : Nat := 118140960795 + 266900 * 2 ^ 59
def prefixEnd_266900 : Nat := 4983230072969 + 3 ^ 40 * 266900 * 2
def baseEnd_266900 : Nat := 60910216304493771654469

theorem tailTrace_266900 : CollatzResearch.WordTrace tailWord_266900 prefixEnd_266900 60910216304493771654469 := by
  unfold tailWord_266900
  simp only [CollatzResearch.WordTrace]
  refine ⟨4867321366537178868035077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6489761822049571824046769 4867321366537178868035077)
  ·
    refine ⟨912622756225721037756577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4867321366537178868035077 912622756225721037756577)
    ·
      refine ⟨684467067169290778317433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 912622756225721037756577 684467067169290778317433)
      ·
        refine ⟨513350300376968083738075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 684467067169290778317433 513350300376968083738075)
        ·
          refine ⟨770025450565452125607113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513350300376968083738075 770025450565452125607113)
          ·
            refine ⟨577519087924089094205335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770025450565452125607113 577519087924089094205335)
            ·
              refine ⟨866278631886133641308003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577519087924089094205335 866278631886133641308003)
              ·
                refine ⟨1299417947829200461962005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866278631886133641308003 1299417947829200461962005)
                ·
                  refine ⟨60910216304493771654469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1299417947829200461962005 60910216304493771654469)
                  ·
                    rfl

theorem cell21_266900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_266900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266900 prefixEnd_266900 := by exact prefixLift 266900
  have htrace : WordTrace (prefixWord ++ tailWord_266900) baseStart_266900 baseEnd_266900 := by
    simpa [prefixWord, tailWord_266900, baseEnd_266900] using wordTrace_append hprefix tailTrace_266900
  have hstable : (prefixWord ++ tailWord_266900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266900).length < 2 ^ (prefixWord ++ tailWord_266900).sum := by decide
  have hdescent : baseEnd_266900 < baseStart_266900 := by decide
  rcases family_descends (prefixWord ++ tailWord_266900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266962 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_266962 : Nat := 118140960795 + 266962 * 2 ^ 59
def prefixEnd_266962 : Nat := 4983230072969 + 3 ^ 40 * 266962 * 2
def baseEnd_266962 : Nat := 60924365549195441621009

theorem tailTrace_266962 : CollatzResearch.WordTrace tailWord_266962 prefixEnd_266962 60924365549195441621009 := by
  unfold tailWord_266962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2434226014712435581206785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6491269372566494883218093 2434226014712435581206785)
  ·
    refine ⟨1825669511034326685905089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2434226014712435581206785 1825669511034326685905089)
    ·
      refine ⟨1369252133275745014428817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1825669511034326685905089 1369252133275745014428817)
      ·
        refine ⟨1026939099956808760821613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1369252133275745014428817 1026939099956808760821613)
        ·
          refine ⟨385102162483803285308105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1026939099956808760821613 385102162483803285308105)
          ·
            refine ⟨288826621862852463981079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385102162483803285308105 288826621862852463981079)
            ·
              refine ⟨433239932794278695971619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288826621862852463981079 433239932794278695971619)
              ·
                refine ⟨649859899191418043957429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433239932794278695971619 649859899191418043957429)
                ·
                  refine ⟨60924365549195441621009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 649859899191418043957429 60924365549195441621009)
                  ·
                    rfl

theorem cell21_266962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_266962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266962 prefixEnd_266962 := by exact prefixLift 266962
  have htrace : WordTrace (prefixWord ++ tailWord_266962) baseStart_266962 baseEnd_266962 := by
    simpa [prefixWord, tailWord_266962, baseEnd_266962] using wordTrace_append hprefix tailTrace_266962
  have hstable : (prefixWord ++ tailWord_266962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266962).length < 2 ^ (prefixWord ++ tailWord_266962).sum := by decide
  have hdescent : baseEnd_266962 < baseStart_266962 := by decide
  rcases family_descends (prefixWord ++ tailWord_266962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266987 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 7]
def baseStart_266987 : Nat := 118140960795 + 266987 * 2 ^ 59
def prefixEnd_266987 : Nat := 4983230072969 + 3 ^ 40 * 266987 * 2
def baseEnd_266987 : Nat := 60930070889800953704291

theorem tailTrace_266987 : CollatzResearch.WordTrace tailWord_266987 prefixEnd_266987 60930070889800953704291 := by
  unfold tailWord_266987
  simp only [CollatzResearch.WordTrace]
  refine ⟨9737815883759171594487215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6491877255839447729658143 9737815883759171594487215)
  ·
    refine ⟨14606723825638757391730823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9737815883759171594487215 14606723825638757391730823)
    ·
      refine ⟨21910085738458136087596235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14606723825638757391730823 21910085738458136087596235)
      ·
        refine ⟨32865128607687204131394353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21910085738458136087596235 32865128607687204131394353)
        ·
          refine ⟨24648846455765403098545765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32865128607687204131394353 24648846455765403098545765)
          ·
            refine ⟨4621658710456013080977331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24648846455765403098545765 4621658710456013080977331)
            ·
              refine ⟨6932488065684019621465997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4621658710456013080977331 6932488065684019621465997)
              ·
                refine ⟨2599683024631507358049749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6932488065684019621465997 2599683024631507358049749)
                ·
                  refine ⟨60930070889800953704291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2599683024631507358049749 60930070889800953704291)
                  ·
                    rfl

theorem cell21_266987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_266987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_266987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_266987 prefixEnd_266987 := by exact prefixLift 266987
  have htrace : WordTrace (prefixWord ++ tailWord_266987) baseStart_266987 baseEnd_266987 := by
    simpa [prefixWord, tailWord_266987, baseEnd_266987] using wordTrace_append hprefix tailTrace_266987
  have hstable : (prefixWord ++ tailWord_266987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266987).length < 2 ^ (prefixWord ++ tailWord_266987).sum := by decide
  have hdescent : baseEnd_266987 < baseStart_266987 := by decide
  rcases family_descends (prefixWord ++ tailWord_266987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267063 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 7]
def baseStart_267063 : Nat := 118140960795 + 267063 * 2 ^ 59
def prefixEnd_267063 : Nat := 4983230072969 + 3 ^ 40 * 267063 * 2
def baseEnd_267063 : Nat := 60947415125241710437469

theorem tailTrace_267063 : CollatzResearch.WordTrace tailWord_267063 prefixEnd_267063 60947415125241710437469 := by
  unfold tailWord_267063
  simp only [CollatzResearch.WordTrace]
  refine ⟨9740587831483836574253843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6493725220989224382835895 9740587831483836574253843)
  ·
    refine ⟨14610881747225754861380765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9740587831483836574253843 14610881747225754861380765)
    ·
      refine ⟨5479080655209658073017787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14610881747225754861380765 5479080655209658073017787)
      ·
        refine ⟨8218620982814487109526681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5479080655209658073017787 8218620982814487109526681)
        ·
          refine ⟨6163965737110865332145011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8218620982814487109526681 6163965737110865332145011)
          ·
            refine ⟨9245948605666297998217517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6163965737110865332145011 9245948605666297998217517)
            ·
              refine ⟨3467230727124861749331569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9245948605666297998217517 3467230727124861749331569)
              ·
                refine ⟨2600423045343646311998677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3467230727124861749331569 2600423045343646311998677)
                ·
                  refine ⟨60947415125241710437469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2600423045343646311998677 60947415125241710437469)
                  ·
                    rfl

theorem cell21_267063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_267063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267063 prefixEnd_267063 := by exact prefixLift 267063
  have htrace : WordTrace (prefixWord ++ tailWord_267063) baseStart_267063 baseEnd_267063 := by
    simpa [prefixWord, tailWord_267063, baseEnd_267063] using wordTrace_append hprefix tailTrace_267063
  have hstable : (prefixWord ++ tailWord_267063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267063).length < 2 ^ (prefixWord ++ tailWord_267063).sum := by decide
  have hdescent : baseEnd_267063 < baseStart_267063 := by decide
  rcases family_descends (prefixWord ++ tailWord_267063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267069 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 4]
def baseStart_267069 : Nat := 118140960795 + 267069 * 2 ^ 59
def prefixEnd_267069 : Nat := 4983230072969 + 3 ^ 40 * 267069 * 2
def baseEnd_267069 : Nat := 60948784406987033337457

theorem tailTrace_267069 : CollatzResearch.WordTrace tailWord_267069 prefixEnd_267069 60948784406987033337457 := by
  unfold tailWord_267069
  simp only [CollatzResearch.WordTrace]
  refine ⟨9740806669462099598972261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6493871112974733065981507 9740806669462099598972261)
  ·
    refine ⟨1826401250524143674807299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9740806669462099598972261 1826401250524143674807299)
    ·
      refine ⟨2739601875786215512210949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1826401250524143674807299 2739601875786215512210949)
      ·
        refine ⟨513675351709915408539553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2739601875786215512210949 513675351709915408539553)
        ·
          refine ⟨385256513782436556404665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 513675351709915408539553 385256513782436556404665)
          ·
            refine ⟨288942385336827417303499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385256513782436556404665 288942385336827417303499)
            ·
              refine ⟨433413578005241125955249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288942385336827417303499 433413578005241125955249)
              ·
                refine ⟨325060183503930844466437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433413578005241125955249 325060183503930844466437)
                ·
                  refine ⟨60948784406987033337457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325060183503930844466437 60948784406987033337457)
                  ·
                    rfl

theorem cell21_267069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_267069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267069 prefixEnd_267069 := by exact prefixLift 267069
  have htrace : WordTrace (prefixWord ++ tailWord_267069) baseStart_267069 baseEnd_267069 := by
    simpa [prefixWord, tailWord_267069, baseEnd_267069] using wordTrace_append hprefix tailTrace_267069
  have hstable : (prefixWord ++ tailWord_267069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267069).length < 2 ^ (prefixWord ++ tailWord_267069).sum := by decide
  have hdescent : baseEnd_267069 < baseStart_267069 := by decide
  rcases family_descends (prefixWord ++ tailWord_267069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267080 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 5]
def baseStart_267080 : Nat := 118140960795 + 267080 * 2 ^ 59
def prefixEnd_267080 : Nat := 4983230072969 + 3 ^ 40 * 267080 * 2
def baseEnd_267080 : Nat := 60951294756853458654101

theorem tailTrace_267080 : CollatzResearch.WordTrace tailWord_267080 prefixEnd_267080 60951294756853458654101 := by
  unfold tailWord_267080
  simp only [CollatzResearch.WordTrace]
  refine ⟨4870603936211124238811347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6494138581614832318415129 4870603936211124238811347)
  ·
    refine ⟨7305905904316686358217021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4870603936211124238811347 7305905904316686358217021)
    ·
      refine ⟨2739714714118757384331383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7305905904316686358217021 2739714714118757384331383)
      ·
        refine ⟨4109572071178136076497075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2739714714118757384331383 4109572071178136076497075)
        ·
          refine ⟨6164358106767204114745613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4109572071178136076497075 6164358106767204114745613)
          ·
            refine ⟨2311634290037701543029605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6164358106767204114745613 2311634290037701543029605)
            ·
              refine ⟨433431429382069039318051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2311634290037701543029605 433431429382069039318051)
              ·
                refine ⟨650147144073103558977077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 433431429382069039318051 650147144073103558977077)
                ·
                  refine ⟨60951294756853458654101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 650147144073103558977077 60951294756853458654101)
                  ·
                    rfl

theorem cell21_267080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_267080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267080 prefixEnd_267080 := by exact prefixLift 267080
  have htrace : WordTrace (prefixWord ++ tailWord_267080) baseStart_267080 baseEnd_267080 := by
    simpa [prefixWord, tailWord_267080, baseEnd_267080] using wordTrace_append hprefix tailTrace_267080
  have hstable : (prefixWord ++ tailWord_267080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267080).length < 2 ^ (prefixWord ++ tailWord_267080).sum := by decide
  have hdescent : baseEnd_267080 < baseStart_267080 := by decide
  rcases family_descends (prefixWord ++ tailWord_267080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267125 : List Nat := [1, 3, 4, 1, 1, 2, 9]
def baseStart_267125 : Nat := 118140960795 + 267125 * 2 ^ 59
def prefixEnd_267125 : Nat := 4983230072969 + 3 ^ 40 * 267125 * 2
def baseEnd_267125 : Nat := 6773507152215931156001

theorem tailTrace_267125 : CollatzResearch.WordTrace tailWord_267125 prefixEnd_267125 6773507152215931156001 := by
  unfold tailWord_267125
  simp only [CollatzResearch.WordTrace]
  refine ⟨9742849157259221163010829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6495232771506147442007219 9742849157259221163010829)
  ·
    refine ⟨3653568433972207936129061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9742849157259221163010829 3653568433972207936129061)
    ·
      refine ⟨685044081369788988024199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3653568433972207936129061 685044081369788988024199)
      ·
        refine ⟨1027566122054683482036299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685044081369788988024199 1027566122054683482036299)
        ·
          refine ⟨1541349183082025223054449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027566122054683482036299 1541349183082025223054449)
          ·
            refine ⟨1156011887311518917290837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1541349183082025223054449 1156011887311518917290837)
            ·
              refine ⟨6773507152215931156001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1156011887311518917290837 6773507152215931156001)
              ·
                rfl

theorem cell21_267125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 9].length) (baseStart_267125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267125 prefixEnd_267125 := by exact prefixLift 267125
  have htrace : WordTrace (prefixWord ++ tailWord_267125) baseStart_267125 baseEnd_267125 := by
    simpa [prefixWord, tailWord_267125, baseEnd_267125] using wordTrace_append hprefix tailTrace_267125
  have hstable : (prefixWord ++ tailWord_267125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267125).length < 2 ^ (prefixWord ++ tailWord_267125).sum := by decide
  have hdescent : baseEnd_267125 < baseStart_267125 := by decide
  rcases family_descends (prefixWord ++ tailWord_267125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267156 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_267156 : Nat := 118140960795 + 267156 * 2 ^ 59
def prefixEnd_267156 : Nat := 4983230072969 + 3 ^ 40 * 267156 * 2
def baseEnd_267156 : Nat := 60968638992294215387279

theorem tailTrace_267156 : CollatzResearch.WordTrace tailWord_267156 prefixEnd_267156 60968638992294215387279 := by
  unfold tailWord_267156
  simp only [CollatzResearch.WordTrace]
  refine ⟨4871989910073456728694661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6495986546764608971592881 4871989910073456728694661)
  ·
    refine ⟨913498108138773136630249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4871989910073456728694661 913498108138773136630249)
    ·
      refine ⟨685123581104079852472687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 913498108138773136630249 685123581104079852472687)
      ·
        refine ⟨1027685371656119778709031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685123581104079852472687 1027685371656119778709031)
        ·
          refine ⟨1541528057484179668063547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1027685371656119778709031 1541528057484179668063547)
          ·
            refine ⟨2312292086226269502095321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1541528057484179668063547 2312292086226269502095321)
            ·
              refine ⟨1734219064669702126571491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2312292086226269502095321 1734219064669702126571491)
              ·
                refine ⟨2601328597004553189857237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734219064669702126571491 2601328597004553189857237)
                ·
                  refine ⟨60968638992294215387279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2601328597004553189857237 60968638992294215387279)
                  ·
                    rfl

theorem cell21_267156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_267156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267156 prefixEnd_267156 := by exact prefixLift 267156
  have htrace : WordTrace (prefixWord ++ tailWord_267156) baseStart_267156 baseEnd_267156 := by
    simpa [prefixWord, tailWord_267156, baseEnd_267156] using wordTrace_append hprefix tailTrace_267156
  have hstable : (prefixWord ++ tailWord_267156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267156).length < 2 ^ (prefixWord ++ tailWord_267156).sum := by decide
  have hdescent : baseEnd_267156 < baseStart_267156 := by decide
  rcases family_descends (prefixWord ++ tailWord_267156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267215 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 7]
def baseStart_267215 : Nat := 118140960795 + 267215 * 2 ^ 59
def prefixEnd_267215 : Nat := 4983230072969 + 3 ^ 40 * 267215 * 2
def baseEnd_267215 : Nat := 60982103596123223903825

theorem tailTrace_267215 : CollatzResearch.WordTrace tailWord_267215 prefixEnd_267215 60982103596123223903825 := by
  unfold tailWord_267215
  simp only [CollatzResearch.WordTrace]
  refine ⟨9746131726933166533787099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6497421151288777689191399 9746131726933166533787099)
  ·
    refine ⟨14619197590399749800680649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9746131726933166533787099 14619197590399749800680649)
    ·
      refine ⟨10964398192799812350510487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14619197590399749800680649 10964398192799812350510487)
      ·
        refine ⟨16446597289199718525765731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10964398192799812350510487 16446597289199718525765731)
        ·
          refine ⟨24669895933799577788648597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16446597289199718525765731 24669895933799577788648597)
          ·
            refine ⟨1156401371896855208842903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24669895933799577788648597 1156401371896855208842903)
            ·
              refine ⟨1734602057845282813264355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156401371896855208842903 1734602057845282813264355)
              ·
                refine ⟨2601903086767924219896533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1734602057845282813264355 2601903086767924219896533)
                ·
                  refine ⟨60982103596123223903825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2601903086767924219896533 60982103596123223903825)
                  ·
                    rfl

theorem cell21_267215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_267215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267215 prefixEnd_267215 := by exact prefixLift 267215
  have htrace : WordTrace (prefixWord ++ tailWord_267215) baseStart_267215 baseEnd_267215 := by
    simpa [prefixWord, tailWord_267215, baseEnd_267215] using wordTrace_append hprefix tailTrace_267215
  have hstable : (prefixWord ++ tailWord_267215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267215).length < 2 ^ (prefixWord ++ tailWord_267215).sum := by decide
  have hdescent : baseEnd_267215 < baseStart_267215 := by decide
  rcases family_descends (prefixWord ++ tailWord_267215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267249 : List Nat := [1, 2, 2, 2, 4, 1, 2, 4, 3]
def baseStart_267249 : Nat := 118140960795 + 267249 * 2 ^ 59
def prefixEnd_267249 : Nat := 4983230072969 + 3 ^ 40 * 267249 * 2
def baseEnd_267249 : Nat := 60989862859346720337089

theorem tailTrace_267249 : CollatzResearch.WordTrace tailWord_267249 prefixEnd_267249 60989862859346720337089 := by
  unfold tailWord_267249
  simp only [CollatzResearch.WordTrace]
  refine ⟨9747371808809990340524801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6498247872539993560349867 9747371808809990340524801)
  ·
    refine ⟨7310528856607492755393601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9747371808809990340524801 7310528856607492755393601)
    ·
      refine ⟨5482896642455619566545201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7310528856607492755393601 5482896642455619566545201)
      ·
        refine ⟨4112172481841714674908901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5482896642455619566545201 4112172481841714674908901)
        ·
          refine ⟨771032340345321501545419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4112172481841714674908901 771032340345321501545419)
          ·
            refine ⟨1156548510517982252318129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771032340345321501545419 1156548510517982252318129)
            ·
              refine ⟨867411382888486689238597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1156548510517982252318129 867411382888486689238597)
              ·
                refine ⟨162639634291591254232237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 867411382888486689238597 162639634291591254232237)
                ·
                  refine ⟨60989862859346720337089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162639634291591254232237 60989862859346720337089)
                  ·
                    rfl

theorem cell21_267249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 3].length) (baseStart_267249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267249 prefixEnd_267249 := by exact prefixLift 267249
  have htrace : WordTrace (prefixWord ++ tailWord_267249) baseStart_267249 baseEnd_267249 := by
    simpa [prefixWord, tailWord_267249, baseEnd_267249] using wordTrace_append hprefix tailTrace_267249
  have hstable : (prefixWord ++ tailWord_267249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267249).length < 2 ^ (prefixWord ++ tailWord_267249).sum := by decide
  have hdescent : baseEnd_267249 < baseStart_267249 := by decide
  rcases family_descends (prefixWord ++ tailWord_267249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267336 : List Nat := [2, 1, 3, 1, 1, 1, 3, 9]
def baseStart_267336 : Nat := 118140960795 + 267336 * 2 ^ 59
def prefixEnd_267336 : Nat := 4983230072969 + 3 ^ 40 * 267336 * 2
def baseEnd_267336 : Nat := 20336572481551300795637

theorem tailTrace_267336 : CollatzResearch.WordTrace tailWord_267336 prefixEnd_267336 20336572481551300795637 := by
  unfold tailWord_267336
  simp only [CollatzResearch.WordTrace]
  refine ⟨4875272479747402099470931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6500363306329869465961241 4875272479747402099470931)
  ·
    refine ⟨7312908719621103149206397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4875272479747402099470931 7312908719621103149206397)
    ·
      refine ⟨2742340769857913680952399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7312908719621103149206397 2742340769857913680952399)
      ·
        refine ⟨4113511154786870521428599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2742340769857913680952399 4113511154786870521428599)
        ·
          refine ⟨6170266732180305782142899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4113511154786870521428599 6170266732180305782142899)
          ·
            refine ⟨9255400098270458673214349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6170266732180305782142899 9255400098270458673214349)
            ·
              refine ⟨3470775036851422002455381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9255400098270458673214349 3470775036851422002455381)
              ·
                refine ⟨20336572481551300795637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3470775036851422002455381 20336572481551300795637)
                ·
                  rfl

theorem cell21_267336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_267336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267336 prefixEnd_267336 := by exact prefixLift 267336
  have htrace : WordTrace (prefixWord ++ tailWord_267336) baseStart_267336 baseEnd_267336 := by
    simpa [prefixWord, tailWord_267336, baseEnd_267336] using wordTrace_append hprefix tailTrace_267336
  have hstable : (prefixWord ++ tailWord_267336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267336).length < 2 ^ (prefixWord ++ tailWord_267336).sum := by decide
  have hdescent : baseEnd_267336 < baseStart_267336 := by decide
  rcases family_descends (prefixWord ++ tailWord_267336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267370 : List Nat := [3, 1, 3, 2, 2, 3, 1, 6]
def baseStart_267370 : Nat := 118140960795 + 267370 * 2 ^ 59
def prefixEnd_267370 : Nat := 4983230072969 + 3 ^ 40 * 267370 * 2
def baseEnd_267370 : Nat := 20339158902625799606725

theorem tailTrace_267370 : CollatzResearch.WordTrace tailWord_267370 prefixEnd_267370 20339158902625799606725 := by
  unfold tailWord_267370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437946260342907001419891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6501190027581085337119709 2437946260342907001419891)
  ·
    refine ⟨3656919390514360502129837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2437946260342907001419891 3656919390514360502129837)
    ·
      refine ⟨1371344771442885188298689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3656919390514360502129837 1371344771442885188298689)
      ·
        refine ⟨1028508578582163891224017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1371344771442885188298689 1028508578582163891224017)
        ·
          refine ⟨771381433936622918418013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1028508578582163891224017 771381433936622918418013)
          ·
            refine ⟨289268037726233594406755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 771381433936622918418013 289268037726233594406755)
            ·
              refine ⟨433902056589350391610133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289268037726233594406755 433902056589350391610133)
              ·
                refine ⟨20339158902625799606725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 433902056589350391610133 20339158902625799606725)
                ·
                  rfl

theorem cell21_267370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_267370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267370 prefixEnd_267370 := by exact prefixLift 267370
  have htrace : WordTrace (prefixWord ++ tailWord_267370) baseStart_267370 baseEnd_267370 := by
    simpa [prefixWord, tailWord_267370, baseEnd_267370] using wordTrace_append hprefix tailTrace_267370
  have hstable : (prefixWord ++ tailWord_267370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267370).length < 2 ^ (prefixWord ++ tailWord_267370).sum := by decide
  have hdescent : baseEnd_267370 < baseStart_267370 := by decide
  rcases family_descends (prefixWord ++ tailWord_267370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267401 : List Nat := [1, 2, 1, 1, 4, 4, 2, 3, 3]
def baseStart_267401 : Nat := 118140960795 + 267401 * 2 ^ 59
def prefixEnd_267401 : Nat := 4983230072969 + 3 ^ 40 * 267401 * 2
def baseEnd_267401 : Nat := 61024551330228233803445

theorem tailTrace_267401 : CollatzResearch.WordTrace tailWord_267401 prefixEnd_267401 61024551330228233803445 := by
  unfold tailWord_267401
  simp only [CollatzResearch.WordTrace]
  refine ⟨9752915704259320300058057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6501943802839546866705371 9752915704259320300058057)
  ·
    refine ⟨7314686778194490225043543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9752915704259320300058057 7314686778194490225043543)
    ·
      refine ⟨10972030167291735337565315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7314686778194490225043543 10972030167291735337565315)
      ·
        refine ⟨16458045250937603006347973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10972030167291735337565315 16458045250937603006347973)
        ·
          refine ⟨3085883484550800563690245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16458045250937603006347973 3085883484550800563690245)
          ·
            refine ⟨578603153353275105691921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3085883484550800563690245 578603153353275105691921)
            ·
              refine ⟨433952365014956329268941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578603153353275105691921 433952365014956329268941)
              ·
                refine ⟨162732136880608623475853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433952365014956329268941 162732136880608623475853)
                ·
                  refine ⟨61024551330228233803445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162732136880608623475853 61024551330228233803445)
                  ·
                    rfl

theorem cell21_267401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 3].length) (baseStart_267401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267401 prefixEnd_267401 := by exact prefixLift 267401
  have htrace : WordTrace (prefixWord ++ tailWord_267401) baseStart_267401 baseEnd_267401 := by
    simpa [prefixWord, tailWord_267401, baseEnd_267401] using wordTrace_append hprefix tailTrace_267401
  have hstable : (prefixWord ++ tailWord_267401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267401).length < 2 ^ (prefixWord ++ tailWord_267401).sum := by decide
  have hdescent : baseEnd_267401 < baseStart_267401 := by decide
  rcases family_descends (prefixWord ++ tailWord_267401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267415 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 4]
def baseStart_267415 : Nat := 118140960795 + 267415 * 2 ^ 59
def prefixEnd_267415 : Nat := 4983230072969 + 3 ^ 40 * 267415 * 2
def baseEnd_267415 : Nat := 61027746320967320570083

theorem tailTrace_267415 : CollatzResearch.WordTrace tailWord_267415 prefixEnd_267415 61027746320967320570083 := by
  unfold tailWord_267415
  simp only [CollatzResearch.WordTrace]
  refine ⟨9753426326208600691067699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6502284217472400460711799 9753426326208600691067699)
  ·
    refine ⟨14630139489312901036601549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9753426326208600691067699 14630139489312901036601549)
    ·
      refine ⟨5486302308492337888725581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14630139489312901036601549 5486302308492337888725581)
      ·
        refine ⟨2057363365684626708272093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5486302308492337888725581 2057363365684626708272093)
        ·
          refine ⟨771511262131735015602035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2057363365684626708272093 771511262131735015602035)
          ·
            refine ⟨1157266893197602523403053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771511262131735015602035 1157266893197602523403053)
            ·
              refine ⟨433975084949100946276145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1157266893197602523403053 433975084949100946276145)
              ·
                refine ⟨325481313711825709707109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433975084949100946276145 325481313711825709707109)
                ·
                  refine ⟨61027746320967320570083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 325481313711825709707109 61027746320967320570083)
                  ·
                    rfl

theorem cell21_267415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 4].length) (baseStart_267415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267415 prefixEnd_267415 := by exact prefixLift 267415
  have htrace : WordTrace (prefixWord ++ tailWord_267415) baseStart_267415 baseEnd_267415 := by
    simpa [prefixWord, tailWord_267415, baseEnd_267415] using wordTrace_append hprefix tailTrace_267415
  have hstable : (prefixWord ++ tailWord_267415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267415).length < 2 ^ (prefixWord ++ tailWord_267415).sum := by decide
  have hdescent : baseEnd_267415 < baseStart_267415 := by decide
  rcases family_descends (prefixWord ++ tailWord_267415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267443 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 5]
def baseStart_267443 : Nat := 118140960795 + 267443 * 2 ^ 59
def prefixEnd_267443 : Nat := 4983230072969 + 3 ^ 40 * 267443 * 2
def baseEnd_267443 : Nat := 61034136302445494103359

theorem tailTrace_267443 : CollatzResearch.WordTrace tailWord_267443 prefixEnd_267443 61034136302445494103359 := by
  unfold tailWord_267443
  simp only [CollatzResearch.WordTrace]
  refine ⟨9754447570107161473086983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6502965046738107648724655 9754447570107161473086983)
  ·
    refine ⟨14631671355160742209630475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9754447570107161473086983 14631671355160742209630475)
    ·
      refine ⟨21947507032741113314445713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14631671355160742209630475 21947507032741113314445713)
      ·
        refine ⟨16460630274555834985834285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21947507032741113314445713 16460630274555834985834285)
        ·
          refine ⟨6172736352958438119687857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16460630274555834985834285 6172736352958438119687857)
          ·
            refine ⟨4629552264718828589765893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6172736352958438119687857 4629552264718828589765893)
            ·
              refine ⟨868041049634780360581105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4629552264718828589765893 868041049634780360581105)
              ·
                refine ⟨651030787226085270435829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 868041049634780360581105 651030787226085270435829)
                ·
                  refine ⟨61034136302445494103359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 651030787226085270435829 61034136302445494103359)
                  ·
                    rfl

theorem cell21_267443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_267443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267443 prefixEnd_267443 := by exact prefixLift 267443
  have htrace : WordTrace (prefixWord ++ tailWord_267443) baseStart_267443 baseEnd_267443 := by
    simpa [prefixWord, tailWord_267443, baseEnd_267443] using wordTrace_append hprefix tailTrace_267443
  have hstable : (prefixWord ++ tailWord_267443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267443).length < 2 ^ (prefixWord ++ tailWord_267443).sum := by decide
  have hdescent : baseEnd_267443 < baseStart_267443 := by decide
  rcases family_descends (prefixWord ++ tailWord_267443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267474 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_267474 : Nat := 118140960795 + 267474 * 2 ^ 59
def prefixEnd_267474 : Nat := 4983230072969 + 3 ^ 40 * 267474 * 2
def baseEnd_267474 : Nat := 61041210924796329086629

theorem tailTrace_267474 : CollatzResearch.WordTrace tailWord_267474 prefixEnd_267474 61041210924796329086629 := by
  unfold tailWord_267474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438894558248713441866369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6503718821996569178310317 2438894558248713441866369)
  ·
    refine ⟨1829170918686535081399777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2438894558248713441866369 1829170918686535081399777)
    ·
      refine ⟨1371878189014901311049833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1829170918686535081399777 1371878189014901311049833)
      ·
        refine ⟨1028908641761175983287375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1371878189014901311049833 1028908641761175983287375)
        ·
          refine ⟨1543362962641763974931063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028908641761175983287375 1543362962641763974931063)
          ·
            refine ⟨2315044443962645962396595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1543362962641763974931063 2315044443962645962396595)
            ·
              refine ⟨3472566665943968943594893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2315044443962645962396595 3472566665943968943594893)
              ·
                refine ⟨1302212499728988353848085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3472566665943968943594893 1302212499728988353848085)
                ·
                  refine ⟨61041210924796329086629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1302212499728988353848085 61041210924796329086629)
                  ·
                    rfl

theorem cell21_267474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_267474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267474 prefixEnd_267474 := by exact prefixLift 267474
  have htrace : WordTrace (prefixWord ++ tailWord_267474) baseStart_267474 baseEnd_267474 := by
    simpa [prefixWord, tailWord_267474, baseEnd_267474] using wordTrace_append hprefix tailTrace_267474
  have hstable : (prefixWord ++ tailWord_267474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267474).length < 2 ^ (prefixWord ++ tailWord_267474).sum := by decide
  have hdescent : baseEnd_267474 < baseStart_267474 := by decide
  rcases family_descends (prefixWord ++ tailWord_267474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267477 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 5]
def baseStart_267477 : Nat := 118140960795 + 267477 * 2 ^ 59
def prefixEnd_267477 : Nat := 4983230072969 + 3 ^ 40 * 267477 * 2
def baseEnd_267477 : Nat := 61041895565668990536623

theorem tailTrace_267477 : CollatzResearch.WordTrace tailWord_267477 prefixEnd_267477 61041895565668990536623 := by
  unfold tailWord_267477
  simp only [CollatzResearch.WordTrace]
  refine ⟨9755687651983985279824685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6503791767989323519883123 9755687651983985279824685)
  ·
    refine ⟨3658382869493994479934257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9755687651983985279824685 3658382869493994479934257)
    ·
      refine ⟨2743787152120495859950693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3658382869493994479934257 2743787152120495859950693)
      ·
        refine ⟨514460091022592973740755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2743787152120495859950693 514460091022592973740755)
        ·
          refine ⟨771690136533889460611133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514460091022592973740755 771690136533889460611133)
          ·
            refine ⟨289383801200208547729175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 771690136533889460611133 289383801200208547729175)
            ·
              refine ⟨434075701800312821593763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289383801200208547729175 434075701800312821593763)
              ·
                refine ⟨651113552700469232390645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 434075701800312821593763 651113552700469232390645)
                ·
                  refine ⟨61041895565668990536623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 651113552700469232390645 61041895565668990536623)
                  ·
                    rfl

theorem cell21_267477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_267477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267477 prefixEnd_267477 := by exact prefixLift 267477
  have htrace : WordTrace (prefixWord ++ tailWord_267477) baseStart_267477 baseEnd_267477 := by
    simpa [prefixWord, tailWord_267477, baseEnd_267477] using wordTrace_append hprefix tailTrace_267477
  have hstable : (prefixWord ++ tailWord_267477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267477).length < 2 ^ (prefixWord ++ tailWord_267477).sum := by decide
  have hdescent : baseEnd_267477 < baseStart_267477 := by decide
  rcases family_descends (prefixWord ++ tailWord_267477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267488 : List Nat := [2, 1, 1, 3, 1, 4, 1, 8]
def baseStart_267488 : Nat := 118140960795 + 267488 * 2 ^ 59
def prefixEnd_267488 : Nat := 4983230072969 + 3 ^ 40 * 267488 * 2
def baseEnd_267488 : Nat := 20348135305178471951089

theorem tailTrace_267488 : CollatzResearch.WordTrace tailWord_267488 prefixEnd_267488 20348135305178471951089 := by
  unfold tailWord_267488
  simp only [CollatzResearch.WordTrace]
  refine ⟨4878044427472067079237559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6504059236629422772316745 4878044427472067079237559)
  ·
    refine ⟨7317066641208100618856339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4878044427472067079237559 7317066641208100618856339)
    ·
      refine ⟨10975599961812150928284509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7317066641208100618856339 10975599961812150928284509)
      ·
        refine ⟨4115849985679556598106691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10975599961812150928284509 4115849985679556598106691)
        ·
          refine ⟨6173774978519334897160037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4115849985679556598106691 6173774978519334897160037)
          ·
            refine ⟨1157582808472375293217507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6173774978519334897160037 1157582808472375293217507)
            ·
              refine ⟨1736374212708562939826261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1157582808472375293217507 1736374212708562939826261)
              ·
                refine ⟨20348135305178471951089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1736374212708562939826261 20348135305178471951089)
                ·
                  rfl

theorem cell21_267488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_267488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267488 prefixEnd_267488 := by exact prefixLift 267488
  have htrace : WordTrace (prefixWord ++ tailWord_267488) baseStart_267488 baseEnd_267488 := by
    simpa [prefixWord, tailWord_267488, baseEnd_267488] using wordTrace_append hprefix tailTrace_267488
  have hstable : (prefixWord ++ tailWord_267488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267488).length < 2 ^ (prefixWord ++ tailWord_267488).sum := by decide
  have hdescent : baseEnd_267488 < baseStart_267488 := by decide
  rcases family_descends (prefixWord ++ tailWord_267488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267522 : List Nat := [3, 4, 1, 1, 4, 8]
def baseStart_267522 : Nat := 118140960795 + 267522 * 2 ^ 59
def prefixEnd_267522 : Nat := 4983230072969 + 3 ^ 40 * 267522 * 2
def baseEnd_267522 : Nat := 2261191302916996751353

theorem tailTrace_267522 : CollatzResearch.WordTrace tailWord_267522 prefixEnd_267522 2261191302916996751353 := by
  unfold tailWord_267522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2439332234205239491303205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6504885957880638643475213 2439332234205239491303205)
  ·
    refine ⟨457374793913482404619351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2439332234205239491303205 457374793913482404619351)
    ·
      refine ⟨686062190870223606929027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457374793913482404619351 686062190870223606929027)
      ·
        refine ⟨1029093286305335410393541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686062190870223606929027 1029093286305335410393541)
        ·
          refine ⟨192954991182250389448789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1029093286305335410393541 192954991182250389448789)
          ·
            refine ⟨2261191302916996751353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 192954991182250389448789 2261191302916996751353)
            ·
              rfl

theorem cell21_267522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 8].length) (baseStart_267522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267522 prefixEnd_267522 := by exact prefixLift 267522
  have htrace : WordTrace (prefixWord ++ tailWord_267522) baseStart_267522 baseEnd_267522 := by
    simpa [prefixWord, tailWord_267522, baseEnd_267522] using wordTrace_append hprefix tailTrace_267522
  have hstable : (prefixWord ++ tailWord_267522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267522).length < 2 ^ (prefixWord ++ tailWord_267522).sum := by decide
  have hdescent : baseEnd_267522 < baseStart_267522 := by decide
  rcases family_descends (prefixWord ++ tailWord_267522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267629 : List Nat := [1, 5, 1, 1, 1, 3, 3, 3, 3]
def baseStart_267629 : Nat := 118140960795 + 267629 * 2 ^ 59
def prefixEnd_267629 : Nat := 4983230072969 + 3 ^ 40 * 267629 * 2
def baseEnd_267629 : Nat := 61076584036550504002979

theorem tailTrace_267629 : CollatzResearch.WordTrace tailWord_267629 prefixEnd_267629 61076584036550504002979 := by
  unfold tailWord_267629
  simp only [CollatzResearch.WordTrace]
  refine ⟨9761231547433315239357941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6507487698288876826238627 9761231547433315239357941)
  ·
    refine ⟨915115457571873303689807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9761231547433315239357941 915115457571873303689807)
    ·
      refine ⟨1372673186357809955534711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 915115457571873303689807 1372673186357809955534711)
      ·
        refine ⟨2059009779536714933302067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372673186357809955534711 2059009779536714933302067)
        ·
          refine ⟨3088514669305072399953101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2059009779536714933302067 3088514669305072399953101)
          ·
            refine ⟨1158193000989402149982413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3088514669305072399953101 1158193000989402149982413)
            ·
              refine ⟨434322375371025806243405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1158193000989402149982413 434322375371025806243405)
              ·
                refine ⟨162870890764134677341277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434322375371025806243405 162870890764134677341277)
                ·
                  refine ⟨61076584036550504002979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162870890764134677341277 61076584036550504002979)
                  ·
                    rfl

theorem cell21_267629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_267629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267629 prefixEnd_267629 := by exact prefixLift 267629
  have htrace : WordTrace (prefixWord ++ tailWord_267629) baseStart_267629 baseEnd_267629 := by
    simpa [prefixWord, tailWord_267629, baseEnd_267629] using wordTrace_append hprefix tailTrace_267629
  have hstable : (prefixWord ++ tailWord_267629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267629).length < 2 ^ (prefixWord ++ tailWord_267629).sum := by decide
  have hdescent : baseEnd_267629 < baseStart_267629 := by decide
  rcases family_descends (prefixWord ++ tailWord_267629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267657 : List Nat := [1, 2, 1, 1, 7, 1, 2, 6]
def baseStart_267657 : Nat := 118140960795 + 267657 * 2 ^ 59
def prefixEnd_267657 : Nat := 4983230072969 + 3 ^ 40 * 267657 * 2
def baseEnd_267657 : Nat := 20360991339342892512085

theorem tailTrace_267657 : CollatzResearch.WordTrace tailWord_267657 prefixEnd_267657 20360991339342892512085 := by
  unfold tailWord_267657
  simp only [CollatzResearch.WordTrace]
  refine ⟨9762252791331876021377225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6508168527554584014251483 9762252791331876021377225)
  ·
    refine ⟨7321689593498907016032919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9762252791331876021377225 7321689593498907016032919)
    ·
      refine ⟨10982534390248360524049379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7321689593498907016032919 10982534390248360524049379)
      ·
        refine ⟨16473801585372540786074069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10982534390248360524049379 16473801585372540786074069)
        ·
          refine ⟨386104724657168924673611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 16473801585372540786074069 386104724657168924673611)
          ·
            refine ⟨579157086985753387010417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386104724657168924673611 579157086985753387010417)
            ·
              refine ⟨434367815239315040257813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 579157086985753387010417 434367815239315040257813)
              ·
                refine ⟨20360991339342892512085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 434367815239315040257813 20360991339342892512085)
                ·
                  rfl

theorem cell21_267657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 6].length) (baseStart_267657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267657 prefixEnd_267657 := by exact prefixLift 267657
  have htrace : WordTrace (prefixWord ++ tailWord_267657) baseStart_267657 baseEnd_267657 := by
    simpa [prefixWord, tailWord_267657, baseEnd_267657] using wordTrace_append hprefix tailTrace_267657
  have hstable : (prefixWord ++ tailWord_267657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267657).length < 2 ^ (prefixWord ++ tailWord_267657).sum := by decide
  have hdescent : baseEnd_267657 < baseStart_267657 := by decide
  rcases family_descends (prefixWord ++ tailWord_267657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267685 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 6]
def baseStart_267685 : Nat := 118140960795 + 267685 * 2 ^ 59
def prefixEnd_267685 : Nat := 4983230072969 + 3 ^ 40 * 267685 * 2
def baseEnd_267685 : Nat := 61089363999506851069531

theorem tailTrace_267685 : CollatzResearch.WordTrace tailWord_267685 prefixEnd_267685 61089363999506851069531 := by
  unfold tailWord_267685
  simp only [CollatzResearch.WordTrace]
  refine ⟨9763274035230436803396509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6508849356820291202264339 9763274035230436803396509)
  ·
    refine ⟨3661227763211413801273691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9763274035230436803396509 3661227763211413801273691)
    ·
      refine ⟨5491841644817120701910537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3661227763211413801273691 5491841644817120701910537)
      ·
        refine ⟨4118881233612840526432903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5491841644817120701910537 4118881233612840526432903)
        ·
          refine ⟨6178321850419260789649355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4118881233612840526432903 6178321850419260789649355)
          ·
            refine ⟨9267482775628891184474033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6178321850419260789649355 9267482775628891184474033)
            ·
              refine ⟨6950612081721668388355525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9267482775628891184474033 6950612081721668388355525)
              ·
                refine ⟨1303239765322812822816661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6950612081721668388355525 1303239765322812822816661)
                ·
                  refine ⟨61089363999506851069531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1303239765322812822816661 61089363999506851069531)
                  ·
                    rfl

theorem cell21_267685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_267685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267685 prefixEnd_267685 := by exact prefixLift 267685
  have htrace : WordTrace (prefixWord ++ tailWord_267685) baseStart_267685 baseEnd_267685 := by
    simpa [prefixWord, tailWord_267685, baseEnd_267685] using wordTrace_append hprefix tailTrace_267685
  have hstable : (prefixWord ++ tailWord_267685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267685).length < 2 ^ (prefixWord ++ tailWord_267685).sum := by decide
  have hdescent : baseEnd_267685 < baseStart_267685 := by decide
  rcases family_descends (prefixWord ++ tailWord_267685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267705 : List Nat := [1, 2, 1, 4, 4, 1, 1, 4, 3]
def baseStart_267705 : Nat := 118140960795 + 267705 * 2 ^ 59
def prefixEnd_267705 : Nat := 4983230072969 + 3 ^ 40 * 267705 * 2
def baseEnd_267705 : Nat := 61093928271991260736157

theorem tailTrace_267705 : CollatzResearch.WordTrace tailWord_267705 prefixEnd_267705 61093928271991260736157 := by
  unfold tailWord_267705
  simp only [CollatzResearch.WordTrace]
  refine ⟨9764003495157980219124569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6509335663438653479416379 9764003495157980219124569)
  ·
    refine ⟨7323002621368485164343427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9764003495157980219124569 7323002621368485164343427)
    ·
      refine ⟨10984503932052727746515141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7323002621368485164343427 10984503932052727746515141)
      ·
        refine ⟨2059594487259886452471589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10984503932052727746515141 2059594487259886452471589)
        ·
          refine ⟨386173966361228709838423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2059594487259886452471589 386173966361228709838423)
          ·
            refine ⟨579260949541843064757635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386173966361228709838423 579260949541843064757635)
            ·
              refine ⟨868891424312764597136453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 579260949541843064757635 868891424312764597136453)
              ·
                refine ⟨162917142058643361963085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 868891424312764597136453 162917142058643361963085)
                ·
                  refine ⟨61093928271991260736157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 162917142058643361963085 61093928271991260736157)
                  ·
                    rfl

theorem cell21_267705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 3].length) (baseStart_267705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267705 prefixEnd_267705 := by exact prefixLift 267705
  have htrace : WordTrace (prefixWord ++ tailWord_267705) baseStart_267705 baseEnd_267705 := by
    simpa [prefixWord, tailWord_267705, baseEnd_267705] using wordTrace_append hprefix tailTrace_267705
  have hstable : (prefixWord ++ tailWord_267705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267705).length < 2 ^ (prefixWord ++ tailWord_267705).sum := by decide
  have hdescent : baseEnd_267705 < baseStart_267705 := by decide
  rcases family_descends (prefixWord ++ tailWord_267705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267733 : List Nat := [1, 3, 2, 3, 1, 1, 5, 5]
def baseStart_267733 : Nat := 118140960795 + 267733 * 2 ^ 59
def prefixEnd_267733 : Nat := 4983230072969 + 3 ^ 40 * 267733 * 2
def baseEnd_267733 : Nat := 20366772751156478089811

theorem tailTrace_267733 : CollatzResearch.WordTrace tailWord_267733 prefixEnd_267733 20366772751156478089811 := by
  unfold tailWord_267733
  simp only [CollatzResearch.WordTrace]
  refine ⟨9765024739056541001143853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6510016492704360667429235 9765024739056541001143853)
  ·
    refine ⟨3661884277146202875428945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9765024739056541001143853 3661884277146202875428945)
    ·
      refine ⟨2746413207859652156571709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3661884277146202875428945 2746413207859652156571709)
      ·
        refine ⟨1029904952947369558714391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2746413207859652156571709 1029904952947369558714391)
        ·
          refine ⟨1544857429421054338071587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1029904952947369558714391 1544857429421054338071587)
          ·
            refine ⟨2317286144131581507107381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1544857429421054338071587 2317286144131581507107381)
            ·
              refine ⟨217245576012335766291317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2317286144131581507107381 217245576012335766291317)
              ·
                refine ⟨20366772751156478089811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217245576012335766291317 20366772751156478089811)
                ·
                  rfl

theorem cell21_267733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 5].length) (baseStart_267733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267733 prefixEnd_267733 := by exact prefixLift 267733
  have htrace : WordTrace (prefixWord ++ tailWord_267733) baseStart_267733 baseEnd_267733 := by
    simpa [prefixWord, tailWord_267733, baseEnd_267733] using wordTrace_append hprefix tailTrace_267733
  have hstable : (prefixWord ++ tailWord_267733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267733).length < 2 ^ (prefixWord ++ tailWord_267733).sum := by decide
  have hdescent : baseEnd_267733 < baseStart_267733 := by decide
  rcases family_descends (prefixWord ++ tailWord_267733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267868 : List Nat := [2, 2, 4, 1, 2, 10]
def baseStart_267868 : Nat := 118140960795 + 267868 * 2 ^ 59
def prefixEnd_267868 : Nat := 4983230072969 + 3 ^ 40 * 267868 * 2
def baseEnd_267868 : Nat := 2264115818249599982191

theorem tailTrace_267868 : CollatzResearch.WordTrace tailWord_267868 prefixEnd_267868 2264115818249599982191 := by
  unfold tailWord_267868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4884974296783729528654129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6513299062378306038205505 4884974296783729528654129)
  ·
    refine ⟨3663730722587797146490597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4884974296783729528654129 3663730722587797146490597)
    ·
      refine ⟨686949510485211964966987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3663730722587797146490597 686949510485211964966987)
      ·
        refine ⟨1030424265727817947450481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 686949510485211964966987 1030424265727817947450481)
        ·
          refine ⟨772818199295863460587861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1030424265727817947450481 772818199295863460587861)
          ·
            refine ⟨2264115818249599982191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 772818199295863460587861 2264115818249599982191)
            ·
              rfl

theorem cell21_267868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 10].length) (baseStart_267868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267868 prefixEnd_267868 := by exact prefixLift 267868
  have htrace : WordTrace (prefixWord ++ tailWord_267868) baseStart_267868 baseEnd_267868 := by
    simpa [prefixWord, tailWord_267868, baseEnd_267868] using wordTrace_append hprefix tailTrace_267868
  have hstable : (prefixWord ++ tailWord_267868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267868).length < 2 ^ (prefixWord ++ tailWord_267868).sum := by decide
  have hdescent : baseEnd_267868 < baseStart_267868 := by decide
  rcases family_descends (prefixWord ++ tailWord_267868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267916 : List Nat := [2, 2, 1, 2, 1, 1, 6, 3, 3]
def baseStart_267916 : Nat := 118140960795 + 267916 * 2 ^ 59
def prefixEnd_267916 : Nat := 4983230072969 + 3 ^ 40 * 267916 * 2
def baseEnd_267916 : Nat := 61142081346701782719059

theorem tailTrace_267916 : CollatzResearch.WordTrace tailWord_267916 prefixEnd_267916 61142081346701782719059 := by
  unfold tailWord_267916
  simp only [CollatzResearch.WordTrace]
  refine ⟨4885849648696781627527801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6514466198262375503370401 4885849648696781627527801)
  ·
    refine ⟨3664387236522586220645851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4885849648696781627527801 3664387236522586220645851)
    ·
      refine ⟨5496580854783879330968777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3664387236522586220645851 5496580854783879330968777)
      ·
        refine ⟨4122435641087909498226583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5496580854783879330968777 4122435641087909498226583)
        ·
          refine ⟨6183653461631864247339875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4122435641087909498226583 6183653461631864247339875)
          ·
            refine ⟨9275480192447796371009813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6183653461631864247339875 9275480192447796371009813)
            ·
              refine ⟨434788134020990454891085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9275480192447796371009813 434788134020990454891085)
              ·
                refine ⟨163045550257871420584157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 434788134020990454891085 163045550257871420584157)
                ·
                  refine ⟨61142081346701782719059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163045550257871420584157 61142081346701782719059)
                  ·
                    rfl

theorem cell21_267916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_267916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_267916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_267916 prefixEnd_267916 := by exact prefixLift 267916
  have htrace : WordTrace (prefixWord ++ tailWord_267916) baseStart_267916 baseEnd_267916 := by
    simpa [prefixWord, tailWord_267916, baseEnd_267916] using wordTrace_append hprefix tailTrace_267916
  have hstable : (prefixWord ++ tailWord_267916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267916).length < 2 ^ (prefixWord ++ tailWord_267916).sum := by decide
  have hdescent : baseEnd_267916 < baseStart_267916 := by decide
  rcases family_descends (prefixWord ++ tailWord_267916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268085 : List Nat := [1, 3, 3, 1, 4, 1, 2, 3, 3]
def baseStart_268085 : Nat := 118140960795 + 268085 * 2 ^ 59
def prefixEnd_268085 : Nat := 4983230072969 + 3 ^ 40 * 268085 * 2
def baseEnd_268085 : Nat := 61180649449195044402047

theorem tailTrace_268085 : CollatzResearch.WordTrace tailWord_268085 prefixEnd_268085 61180649449195044402047 := by
  unfold tailWord_268085
  simp only [CollatzResearch.WordTrace]
  refine ⟨9777863233781305117957709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6518575489187536745305139 9777863233781305117957709)
  ·
    refine ⟨3666698712667989419234141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9777863233781305117957709 3666698712667989419234141)
    ·
      refine ⟨1375012017250496032212803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3666698712667989419234141 1375012017250496032212803)
      ·
        refine ⟨2062518025875744048319205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375012017250496032212803 2062518025875744048319205)
        ·
          refine ⟨386722129851702009059851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2062518025875744048319205 386722129851702009059851)
          ·
            refine ⟨580083194777553013589777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386722129851702009059851 580083194777553013589777)
            ·
              refine ⟨435062396083164760192333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580083194777553013589777 435062396083164760192333)
              ·
                refine ⟨163148398531186785072125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435062396083164760192333 163148398531186785072125)
                ·
                  refine ⟨61180649449195044402047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163148398531186785072125 61180649449195044402047)
                  ·
                    rfl

theorem cell21_268085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_268085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268085 prefixEnd_268085 := by exact prefixLift 268085
  have htrace : WordTrace (prefixWord ++ tailWord_268085) baseStart_268085 baseEnd_268085 := by
    simpa [prefixWord, tailWord_268085, baseEnd_268085] using wordTrace_append hprefix tailTrace_268085
  have hstable : (prefixWord ++ tailWord_268085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268085).length < 2 ^ (prefixWord ++ tailWord_268085).sum := by decide
  have hdescent : baseEnd_268085 < baseStart_268085 := by decide
  rcases family_descends (prefixWord ++ tailWord_268085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268102 : List Nat := [6, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_268102 : Nat := 118140960795 + 268102 * 2 ^ 59
def prefixEnd_268102 : Nat := 4983230072969 + 3 ^ 40 * 268102 * 2
def baseEnd_268102 : Nat := 61184529080806792618679

theorem tailTrace_268102 : CollatzResearch.WordTrace tailWord_268102 prefixEnd_268102 61184529080806792618679 := by
  unfold tailWord_268102
  simp only [CollatzResearch.WordTrace]
  refine ⟨305577602334991156916455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6518988849813144680884373 305577602334991156916455)
  ·
    refine ⟨458366403502486735374683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305577602334991156916455 458366403502486735374683)
    ·
      refine ⟨687549605253730103062025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 458366403502486735374683 687549605253730103062025)
      ·
        refine ⟨515662203940297577296519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687549605253730103062025 515662203940297577296519)
        ·
          refine ⟨773493305910446365944779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515662203940297577296519 773493305910446365944779)
          ·
            refine ⟨1160239958865669548917169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773493305910446365944779 1160239958865669548917169)
            ·
              refine ⟨870179969149252161687877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1160239958865669548917169 870179969149252161687877)
              ·
                refine ⟨163158744215484780316477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 870179969149252161687877 163158744215484780316477)
                ·
                  refine ⟨61184529080806792618679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163158744215484780316477 61184529080806792618679)
                  ·
                    rfl

theorem cell21_268102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_268102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268102 prefixEnd_268102 := by exact prefixLift 268102
  have htrace : WordTrace (prefixWord ++ tailWord_268102) baseStart_268102 baseEnd_268102 := by
    simpa [prefixWord, tailWord_268102, baseEnd_268102] using wordTrace_append hprefix tailTrace_268102
  have hstable : (prefixWord ++ tailWord_268102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268102).length < 2 ^ (prefixWord ++ tailWord_268102).sum := by decide
  have hdescent : baseEnd_268102 < baseStart_268102 := by decide
  rcases family_descends (prefixWord ++ tailWord_268102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268130 : List Nat := [3, 3, 2, 1, 2, 3, 2, 5]
def baseStart_268130 : Nat := 118140960795 + 268130 * 2 ^ 59
def prefixEnd_268130 : Nat := 4983230072969 + 3 ^ 40 * 268130 * 2
def baseEnd_268130 : Nat := 20396973020761655383985

theorem tailTrace_268130 : CollatzResearch.WordTrace tailWord_268130 prefixEnd_268130 20396973020761655383985 := by
  unfold tailWord_268130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2444876129654569450836461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6519669679078851868897229 2444876129654569450836461)
  ·
    refine ⟨916828548620463544063673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2444876129654569450836461 916828548620463544063673)
    ·
      refine ⟨687621411465347658047755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 916828548620463544063673 687621411465347658047755)
      ·
        refine ⟨1031432117198021487071633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 687621411465347658047755 1031432117198021487071633)
        ·
          refine ⟨773574087898516115303725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1031432117198021487071633 773574087898516115303725)
          ·
            refine ⟨290090282961943543238897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 773574087898516115303725 290090282961943543238897)
            ·
              refine ⟨217567712221457657429173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290090282961943543238897 217567712221457657429173)
              ·
                refine ⟨20396973020761655383985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217567712221457657429173 20396973020761655383985)
                ·
                  rfl

theorem cell21_268130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_268130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268130 prefixEnd_268130 := by exact prefixLift 268130
  have htrace : WordTrace (prefixWord ++ tailWord_268130) baseStart_268130 baseEnd_268130 := by
    simpa [prefixWord, tailWord_268130, baseEnd_268130] using wordTrace_append hprefix tailTrace_268130
  have hstable : (prefixWord ++ tailWord_268130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268130).length < 2 ^ (prefixWord ++ tailWord_268130).sum := by decide
  have hdescent : baseEnd_268130 < baseStart_268130 := by decide
  rcases family_descends (prefixWord ++ tailWord_268130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268141 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 6]
def baseStart_268141 : Nat := 118140960795 + 268141 * 2 ^ 59
def prefixEnd_268141 : Nat := 4983230072969 + 3 ^ 40 * 268141 * 2
def baseEnd_268141 : Nat := 61193429412151391468599

theorem tailTrace_268141 : CollatzResearch.WordTrace tailWord_268141 prefixEnd_268141 61193429412151391468599 := by
  unfold tailWord_268141
  simp only [CollatzResearch.WordTrace]
  refine ⟨9779905721578426681996277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6519937147718951121330851 9779905721578426681996277)
  ·
    refine ⟨916866161397977501437151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9779905721578426681996277 916866161397977501437151)
    ·
      refine ⟨1375299242096966252155727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 916866161397977501437151 1375299242096966252155727)
      ·
        refine ⟨2062948863145449378233591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1375299242096966252155727 2062948863145449378233591)
        ·
          refine ⟨3094423294718174067350387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2062948863145449378233591 3094423294718174067350387)
          ·
            refine ⟨4641634942077261101025581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3094423294718174067350387 4641634942077261101025581)
            ·
              refine ⟨1740613103278972912884593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4641634942077261101025581 1740613103278972912884593)
              ·
                refine ⟨1305459827459229684663445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1740613103278972912884593 1305459827459229684663445)
                ·
                  refine ⟨61193429412151391468599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1305459827459229684663445 61193429412151391468599)
                  ·
                    rfl

theorem cell21_268141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_268141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268141 prefixEnd_268141 := by exact prefixLift 268141
  have htrace : WordTrace (prefixWord ++ tailWord_268141) baseStart_268141 baseEnd_268141 := by
    simpa [prefixWord, tailWord_268141, baseEnd_268141] using wordTrace_append hprefix tailTrace_268141
  have hstable : (prefixWord ++ tailWord_268141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268141).length < 2 ^ (prefixWord ++ tailWord_268141).sum := by decide
  have hdescent : baseEnd_268141 < baseStart_268141 := by decide
  rcases family_descends (prefixWord ++ tailWord_268141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268161 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 5]
def baseStart_268161 : Nat := 118140960795 + 268161 * 2 ^ 59
def prefixEnd_268161 : Nat := 4983230072969 + 3 ^ 40 * 268161 * 2
def baseEnd_268161 : Nat := 61197993684635801135225

theorem tailTrace_268161 : CollatzResearch.WordTrace tailWord_268161 prefixEnd_268161 61197993684635801135225 := by
  unfold tailWord_268161
  simp only [CollatzResearch.WordTrace]
  refine ⟨9780635181505970097724337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6520423454337313398482891 9780635181505970097724337)
  ·
    refine ⟨7335476386129477573293253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9780635181505970097724337 7335476386129477573293253)
    ·
      refine ⟨1375401822399277044992485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7335476386129477573293253 1375401822399277044992485)
      ·
        refine ⟨257887841699864445936091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1375401822399277044992485 257887841699864445936091)
        ·
          refine ⟨386831762549796668904137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257887841699864445936091 386831762549796668904137)
          ·
            refine ⟨290123821912347501678103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386831762549796668904137 290123821912347501678103)
            ·
              refine ⟨435185732868521252517155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290123821912347501678103 435185732868521252517155)
              ·
                refine ⟨652778599302781878775733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435185732868521252517155 652778599302781878775733)
                ·
                  refine ⟨61197993684635801135225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 652778599302781878775733 61197993684635801135225)
                  ·
                    rfl

theorem cell21_268161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 5].length) (baseStart_268161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268161 prefixEnd_268161 := by exact prefixLift 268161
  have htrace : WordTrace (prefixWord ++ tailWord_268161) baseStart_268161 baseEnd_268161 := by
    simpa [prefixWord, tailWord_268161, baseEnd_268161] using wordTrace_append hprefix tailTrace_268161
  have hstable : (prefixWord ++ tailWord_268161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268161).length < 2 ^ (prefixWord ++ tailWord_268161).sum := by decide
  have hdescent : baseEnd_268161 < baseStart_268161 := by decide
  rcases family_descends (prefixWord ++ tailWord_268161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268206 : List Nat := [4, 1, 5, 1, 1, 9]
def baseStart_268206 : Nat := 118140960795 + 268206 * 2 ^ 59
def prefixEnd_268206 : Nat := 4983230072969 + 3 ^ 40 * 268206 * 2
def baseEnd_268206 : Nat := 2266972714730582329079

theorem tailTrace_268206 : CollatzResearch.WordTrace tailWord_268206 prefixEnd_268206 2266972714730582329079 := by
  unfold tailWord_268206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1222784558292867847889059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6521517644228628522074981 1222784558292867847889059)
  ·
    refine ⟨1834176837439301771833589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1222784558292867847889059 1834176837439301771833589)
    ·
      refine ⟨171954078509934541109399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1834176837439301771833589 171954078509934541109399)
      ·
        refine ⟨257931117764901811664099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171954078509934541109399 257931117764901811664099)
        ·
          refine ⟨386896676647352717496149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257931117764901811664099 386896676647352717496149)
          ·
            refine ⟨2266972714730582329079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 386896676647352717496149 2266972714730582329079)
            ·
              rfl

theorem cell21_268206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 9].length) (baseStart_268206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268206 prefixEnd_268206 := by exact prefixLift 268206
  have htrace : WordTrace (prefixWord ++ tailWord_268206) baseStart_268206 baseEnd_268206 := by
    simpa [prefixWord, tailWord_268206, baseEnd_268206] using wordTrace_append hprefix tailTrace_268206
  have hstable : (prefixWord ++ tailWord_268206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268206).length < 2 ^ (prefixWord ++ tailWord_268206).sum := by decide
  have hdescent : baseEnd_268206 < baseStart_268206 := by decide
  rcases family_descends (prefixWord ++ tailWord_268206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268212 : List Nat := [2, 5, 2, 1, 3, 1, 2, 2, 3]
def baseStart_268212 : Nat := 118140960795 + 268212 * 2 ^ 59
def prefixEnd_268212 : Nat := 4983230072969 + 3 ^ 40 * 268212 * 2
def baseEnd_268212 : Nat := 61209632579471045785121

theorem tailTrace_268212 : CollatzResearch.WordTrace tailWord_268212 prefixEnd_268212 61209632579471045785121 := by
  unfold tailWord_268212
  simp only [CollatzResearch.WordTrace]
  refine ⟨4891247652160602903915445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6521663536214137205220593 4891247652160602903915445)
  ·
    refine ⟨458554467390056522242073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4891247652160602903915445 458554467390056522242073)
    ·
      refine ⟨343915850542542391681555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458554467390056522242073 343915850542542391681555)
      ·
        refine ⟨515873775813813587522333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343915850542542391681555 515873775813813587522333)
        ·
          refine ⟨193452665930180095320875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 515873775813813587522333 193452665930180095320875)
          ·
            refine ⟨290178998895270142981313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193452665930180095320875 290178998895270142981313)
            ·
              refine ⟨217634249171452607235985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290178998895270142981313 217634249171452607235985)
              ·
                refine ⟨163225686878589455426989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217634249171452607235985 163225686878589455426989)
                ·
                  refine ⟨61209632579471045785121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163225686878589455426989 61209632579471045785121)
                  ·
                    rfl

theorem cell21_268212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_268212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268212 prefixEnd_268212 := by exact prefixLift 268212
  have htrace : WordTrace (prefixWord ++ tailWord_268212) baseStart_268212 baseEnd_268212 := by
    simpa [prefixWord, tailWord_268212, baseEnd_268212] using wordTrace_append hprefix tailTrace_268212
  have hstable : (prefixWord ++ tailWord_268212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268212).length < 2 ^ (prefixWord ++ tailWord_268212).sum := by decide
  have hdescent : baseEnd_268212 < baseStart_268212 := by decide
  rcases family_descends (prefixWord ++ tailWord_268212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268248 : List Nat := [2, 1, 2, 2, 2, 2, 5, 5]
def baseStart_268248 : Nat := 118140960795 + 268248 * 2 ^ 59
def prefixEnd_268248 : Nat := 4983230072969 + 3 ^ 40 * 268248 * 2
def baseEnd_268248 : Nat := 20405949423314327728349

theorem tailTrace_268248 : CollatzResearch.WordTrace tailWord_268248 prefixEnd_268248 20405949423314327728349 := by
  unfold tailWord_268248
  simp only [CollatzResearch.WordTrace]
  refine ⟨4891904166095391978070699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6522538888127189304094265 4891904166095391978070699)
  ·
    refine ⟨7337856249143087967106049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4891904166095391978070699 7337856249143087967106049)
    ·
      refine ⟨5503392186857315975329537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7337856249143087967106049 5503392186857315975329537)
      ·
        refine ⟨4127544140142986981497153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5503392186857315975329537 4127544140142986981497153)
        ·
          refine ⟨3095658105107240236122865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4127544140142986981497153 3095658105107240236122865)
          ·
            refine ⟨2321743578830430177092149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3095658105107240236122865 2321743578830430177092149)
            ·
              refine ⟨217663460515352829102389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2321743578830430177092149 217663460515352829102389)
              ·
                refine ⟨20405949423314327728349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217663460515352829102389 20405949423314327728349)
                ·
                  rfl

theorem cell21_268248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_268248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268248 prefixEnd_268248 := by exact prefixLift 268248
  have htrace : WordTrace (prefixWord ++ tailWord_268248) baseStart_268248 baseEnd_268248 := by
    simpa [prefixWord, tailWord_268248, baseEnd_268248] using wordTrace_append hprefix tailTrace_268248
  have hstable : (prefixWord ++ tailWord_268248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268248).length < 2 ^ (prefixWord ++ tailWord_268248).sum := by decide
  have hdescent : baseEnd_268248 < baseStart_268248 := by decide
  rcases family_descends (prefixWord ++ tailWord_268248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268344 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 4]
def baseStart_268344 : Nat := 118140960795 + 268344 * 2 ^ 59
def prefixEnd_268344 : Nat := 4983230072969 + 3 ^ 40 * 268344 * 2
def baseEnd_268344 : Nat := 61239756777868149584851

theorem tailTrace_268344 : CollatzResearch.WordTrace tailWord_268344 prefixEnd_268344 61239756777868149584851 := by
  unfold tailWord_268344
  simp only [CollatzResearch.WordTrace]
  refine ⟨4893654869921496175818043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6524873159895328234424057 4893654869921496175818043)
  ·
    refine ⟨7340482304882244263727065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4893654869921496175818043 7340482304882244263727065)
    ·
      refine ⟨5505361728661683197795299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7340482304882244263727065 5505361728661683197795299)
      ·
        refine ⟨8258042592992524796692949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5505361728661683197795299 8258042592992524796692949)
        ·
          refine ⟨193547873273262299922491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 8258042592992524796692949 193547873273262299922491)
          ·
            refine ⟨290321809909893449883737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193547873273262299922491 290321809909893449883737)
            ·
              refine ⟨217741357432420087412803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290321809909893449883737 217741357432420087412803)
              ·
                refine ⟨326612036148630131119205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217741357432420087412803 326612036148630131119205)
                ·
                  refine ⟨61239756777868149584851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 326612036148630131119205 61239756777868149584851)
                  ·
                    rfl

theorem cell21_268344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 4].length) (baseStart_268344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268344 prefixEnd_268344 := by exact prefixLift 268344
  have htrace : WordTrace (prefixWord ++ tailWord_268344) baseStart_268344 baseEnd_268344 := by
    simpa [prefixWord, tailWord_268344, baseEnd_268344] using wordTrace_append hprefix tailTrace_268344
  have hstable : (prefixWord ++ tailWord_268344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268344).length < 2 ^ (prefixWord ++ tailWord_268344).sum := by decide
  have hdescent : baseEnd_268344 < baseStart_268344 := by decide
  rcases family_descends (prefixWord ++ tailWord_268344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268389 : List Nat := [1, 3, 1, 3, 2, 4, 2, 2, 3]
def baseStart_268389 : Nat := 118140960795 + 268389 * 2 ^ 59
def prefixEnd_268389 : Nat := 4983230072969 + 3 ^ 40 * 268389 * 2
def baseEnd_268389 : Nat := 61250026390958071334759

theorem tailTrace_268389 : CollatzResearch.WordTrace tailWord_268389 prefixEnd_268389 61250026390958071334759 := by
  unfold tailWord_268389
  simp only [CollatzResearch.WordTrace]
  refine ⟨9788951024679965037024221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6525967349786643358016147 9788951024679965037024221)
  ·
    refine ⟨3670856634254986888884083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9788951024679965037024221 3670856634254986888884083)
    ·
      refine ⟨5506284951382480333326125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3670856634254986888884083 5506284951382480333326125)
      ·
        refine ⟨2064856856768430124997297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5506284951382480333326125 2064856856768430124997297)
        ·
          refine ⟨1548642642576322593747973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2064856856768430124997297 1548642642576322593747973)
          ·
            refine ⟨290370495483060486327745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1548642642576322593747973 290370495483060486327745)
            ·
              refine ⟨217777871612295364745809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290370495483060486327745 217777871612295364745809)
              ·
                refine ⟨163333403709221523559357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217777871612295364745809 163333403709221523559357)
                ·
                  refine ⟨61250026390958071334759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163333403709221523559357 61250026390958071334759)
                  ·
                    rfl

theorem cell21_268389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 3].length) (baseStart_268389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268389 prefixEnd_268389 := by exact prefixLift 268389
  have htrace : WordTrace (prefixWord ++ tailWord_268389) baseStart_268389 baseEnd_268389 := by
    simpa [prefixWord, tailWord_268389, baseEnd_268389] using wordTrace_append hprefix tailTrace_268389
  have hstable : (prefixWord ++ tailWord_268389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268389).length < 2 ^ (prefixWord ++ tailWord_268389).sum := by decide
  have hdescent : baseEnd_268389 < baseStart_268389 := by decide
  rcases family_descends (prefixWord ++ tailWord_268389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268400 : List Nat := [2, 1, 1, 1, 5, 4, 1, 6]
def baseStart_268400 : Nat := 118140960795 + 268400 * 2 ^ 59
def prefixEnd_268400 : Nat := 4983230072969 + 3 ^ 40 * 268400 * 2
def baseEnd_268400 : Nat := 20417512246941498883801

theorem tailTrace_268400 : CollatzResearch.WordTrace tailWord_268400 prefixEnd_268400 20417512246941498883801 := by
  unfold tailWord_268400
  simp only [CollatzResearch.WordTrace]
  refine ⟨4894676113820056957837327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6526234818426742610449769 4894676113820056957837327)
  ·
    refine ⟨7342014170730085436755991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4894676113820056957837327 7342014170730085436755991)
    ·
      refine ⟨11013021256095128155133987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7342014170730085436755991 11013021256095128155133987)
      ·
        refine ⟨16519531884142692232700981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11013021256095128155133987 16519531884142692232700981)
        ·
          refine ⟨1548706114138377396815717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16519531884142692232700981 1548706114138377396815717)
          ·
            refine ⟨290382396400945761902947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1548706114138377396815717 290382396400945761902947)
            ·
              refine ⟨435573594601418642854421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290382396400945761902947 435573594601418642854421)
              ·
                refine ⟨20417512246941498883801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 435573594601418642854421 20417512246941498883801)
                ·
                  rfl

theorem cell21_268400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_268400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268400 prefixEnd_268400 := by exact prefixLift 268400
  have htrace : WordTrace (prefixWord ++ tailWord_268400) baseStart_268400 baseEnd_268400 := by
    simpa [prefixWord, tailWord_268400, baseEnd_268400] using wordTrace_append hprefix tailTrace_268400
  have hstable : (prefixWord ++ tailWord_268400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268400).length < 2 ^ (prefixWord ++ tailWord_268400).sum := by decide
  have hdescent : baseEnd_268400 < baseStart_268400 := by decide
  rcases family_descends (prefixWord ++ tailWord_268400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268417 : List Nat := [1, 2, 4, 2, 3, 1, 3, 5]
def baseStart_268417 : Nat := 118140960795 + 268417 * 2 ^ 59
def prefixEnd_268417 : Nat := 4983230072969 + 3 ^ 40 * 268417 * 2
def baseEnd_268417 : Nat := 20418805457478748289345

theorem tailTrace_268417 : CollatzResearch.WordTrace tailWord_268417 prefixEnd_268417 20418805457478748289345 := by
  unfold tailWord_268417
  simp only [CollatzResearch.WordTrace]
  refine ⟨9789972268578525819043505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6526648179052350546029003 9789972268578525819043505)
  ·
    refine ⟨7342479201433894364282629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9789972268578525819043505 7342479201433894364282629)
    ·
      refine ⟨1376714850268855193302993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7342479201433894364282629 1376714850268855193302993)
      ·
        refine ⟨1032536137701641394977245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1376714850268855193302993 1032536137701641394977245)
        ·
          refine ⟨387201051638115523116467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1032536137701641394977245 387201051638115523116467)
          ·
            refine ⟨580801577457173284674701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387201051638115523116467 580801577457173284674701)
            ·
              refine ⟨217800591546439981753013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580801577457173284674701 217800591546439981753013)
              ·
                refine ⟨20418805457478748289345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217800591546439981753013 20418805457478748289345)
                ·
                  rfl

theorem cell21_268417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 5].length) (baseStart_268417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268417 prefixEnd_268417 := by exact prefixLift 268417
  have htrace : WordTrace (prefixWord ++ tailWord_268417) baseStart_268417 baseEnd_268417 := by
    simpa [prefixWord, tailWord_268417, baseEnd_268417] using wordTrace_append hprefix tailTrace_268417
  have hstable : (prefixWord ++ tailWord_268417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268417).length < 2 ^ (prefixWord ++ tailWord_268417).sum := by decide
  have hdescent : baseEnd_268417 < baseStart_268417 := by decide
  rcases family_descends (prefixWord ++ tailWord_268417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268445 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 6]
def baseStart_268445 : Nat := 118140960795 + 268445 * 2 ^ 59
def prefixEnd_268445 : Nat := 4983230072969 + 3 ^ 40 * 268445 * 2
def baseEnd_268445 : Nat := 61262806353914418401311

theorem tailTrace_268445 : CollatzResearch.WordTrace tailWord_268445 prefixEnd_268445 61262806353914418401311 := by
  unfold tailWord_268445
  simp only [CollatzResearch.WordTrace]
  refine ⟨9790993512477086601062789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6527329008318057734041859 9790993512477086601062789)
  ·
    refine ⟨1835811283589453737699273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9790993512477086601062789 1835811283589453737699273)
    ·
      refine ⟨1376858462692090303274455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1835811283589453737699273 1376858462692090303274455)
      ·
        refine ⟨2065287694038135454911683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1376858462692090303274455 2065287694038135454911683)
        ·
          refine ⟨3097931541057203182367525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2065287694038135454911683 3097931541057203182367525)
          ·
            refine ⟨580862163948225596693911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3097931541057203182367525 580862163948225596693911)
            ·
              refine ⟨871293245922338395040867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580862163948225596693911 871293245922338395040867)
              ·
                refine ⟨1306939868883507592561301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 871293245922338395040867 1306939868883507592561301)
                ·
                  refine ⟨61262806353914418401311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1306939868883507592561301 61262806353914418401311)
                  ·
                    rfl

theorem cell21_268445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_268445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268445 prefixEnd_268445 := by exact prefixLift 268445
  have htrace : WordTrace (prefixWord ++ tailWord_268445) baseStart_268445 baseEnd_268445 := by
    simpa [prefixWord, tailWord_268445, baseEnd_268445] using wordTrace_append hprefix tailTrace_268445
  have hstable : (prefixWord ++ tailWord_268445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268445).length < 2 ^ (prefixWord ++ tailWord_268445).sum := by decide
  have hdescent : baseEnd_268445 < baseStart_268445 := by decide
  rcases family_descends (prefixWord ++ tailWord_268445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268468 : List Nat := [2, 5, 3, 1, 1, 2, 2, 5]
def baseStart_268468 : Nat := 118140960795 + 268468 * 2 ^ 59
def prefixEnd_268468 : Nat := 4983230072969 + 3 ^ 40 * 268468 * 2
def baseEnd_268468 : Nat := 20422685089090496505977

theorem tailTrace_268468 : CollatzResearch.WordTrace tailWord_268468 prefixEnd_268468 20422685089090496505977 := by
  unfold tailWord_268468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4895916195696880764575029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6527888260929174352766705 4895916195696880764575029)
  ·
    refine ⟨458992143346582571678909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4895916195696880764575029 458992143346582571678909)
    ·
      refine ⟨172122053754968464379591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 458992143346582571678909 172122053754968464379591)
      ·
        refine ⟨258183080632452696569387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172122053754968464379591 258183080632452696569387)
        ·
          refine ⟨387274620948679044854081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258183080632452696569387 387274620948679044854081)
          ·
            refine ⟨290455965711509283640561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387274620948679044854081 290455965711509283640561)
            ·
              refine ⟨217841974283631962730421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290455965711509283640561 217841974283631962730421)
              ·
                refine ⟨20422685089090496505977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 217841974283631962730421 20422685089090496505977)
                ·
                  rfl

theorem cell21_268468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 5].length) (baseStart_268468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268468 prefixEnd_268468 := by exact prefixLift 268468
  have htrace : WordTrace (prefixWord ++ tailWord_268468) baseStart_268468 baseEnd_268468 := by
    simpa [prefixWord, tailWord_268468, baseEnd_268468] using wordTrace_append hprefix tailTrace_268468
  have hstable : (prefixWord ++ tailWord_268468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268468).length < 2 ^ (prefixWord ++ tailWord_268468).sum := by decide
  have hdescent : baseEnd_268468 < baseStart_268468 := by decide
  rcases family_descends (prefixWord ++ tailWord_268468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268476 : List Nat := [2, 2, 2, 3, 3, 1, 1, 7]
def baseStart_268476 : Nat := 118140960795 + 268476 * 2 ^ 59
def prefixEnd_268476 : Nat := 4983230072969 + 3 ^ 40 * 268476 * 2
def baseEnd_268476 : Nat := 20423293658755084461527

theorem tailTrace_268476 : CollatzResearch.WordTrace tailWord_268476 prefixEnd_268476 20423293658755084461527 := by
  unfold tailWord_268476
  simp only [CollatzResearch.WordTrace]
  refine ⟨4896062087682389447720641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6528082783576519263627521 4896062087682389447720641)
  ·
    refine ⟨3672046565761792085790481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4896062087682389447720641 3672046565761792085790481)
    ·
      refine ⟨2754034924321344064342861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3672046565761792085790481 2754034924321344064342861)
      ·
        refine ⟨1032763096620504024128573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2754034924321344064342861 1032763096620504024128573)
        ·
          refine ⟨387286161232689009048215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1032763096620504024128573 387286161232689009048215)
          ·
            refine ⟨580929241849033513572323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387286161232689009048215 580929241849033513572323)
            ·
              refine ⟨871393862773550270358485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580929241849033513572323 871393862773550270358485)
              ·
                refine ⟨20423293658755084461527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 871393862773550270358485 20423293658755084461527)
                ·
                  rfl

theorem cell21_268476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_268476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268476 prefixEnd_268476 := by exact prefixLift 268476
  have htrace : WordTrace (prefixWord ++ tailWord_268476) baseStart_268476 baseEnd_268476 := by
    simpa [prefixWord, tailWord_268476, baseEnd_268476] using wordTrace_append hprefix tailTrace_268476
  have hstable : (prefixWord ++ tailWord_268476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268476).length < 2 ^ (prefixWord ++ tailWord_268476).sum := by decide
  have hdescent : baseEnd_268476 < baseStart_268476 := by decide
  rcases family_descends (prefixWord ++ tailWord_268476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268482 : List Nat := [3, 5, 1, 1, 1, 1, 3, 3, 3]
def baseStart_268482 : Nat := 118140960795 + 268482 * 2 ^ 59
def prefixEnd_268482 : Nat := 4983230072969 + 3 ^ 40 * 268482 * 2
def baseEnd_268482 : Nat := 61271250258010576284569

theorem tailTrace_268482 : CollatzResearch.WordTrace tailWord_268482 prefixEnd_268482 61271250258010576284569 := by
  unfold tailWord_268482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2448085753335760480039925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6528228675562027946773133 2448085753335760480039925)
  ·
    refine ⟨229508039375227545003743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2448085753335760480039925 229508039375227545003743)
    ·
      refine ⟨344262059062841317505615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229508039375227545003743 344262059062841317505615)
      ·
        refine ⟨516393088594261976258423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344262059062841317505615 516393088594261976258423)
        ·
          refine ⟨774589632891392964387635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516393088594261976258423 774589632891392964387635)
          ·
            refine ⟨1161884449337089446581453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774589632891392964387635 1161884449337089446581453)
            ·
              refine ⟨435706668501408542468045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1161884449337089446581453 435706668501408542468045)
              ·
                refine ⟨163390000688028203425517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435706668501408542468045 163390000688028203425517)
                ·
                  refine ⟨61271250258010576284569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163390000688028203425517 61271250258010576284569)
                  ·
                    rfl

theorem cell21_268482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_268482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268482 prefixEnd_268482 := by exact prefixLift 268482
  have htrace : WordTrace (prefixWord ++ tailWord_268482) baseStart_268482 baseEnd_268482 := by
    simpa [prefixWord, tailWord_268482, baseEnd_268482] using wordTrace_append hprefix tailTrace_268482
  have hstable : (prefixWord ++ tailWord_268482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268482).length < 2 ^ (prefixWord ++ tailWord_268482).sum := by decide
  have hdescent : baseEnd_268482 < baseStart_268482 := by decide
  rcases family_descends (prefixWord ++ tailWord_268482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268549 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 9]
def baseStart_268549 : Nat := 118140960795 + 268549 * 2 ^ 59
def prefixEnd_268549 : Nat := 4983230072969 + 3 ^ 40 * 268549 * 2
def baseEnd_268549 : Nat := 61286540570833348667765

theorem tailTrace_268549 : CollatzResearch.WordTrace tailWord_268549 prefixEnd_268549 61286540570833348667765 := by
  unfold tailWord_268549
  simp only [CollatzResearch.WordTrace]
  refine ⟨9794786704100312362848701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6529857802733541575232467 9794786704100312362848701)
  ·
    refine ⟨3673045014037617136068263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9794786704100312362848701 3673045014037617136068263)
    ·
      refine ⟨5509567521056425704102395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3673045014037617136068263 5509567521056425704102395)
      ·
        refine ⟨8264351281584638556153593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5509567521056425704102395 8264351281584638556153593)
        ·
          refine ⟨6198263461188478917115195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8264351281584638556153593 6198263461188478917115195)
          ·
            refine ⟨9297395191782718375672793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6198263461188478917115195 9297395191782718375672793)
            ·
              refine ⟨6973046393837038781754595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9297395191782718375672793 6973046393837038781754595)
              ·
                refine ⟨10459569590755558172631893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6973046393837038781754595 10459569590755558172631893)
                ·
                  refine ⟨61286540570833348667765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10459569590755558172631893 61286540570833348667765)
                  ·
                    rfl

theorem cell21_268549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_268549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268549 prefixEnd_268549 := by exact prefixLift 268549
  have htrace : WordTrace (prefixWord ++ tailWord_268549) baseStart_268549 baseEnd_268549 := by
    simpa [prefixWord, tailWord_268549, baseEnd_268549] using wordTrace_append hprefix tailTrace_268549
  have hstable : (prefixWord ++ tailWord_268549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268549).length < 2 ^ (prefixWord ++ tailWord_268549).sum := by decide
  have hdescent : baseEnd_268549 < baseStart_268549 := by decide
  rcases family_descends (prefixWord ++ tailWord_268549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268656 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_268656 : Nat := 118140960795 + 268656 * 2 ^ 59
def prefixEnd_268656 : Nat := 4983230072969 + 3 ^ 40 * 268656 * 2
def baseEnd_268656 : Nat := 61310959428624940384213

theorem tailTrace_268656 : CollatzResearch.WordTrace tailWord_268656 prefixEnd_268656 61310959428624940384213 := by
  unfold tailWord_268656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4899344657356334818496911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6532459543141779757995881 4899344657356334818496911)
  ·
    refine ⟨7349016986034502227745367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4899344657356334818496911 7349016986034502227745367)
    ·
      refine ⟨11023525479051753341618051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7349016986034502227745367 11023525479051753341618051)
      ·
        refine ⟨16535288218577630012427077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11023525479051753341618051 16535288218577630012427077)
        ·
          refine ⟨3100366540983305627330077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16535288218577630012427077 3100366540983305627330077)
          ·
            refine ⟨1162637452868739610248779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3100366540983305627330077 1162637452868739610248779)
            ·
              refine ⟨1743956179303109415373169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1162637452868739610248779 1743956179303109415373169)
              ·
                refine ⟨1307967134477332061529877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1743956179303109415373169 1307967134477332061529877)
                ·
                  refine ⟨61310959428624940384213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1307967134477332061529877 61310959428624940384213)
                  ·
                    rfl

theorem cell21_268656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_268656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268656 prefixEnd_268656 := by exact prefixLift 268656
  have htrace : WordTrace (prefixWord ++ tailWord_268656) baseStart_268656 baseEnd_268656 := by
    simpa [prefixWord, tailWord_268656, baseEnd_268656] using wordTrace_append hprefix tailTrace_268656
  have hstable : (prefixWord ++ tailWord_268656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268656).length < 2 ^ (prefixWord ++ tailWord_268656).sum := by decide
  have hdescent : baseEnd_268656 < baseStart_268656 := by decide
  rcases family_descends (prefixWord ++ tailWord_268656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268662 : List Nat := [5, 1, 1, 4, 2, 1, 7]
def baseStart_268662 : Nat := 118140960795 + 268662 * 2 ^ 59
def prefixEnd_268662 : Nat := 4983230072969 + 3 ^ 40 * 268662 * 2
def baseEnd_268662 : Nat := 6812480967818918142689

theorem tailTrace_268662 : CollatzResearch.WordTrace tailWord_268662 prefixEnd_268662 6812480967818918142689 := by
  unfold tailWord_268662
  simp only [CollatzResearch.WordTrace]
  refine ⟨612431759543183291357015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6532605435127288441141493 612431759543183291357015)
  ·
    refine ⟨918647639314774937035523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 612431759543183291357015 918647639314774937035523)
    ·
      refine ⟨1377971458972162405553285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 918647639314774937035523 1377971458972162405553285)
      ·
        refine ⟨258369648557280451041241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1377971458972162405553285 258369648557280451041241)
        ·
          refine ⟨193777236417960338280931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258369648557280451041241 193777236417960338280931)
          ·
            refine ⟨290665854626940507421397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193777236417960338280931 290665854626940507421397)
            ·
              refine ⟨6812480967818918142689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 290665854626940507421397 6812480967818918142689)
              ·
                rfl

theorem cell21_268662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 7].length) (baseStart_268662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268662 prefixEnd_268662 := by exact prefixLift 268662
  have htrace : WordTrace (prefixWord ++ tailWord_268662) baseStart_268662 baseEnd_268662 := by
    simpa [prefixWord, tailWord_268662, baseEnd_268662] using wordTrace_append hprefix tailTrace_268662
  have hstable : (prefixWord ++ tailWord_268662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268662).length < 2 ^ (prefixWord ++ tailWord_268662).sum := by decide
  have hdescent : baseEnd_268662 < baseStart_268662 := by decide
  rcases family_descends (prefixWord ++ tailWord_268662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268673 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 6]
def baseStart_268673 : Nat := 118140960795 + 268673 * 2 ^ 59
def prefixEnd_268673 : Nat := 4983230072969 + 3 ^ 40 * 268673 * 2
def baseEnd_268673 : Nat := 61314839060236688600845

theorem tailTrace_268673 : CollatzResearch.WordTrace tailWord_268673 prefixEnd_268673 61314839060236688600845 := by
  unfold tailWord_268673
  simp only [CollatzResearch.WordTrace]
  refine ⟨9799309355651081540362673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6532872903767387693575115 9799309355651081540362673)
  ·
    refine ⟨7349482016738311155272005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9799309355651081540362673 7349482016738311155272005)
    ·
      refine ⟨1378027878138433341613501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7349482016738311155272005 1378027878138433341613501)
      ·
        refine ⟨516760454301912503105063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1378027878138433341613501 516760454301912503105063)
        ·
          refine ⟨775140681452868754657595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516760454301912503105063 775140681452868754657595)
          ·
            refine ⟨1162711022179303131986393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 775140681452868754657595 1162711022179303131986393)
            ·
              refine ⟨872033266634477348989795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1162711022179303131986393 872033266634477348989795)
              ·
                refine ⟨1308049899951716023484693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 872033266634477348989795 1308049899951716023484693)
                ·
                  refine ⟨61314839060236688600845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1308049899951716023484693 61314839060236688600845)
                  ·
                    rfl

theorem cell21_268673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_268673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268673 prefixEnd_268673 := by exact prefixLift 268673
  have htrace : WordTrace (prefixWord ++ tailWord_268673) baseStart_268673 baseEnd_268673 := by
    simpa [prefixWord, tailWord_268673, baseEnd_268673] using wordTrace_append hprefix tailTrace_268673
  have hstable : (prefixWord ++ tailWord_268673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268673).length < 2 ^ (prefixWord ++ tailWord_268673).sum := by decide
  have hdescent : baseEnd_268673 < baseStart_268673 := by decide
  rcases family_descends (prefixWord ++ tailWord_268673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268676 : List Nat := [2, 3, 2, 1, 1, 2, 5, 2, 3]
def baseStart_268676 : Nat := 118140960795 + 268676 * 2 ^ 59
def prefixEnd_268676 : Nat := 4983230072969 + 3 ^ 40 * 268676 * 2
def baseEnd_268676 : Nat := 61315523701109350050839

theorem tailTrace_268676 : CollatzResearch.WordTrace tailWord_268676 prefixEnd_268676 61315523701109350050839 := by
  unfold tailWord_268676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4899709387320106526360941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6532945849760142035147921 4899709387320106526360941)
  ·
    refine ⟨1837391020245039947385353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4899709387320106526360941 1837391020245039947385353)
    ·
      refine ⟨1378043265183779960539015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1837391020245039947385353 1378043265183779960539015)
      ·
        refine ⟨2067064897775669940808523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1378043265183779960539015 2067064897775669940808523)
        ·
          refine ⟨3100597346663504911212785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2067064897775669940808523 3100597346663504911212785)
          ·
            refine ⟨2325448009997628683409589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3100597346663504911212785 2325448009997628683409589)
            ·
              refine ⟨218010750937277689069649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2325448009997628683409589 218010750937277689069649)
              ·
                refine ⟨163508063202958266802237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218010750937277689069649 163508063202958266802237)
                ·
                  refine ⟨61315523701109350050839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163508063202958266802237 61315523701109350050839)
                  ·
                    rfl

theorem cell21_268676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_268676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268676 prefixEnd_268676 := by exact prefixLift 268676
  have htrace : WordTrace (prefixWord ++ tailWord_268676) baseStart_268676 baseEnd_268676 := by
    simpa [prefixWord, tailWord_268676, baseEnd_268676] using wordTrace_append hprefix tailTrace_268676
  have hstable : (prefixWord ++ tailWord_268676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268676).length < 2 ^ (prefixWord ++ tailWord_268676).sum := by decide
  have hdescent : baseEnd_268676 < baseStart_268676 := by decide
  rcases family_descends (prefixWord ++ tailWord_268676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268724 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 4]
def baseStart_268724 : Nat := 118140960795 + 268724 * 2 ^ 59
def prefixEnd_268724 : Nat := 4983230072969 + 3 ^ 40 * 268724 * 2
def baseEnd_268724 : Nat := 61326477955071933250741

theorem tailTrace_268724 : CollatzResearch.WordTrace tailWord_268724 prefixEnd_268724 61326477955071933250741 := by
  unfold tailWord_268724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4900584739233158625234613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6534112985644211500312817 4900584739233158625234613)
  ·
    refine ⟨459429819303108621115745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4900584739233158625234613 459429819303108621115745)
    ·
      refine ⟨344572364477331465836809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 459429819303108621115745 344572364477331465836809)
      ·
        refine ⟨258429273357998599377607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344572364477331465836809 258429273357998599377607)
        ·
          refine ⟨387643910036997899066411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258429273357998599377607 387643910036997899066411)
          ·
            refine ⟨581465865055496848599617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387643910036997899066411 581465865055496848599617)
            ·
              refine ⟨436099398791622636449713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 581465865055496848599617 436099398791622636449713)
              ·
                refine ⟨327074549093716977337285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436099398791622636449713 327074549093716977337285)
                ·
                  refine ⟨61326477955071933250741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 327074549093716977337285 61326477955071933250741)
                  ·
                    rfl

theorem cell21_268724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_268724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268724 prefixEnd_268724 := by exact prefixLift 268724
  have htrace : WordTrace (prefixWord ++ tailWord_268724) baseStart_268724 baseEnd_268724 := by
    simpa [prefixWord, tailWord_268724, baseEnd_268724] using wordTrace_append hprefix tailTrace_268724
  have hstable : (prefixWord ++ tailWord_268724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268724).length < 2 ^ (prefixWord ++ tailWord_268724).sum := by decide
  have hdescent : baseEnd_268724 < baseStart_268724 := by decide
  rcases family_descends (prefixWord ++ tailWord_268724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268828 : List Nat := [2, 2, 3, 1, 2, 4, 1, 3, 3]
def baseStart_268828 : Nat := 118140960795 + 268828 * 2 ^ 59
def prefixEnd_268828 : Nat := 4983230072969 + 3 ^ 40 * 268828 * 2
def baseEnd_268828 : Nat := 61350212171990863517195

theorem tailTrace_268828 : CollatzResearch.WordTrace tailWord_268828 prefixEnd_268828 61350212171990863517195 := by
  unfold tailWord_268828
  simp only [CollatzResearch.WordTrace]
  refine ⟨4902481335044771506127569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6536641780059695341503425 4902481335044771506127569)
  ·
    refine ⟨3676861001283578629595677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4902481335044771506127569 3676861001283578629595677)
    ·
      refine ⟨1378822875481341986098379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3676861001283578629595677 1378822875481341986098379)
      ·
        refine ⟨2068234313222012979147569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1378822875481341986098379 2068234313222012979147569)
        ·
          refine ⟨1551175734916509734360677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2068234313222012979147569 1551175734916509734360677)
          ·
            refine ⟨290845450296845575192627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1551175734916509734360677 290845450296845575192627)
            ·
              refine ⟨436268175445268362788941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290845450296845575192627 436268175445268362788941)
              ·
                refine ⟨163600565791975636045853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 436268175445268362788941 163600565791975636045853)
                ·
                  refine ⟨61350212171990863517195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163600565791975636045853 61350212171990863517195)
                  ·
                    rfl

theorem cell21_268828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 3].length) (baseStart_268828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268828 prefixEnd_268828 := by exact prefixLift 268828
  have htrace : WordTrace (prefixWord ++ tailWord_268828) baseStart_268828 baseEnd_268828 := by
    simpa [prefixWord, tailWord_268828, baseEnd_268828] using wordTrace_append hprefix tailTrace_268828
  have hstable : (prefixWord ++ tailWord_268828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268828).length < 2 ^ (prefixWord ++ tailWord_268828).sum := by decide
  have hdescent : baseEnd_268828 < baseStart_268828 := by decide
  rcases family_descends (prefixWord ++ tailWord_268828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268904 : List Nat := [2, 1, 4, 3, 2, 1, 1, 4, 3]
def baseStart_268904 : Nat := 118140960795 + 268904 * 2 ^ 59
def prefixEnd_268904 : Nat := 4983230072969 + 3 ^ 40 * 268904 * 2
def baseEnd_268904 : Nat := 61367556407431620250373

theorem tailTrace_268904 : CollatzResearch.WordTrace tailWord_268904 prefixEnd_268904 61367556407431620250373 := by
  unfold tailWord_268904
  simp only [CollatzResearch.WordTrace]
  refine ⟨4903867308907103996010883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6538489745209471994681177 4903867308907103996010883)
  ·
    refine ⟨7355800963360655994016325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4903867308907103996010883 7355800963360655994016325)
    ·
      refine ⟨1379212680630122998878061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7355800963360655994016325 1379212680630122998878061)
      ·
        refine ⟨517204755236296124579273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1379212680630122998878061 517204755236296124579273)
        ·
          refine ⟨387903566427222093434455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 517204755236296124579273 387903566427222093434455)
          ·
            refine ⟨581855349640833140151683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387903566427222093434455 581855349640833140151683)
            ·
              refine ⟨872783024461249710227525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 581855349640833140151683 872783024461249710227525)
              ·
                refine ⟨163646817086484320667661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 872783024461249710227525 163646817086484320667661)
                ·
                  refine ⟨61367556407431620250373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163646817086484320667661 61367556407431620250373)
                  ·
                    rfl

theorem cell21_268904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 3].length) (baseStart_268904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268904 prefixEnd_268904 := by exact prefixLift 268904
  have htrace : WordTrace (prefixWord ++ tailWord_268904) baseStart_268904 baseEnd_268904 := by
    simpa [prefixWord, tailWord_268904, baseEnd_268904] using wordTrace_append hprefix tailTrace_268904
  have hstable : (prefixWord ++ tailWord_268904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268904).length < 2 ^ (prefixWord ++ tailWord_268904).sum := by decide
  have hdescent : baseEnd_268904 < baseStart_268904 := by decide
  rcases family_descends (prefixWord ++ tailWord_268904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268932 : List Nat := [2, 3, 2, 1, 3, 2, 3, 5]
def baseStart_268932 : Nat := 118140960795 + 268932 * 2 ^ 59
def prefixEnd_268932 : Nat := 4983230072969 + 3 ^ 40 * 268932 * 2
def baseEnd_268932 : Nat := 20457982129636597927883

theorem tailTrace_268932 : CollatzResearch.WordTrace tailWord_268932 prefixEnd_268932 20457982129636597927883 := by
  unfold tailWord_268932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4904377930856384387020525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6539170574475179182694033 4904377930856384387020525)
  ·
    refine ⟨1839141724071144145132697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4904377930856384387020525 1839141724071144145132697)
    ·
      refine ⟨1379356293053358108849523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1839141724071144145132697 1379356293053358108849523)
      ·
        refine ⟨2069034439580037163274285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1379356293053358108849523 2069034439580037163274285)
        ·
          refine ⟨775887914842513936227857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2069034439580037163274285 775887914842513936227857)
          ·
            refine ⟨581915936131885452170893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 775887914842513936227857 581915936131885452170893)
            ·
              refine ⟨218218476049457044564085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 581915936131885452170893 218218476049457044564085)
              ·
                refine ⟨20457982129636597927883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 218218476049457044564085 20457982129636597927883)
                ·
                  rfl

theorem cell21_268932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_268932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268932 prefixEnd_268932 := by exact prefixLift 268932
  have htrace : WordTrace (prefixWord ++ tailWord_268932) baseStart_268932 baseEnd_268932 := by
    simpa [prefixWord, tailWord_268932, baseEnd_268932] using wordTrace_append hprefix tailTrace_268932
  have hstable : (prefixWord ++ tailWord_268932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268932).length < 2 ^ (prefixWord ++ tailWord_268932).sum := by decide
  have hdescent : baseEnd_268932 < baseStart_268932 := by decide
  rcases family_descends (prefixWord ++ tailWord_268932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268943 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 8]
def baseStart_268943 : Nat := 118140960795 + 268943 * 2 ^ 59
def prefixEnd_268943 : Nat := 4983230072969 + 3 ^ 40 * 268943 * 2
def baseEnd_268943 : Nat := 61376456738776219100293

theorem tailTrace_268943 : CollatzResearch.WordTrace tailWord_268943 prefixEnd_268943 61376456738776219100293 := by
  unfold tailWord_268943
  simp only [CollatzResearch.WordTrace]
  refine ⟨9809157064672917652691483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6539438043115278435127655 9809157064672917652691483)
  ·
    refine ⟨14713735597009376479037225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9809157064672917652691483 14713735597009376479037225)
    ·
      refine ⟨11035301697757032359277919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14713735597009376479037225 11035301697757032359277919)
      ·
        refine ⟨16552952546635548538916879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11035301697757032359277919 16552952546635548538916879)
        ·
          refine ⟨24829428819953322808375319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16552952546635548538916879 24829428819953322808375319)
          ·
            refine ⟨37244143229929984212562979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24829428819953322808375319 37244143229929984212562979)
            ·
              refine ⟨55866214844894976318844469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37244143229929984212562979 55866214844894976318844469)
              ·
                refine ⟨5237457641708904029891669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55866214844894976318844469 5237457641708904029891669)
                ·
                  refine ⟨61376456738776219100293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5237457641708904029891669 61376456738776219100293)
                  ·
                    rfl

theorem cell21_268943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_268943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268943 prefixEnd_268943 := by exact prefixLift 268943
  have htrace : WordTrace (prefixWord ++ tailWord_268943) baseStart_268943 baseEnd_268943 := by
    simpa [prefixWord, tailWord_268943, baseEnd_268943] using wordTrace_append hprefix tailTrace_268943
  have hstable : (prefixWord ++ tailWord_268943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268943).length < 2 ^ (prefixWord ++ tailWord_268943).sum := by decide
  have hdescent : baseEnd_268943 < baseStart_268943 := by decide
  rcases family_descends (prefixWord ++ tailWord_268943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_268991 : List Nat := [1, 1, 2, 2, 2, 4, 4, 5]
def baseStart_268991 : Nat := 118140960795 + 268991 * 2 ^ 59
def prefixEnd_268991 : Nat := 4983230072969 + 3 ^ 40 * 268991 * 2
def baseEnd_268991 : Nat := 20462470330912934100065

theorem tailTrace_268991 : CollatzResearch.WordTrace tailWord_268991 prefixEnd_268991 20462470330912934100065 := by
  unfold tailWord_268991
  simp only [CollatzResearch.WordTrace]
  refine ⟨9810907768499021850438827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6540605178999347900292551 9810907768499021850438827)
  ·
    refine ⟨14716361652748532775658241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9810907768499021850438827 14716361652748532775658241)
    ·
      refine ⟨11037271239561399581743681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14716361652748532775658241 11037271239561399581743681)
      ·
        refine ⟨8277953429671049686307761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11037271239561399581743681 8277953429671049686307761)
        ·
          refine ⟨6208465072253287264730821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8277953429671049686307761 6208465072253287264730821)
          ·
            refine ⟨1164087201047491362137029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6208465072253287264730821 1164087201047491362137029)
            ·
              refine ⟨218266350196404630400693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1164087201047491362137029 218266350196404630400693)
              ·
                refine ⟨20462470330912934100065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 218266350196404630400693 20462470330912934100065)
                ·
                  rfl

theorem cell21_268991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 5].length) (baseStart_268991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_268991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_268991 prefixEnd_268991 := by exact prefixLift 268991
  have htrace : WordTrace (prefixWord ++ tailWord_268991) baseStart_268991 baseEnd_268991 := by
    simpa [prefixWord, tailWord_268991, baseEnd_268991] using wordTrace_append hprefix tailTrace_268991
  have hstable : (prefixWord ++ tailWord_268991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_268991).length < 2 ^ (prefixWord ++ tailWord_268991).sum := by decide
  have hdescent : baseEnd_268991 < baseStart_268991 := by decide
  rcases family_descends (prefixWord ++ tailWord_268991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269050 : List Nat := [3, 1, 1, 1, 1, 3, 4, 7]
def baseStart_269050 : Nat := 118140960795 + 269050 * 2 ^ 59
def prefixEnd_269050 : Nat := 4983230072969 + 3 ^ 40 * 269050 * 2
def baseEnd_269050 : Nat := 20466958532189270272247

theorem tailTrace_269050 : CollatzResearch.WordTrace tailWord_269050 prefixEnd_269050 20466958532189270272247 := by
  unfold tailWord_269050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2453264918821318731709151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6542039783523516617891069 2453264918821318731709151)
  ·
    refine ⟨3679897378231978097563727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2453264918821318731709151 3679897378231978097563727)
    ·
      refine ⟨5519846067347967146345591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3679897378231978097563727 5519846067347967146345591)
      ·
        refine ⟨8279769101021950719518387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5519846067347967146345591 8279769101021950719518387)
        ·
          refine ⟨12419653651532926079277581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8279769101021950719518387 12419653651532926079277581)
          ·
            refine ⟨4657370119324847279729093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12419653651532926079277581 4657370119324847279729093)
            ·
              refine ⟨873256897373408864949205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4657370119324847279729093 873256897373408864949205)
              ·
                refine ⟨20466958532189270272247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 873256897373408864949205 20466958532189270272247)
                ·
                  rfl

theorem cell21_269050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_269050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269050 prefixEnd_269050 := by exact prefixLift 269050
  have htrace : WordTrace (prefixWord ++ tailWord_269050) baseStart_269050 baseEnd_269050 := by
    simpa [prefixWord, tailWord_269050, baseEnd_269050] using wordTrace_append hprefix tailTrace_269050
  have hstable : (prefixWord ++ tailWord_269050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269050).length < 2 ^ (prefixWord ++ tailWord_269050).sum := by decide
  have hdescent : baseEnd_269050 < baseStart_269050 := by decide
  rcases family_descends (prefixWord ++ tailWord_269050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269129 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 4]
def baseStart_269129 : Nat := 118140960795 + 269129 * 2 ^ 59
def prefixEnd_269129 : Nat := 4983230072969 + 3 ^ 40 * 269129 * 2
def baseEnd_269129 : Nat := 61418904472881228999913

theorem tailTrace_269129 : CollatzResearch.WordTrace tailWord_269129 prefixEnd_269129 61418904472881228999913 := by
  unfold tailWord_269129
  simp only [CollatzResearch.WordTrace]
  refine ⟨9815941041999071418962441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6543960694666047612641627 9815941041999071418962441)
  ·
    refine ⟨7361955781499303564221831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9815941041999071418962441 7361955781499303564221831)
    ·
      refine ⟨11042933672248955346332747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7361955781499303564221831 11042933672248955346332747)
      ·
        refine ⟨16564400508373433019499121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11042933672248955346332747 16564400508373433019499121)
        ·
          refine ⟨12423300381280074764624341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16564400508373433019499121 12423300381280074764624341)
          ·
            refine ⟨291171102686251752295883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 12423300381280074764624341 291171102686251752295883)
            ·
              refine ⟨436756654029377628443825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291171102686251752295883 436756654029377628443825)
              ·
                refine ⟨327567490522033221332869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 436756654029377628443825 327567490522033221332869)
                ·
                  refine ⟨61418904472881228999913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 327567490522033221332869 61418904472881228999913)
                  ·
                    rfl

theorem cell21_269129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_269129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269129 prefixEnd_269129 := by exact prefixLift 269129
  have htrace : WordTrace (prefixWord ++ tailWord_269129) baseStart_269129 baseEnd_269129 := by
    simpa [prefixWord, tailWord_269129, baseEnd_269129] using wordTrace_append hprefix tailTrace_269129
  have hstable : (prefixWord ++ tailWord_269129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269129).length < 2 ^ (prefixWord ++ tailWord_269129).sum := by decide
  have hdescent : baseEnd_269129 < baseStart_269129 := by decide
  rcases family_descends (prefixWord ++ tailWord_269129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269157 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 5]
def baseStart_269157 : Nat := 118140960795 + 269157 * 2 ^ 59
def prefixEnd_269157 : Nat := 4983230072969 + 3 ^ 40 * 269157 * 2
def baseEnd_269157 : Nat := 61425294454359402533189

theorem tailTrace_269157 : CollatzResearch.WordTrace tailWord_269157 prefixEnd_269157 61425294454359402533189 := by
  unfold tailWord_269157
  simp only [CollatzResearch.WordTrace]
  refine ⟨9816962285897632200981725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6544641523931754800654483 9816962285897632200981725)
  ·
    refine ⟨3681360857211612075368147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9816962285897632200981725 3681360857211612075368147)
    ·
      refine ⟨5522041285817418113052221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3681360857211612075368147 5522041285817418113052221)
      ·
        refine ⟨2070765482181531792394583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5522041285817418113052221 2070765482181531792394583)
        ·
          refine ⟨3106148223272297688591875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2070765482181531792394583 3106148223272297688591875)
          ·
            refine ⟨4659222334908446532887813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3106148223272297688591875 4659222334908446532887813)
            ·
              refine ⟨873604187795333724916465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4659222334908446532887813 873604187795333724916465)
              ·
                refine ⟨655203140846500293687349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 873604187795333724916465 655203140846500293687349)
                ·
                  refine ⟨61425294454359402533189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 655203140846500293687349 61425294454359402533189)
                  ·
                    rfl

theorem cell21_269157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 5].length) (baseStart_269157 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269157 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269157 prefixEnd_269157 := by exact prefixLift 269157
  have htrace : WordTrace (prefixWord ++ tailWord_269157) baseStart_269157 baseEnd_269157 := by
    simpa [prefixWord, tailWord_269157, baseEnd_269157] using wordTrace_append hprefix tailTrace_269157
  have hstable : (prefixWord ++ tailWord_269157).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269157).length < 2 ^ (prefixWord ++ tailWord_269157).sum := by decide
  have hdescent : baseEnd_269157 < baseStart_269157 := by decide
  rcases family_descends (prefixWord ++ tailWord_269157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269160 : List Nat := [2, 1, 4, 2, 1, 4, 2, 5]
def baseStart_269160 : Nat := 118140960795 + 269160 * 2 ^ 59
def prefixEnd_269160 : Nat := 4983230072969 + 3 ^ 40 * 269160 * 2
def baseEnd_269160 : Nat := 20475326365077354661061

theorem tailTrace_269160 : CollatzResearch.WordTrace tailWord_269160 prefixEnd_269160 20475326365077354661061 := by
  unfold tailWord_269160
  simp only [CollatzResearch.WordTrace]
  refine ⟨4908535852443381856670467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6544714469924509142227289 4908535852443381856670467)
  ·
    refine ⟨7362803778665072785005701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4908535852443381856670467 7362803778665072785005701)
    ·
      refine ⟨1380525708499701147188569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7362803778665072785005701 1380525708499701147188569)
      ·
        refine ⟨1035394281374775860391427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1380525708499701147188569 1035394281374775860391427)
        ·
          refine ⟨1553091422062163790587141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1035394281374775860391427 1553091422062163790587141)
          ·
            refine ⟨291204641636655710735089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1553091422062163790587141 291204641636655710735089)
            ·
              refine ⟨218403481227491783051317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291204641636655710735089 218403481227491783051317)
              ·
                refine ⟨20475326365077354661061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 218403481227491783051317 20475326365077354661061)
                ·
                  rfl

theorem cell21_269160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 5].length) (baseStart_269160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269160 prefixEnd_269160 := by exact prefixLift 269160
  have htrace : WordTrace (prefixWord ++ tailWord_269160) baseStart_269160 baseEnd_269160 := by
    simpa [prefixWord, tailWord_269160, baseEnd_269160] using wordTrace_append hprefix tailTrace_269160
  have hstable : (prefixWord ++ tailWord_269160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269160).length < 2 ^ (prefixWord ++ tailWord_269160).sum := by decide
  have hdescent : baseEnd_269160 < baseStart_269160 := by decide
  rcases family_descends (prefixWord ++ tailWord_269160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269171 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 6]
def baseStart_269171 : Nat := 118140960795 + 269171 * 2 ^ 59
def prefixEnd_269171 : Nat := 4983230072969 + 3 ^ 40 * 269171 * 2
def baseEnd_269171 : Nat := 61428489445098489299827

theorem tailTrace_269171 : CollatzResearch.WordTrace tailWord_269171 prefixEnd_269171 61428489445098489299827 := by
  unfold tailWord_269171
  simp only [CollatzResearch.WordTrace]
  refine ⟨9817472907846912591991367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6544981938564608394660911 9817472907846912591991367)
  ·
    refine ⟨14726209361770368887987051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9817472907846912591991367 14726209361770368887987051)
    ·
      refine ⟨22089314042655553331980577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14726209361770368887987051 22089314042655553331980577)
      ·
        refine ⟨16566985531991664998985433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22089314042655553331980577 16566985531991664998985433)
        ·
          refine ⟨12425239148993748749239075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16566985531991664998985433 12425239148993748749239075)
          ·
            refine ⟨18637858723490623123858613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12425239148993748749239075 18637858723490623123858613)
            ·
              refine ⟨1747299255327245917861745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18637858723490623123858613 1747299255327245917861745)
              ·
                refine ⟨1310474441495434438396309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1747299255327245917861745 1310474441495434438396309)
                ·
                  refine ⟨61428489445098489299827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1310474441495434438396309 61428489445098489299827)
                  ·
                    rfl

theorem cell21_269171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 6].length) (baseStart_269171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269171 prefixEnd_269171 := by exact prefixLift 269171
  have htrace : WordTrace (prefixWord ++ tailWord_269171) baseStart_269171 baseEnd_269171 := by
    simpa [prefixWord, tailWord_269171, baseEnd_269171] using wordTrace_append hprefix tailTrace_269171
  have hstable : (prefixWord ++ tailWord_269171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269171).length < 2 ^ (prefixWord ++ tailWord_269171).sum := by decide
  have hdescent : baseEnd_269171 < baseStart_269171 := by decide
  rcases family_descends (prefixWord ++ tailWord_269171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269188 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 4]
def baseStart_269188 : Nat := 118140960795 + 269188 * 2 ^ 59
def prefixEnd_269188 : Nat := 4983230072969 + 3 ^ 40 * 269188 * 2
def baseEnd_269188 : Nat := 61432369076710237516459

theorem tailTrace_269188 : CollatzResearch.WordTrace tailWord_269188 prefixEnd_269188 61432369076710237516459 := by
  unfold tailWord_269188
  simp only [CollatzResearch.WordTrace]
  refine ⟨4909046474392662247680109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6545395299190216330240145 4909046474392662247680109)
  ·
    refine ⟨1840892427897248342880041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4909046474392662247680109 1840892427897248342880041)
    ·
      refine ⟨1380669320922936257160031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1840892427897248342880041 1380669320922936257160031)
      ·
        refine ⟨2071003981384404385740047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380669320922936257160031 2071003981384404385740047)
        ·
          refine ⟨3106505972076606578610071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2071003981384404385740047 3106505972076606578610071)
          ·
            refine ⟨4659758958114909867915107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3106505972076606578610071 4659758958114909867915107)
            ·
              refine ⟨6989638437172364801872661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4659758958114909867915107 6989638437172364801872661)
              ·
                refine ⟨327639301742454600087781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6989638437172364801872661 327639301742454600087781)
                ·
                  refine ⟨61432369076710237516459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 327639301742454600087781 61432369076710237516459)
                  ·
                    rfl

theorem cell21_269188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_269188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269188 prefixEnd_269188 := by exact prefixLift 269188
  have htrace : WordTrace (prefixWord ++ tailWord_269188) baseStart_269188 baseEnd_269188 := by
    simpa [prefixWord, tailWord_269188, baseEnd_269188] using wordTrace_append hprefix tailTrace_269188
  have hstable : (prefixWord ++ tailWord_269188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269188).length < 2 ^ (prefixWord ++ tailWord_269188).sum := by decide
  have hdescent : baseEnd_269188 < baseStart_269188 := by decide
  rcases family_descends (prefixWord ++ tailWord_269188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269205 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 4]
def baseStart_269205 : Nat := 118140960795 + 269205 * 2 ^ 59
def prefixEnd_269205 : Nat := 4983230072969 + 3 ^ 40 * 269205 * 2
def baseEnd_269205 : Nat := 61436248708321985733091

theorem tailTrace_269205 : CollatzResearch.WordTrace tailWord_269205 prefixEnd_269205 61436248708321985733091 := by
  unfold tailWord_269205
  simp only [CollatzResearch.WordTrace]
  refine ⟨9818712989723736398729069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6545808659815824265819379 9818712989723736398729069)
  ·
    refine ⟨3682017371146401149523401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9818712989723736398729069 3682017371146401149523401)
    ·
      refine ⟨2761513028359800862142551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3682017371146401149523401 2761513028359800862142551)
      ·
        refine ⟨4142269542539701293213827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2761513028359800862142551 4142269542539701293213827)
        ·
          refine ⟨6213404313809551939820741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4142269542539701293213827 6213404313809551939820741)
          ·
            refine ⟨1165013308839290988716389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6213404313809551939820741 1165013308839290988716389)
            ·
              refine ⟨218439995407367060384323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1165013308839290988716389 218439995407367060384323)
              ·
                refine ⟨327659993111050590576485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218439995407367060384323 327659993111050590576485)
                ·
                  refine ⟨61436248708321985733091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 327659993111050590576485 61436248708321985733091)
                  ·
                    rfl

theorem cell21_269205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_269205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269205 prefixEnd_269205 := by exact prefixLift 269205
  have htrace : WordTrace (prefixWord ++ tailWord_269205) baseStart_269205 baseEnd_269205 := by
    simpa [prefixWord, tailWord_269205, baseEnd_269205] using wordTrace_append hprefix tailTrace_269205
  have hstable : (prefixWord ++ tailWord_269205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269205).length < 2 ^ (prefixWord ++ tailWord_269205).sum := by decide
  have hdescent : baseEnd_269205 < baseStart_269205 := by decide
  rcases family_descends (prefixWord ++ tailWord_269205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269343 : List Nat := [1, 1, 2, 4, 1, 5, 1, 3, 3]
def baseStart_269343 : Nat := 118140960795 + 269343 * 2 ^ 59
def prefixEnd_269343 : Nat := 4983230072969 + 3 ^ 40 * 269343 * 2
def baseEnd_269343 : Nat := 61467742188464412432809

theorem tailTrace_269343 : CollatzResearch.WordTrace tailWord_269343 prefixEnd_269343 61467742188464412432809 := by
  unfold tailWord_269343
  simp only [CollatzResearch.WordTrace]
  refine ⟨9823746263223785967252683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6549164175482523978168455 9823746263223785967252683)
  ·
    refine ⟨14735619394835678950879025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9823746263223785967252683 14735619394835678950879025)
    ·
      refine ⟨11051714546126759213159269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14735619394835678950879025 11051714546126759213159269)
      ·
        refine ⟨2072196477398767352467363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11051714546126759213159269 2072196477398767352467363)
        ·
          refine ⟨3108294716098151028701045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2072196477398767352467363 3108294716098151028701045)
          ·
            refine ⟨291402629634201658940723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3108294716098151028701045 291402629634201658940723)
            ·
              refine ⟨437103944451302488411085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291402629634201658940723 437103944451302488411085)
              ·
                refine ⟨163913979169238433154157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 437103944451302488411085 163913979169238433154157)
                ·
                  refine ⟨61467742188464412432809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163913979169238433154157 61467742188464412432809)
                  ·
                    rfl

theorem cell21_269343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 3].length) (baseStart_269343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269343 prefixEnd_269343 := by exact prefixLift 269343
  have htrace : WordTrace (prefixWord ++ tailWord_269343) baseStart_269343 baseEnd_269343 := by
    simpa [prefixWord, tailWord_269343, baseEnd_269343] using wordTrace_append hprefix tailTrace_269343
  have hstable : (prefixWord ++ tailWord_269343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269343).length < 2 ^ (prefixWord ++ tailWord_269343).sum := by decide
  have hdescent : baseEnd_269343 < baseStart_269343 := by decide
  rcases family_descends (prefixWord ++ tailWord_269343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269374 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_269374 : Nat := 118140960795 + 269374 * 2 ^ 59
def prefixEnd_269374 : Nat := 4983230072969 + 3 ^ 40 * 269374 * 2
def baseEnd_269374 : Nat := 61474816810815247416079

theorem tailTrace_269374 : CollatzResearch.WordTrace tailWord_269374 prefixEnd_269374 61474816810815247416079 := by
  unfold tailWord_269374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1228109615763934782703897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6549917950740985507754117 1228109615763934782703897)
  ·
    refine ⟨921082211822951087027923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1228109615763934782703897 921082211822951087027923)
    ·
      refine ⟨1381623317734426630541885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 921082211822951087027923 1381623317734426630541885)
      ·
        refine ⟨518108744150409986453207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1381623317734426630541885 518108744150409986453207)
        ·
          refine ⟨777163116225614979679811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518108744150409986453207 777163116225614979679811)
          ·
            refine ⟨1165744674338422469519717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 777163116225614979679811 1165744674338422469519717)
            ·
              refine ⟨218577126438454213034947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1165744674338422469519717 218577126438454213034947)
              ·
                refine ⟨327865689657681319552421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218577126438454213034947 327865689657681319552421)
                ·
                  refine ⟨61474816810815247416079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 327865689657681319552421 61474816810815247416079)
                  ·
                    rfl

theorem cell21_269374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_269374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269374 prefixEnd_269374 := by exact prefixLift 269374
  have htrace : WordTrace (prefixWord ++ tailWord_269374) baseStart_269374 baseEnd_269374 := by
    simpa [prefixWord, tailWord_269374, baseEnd_269374] using wordTrace_append hprefix tailTrace_269374
  have hstable : (prefixWord ++ tailWord_269374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269374).length < 2 ^ (prefixWord ++ tailWord_269374).sum := by decide
  have hdescent : baseEnd_269374 < baseStart_269374 := by decide
  rcases family_descends (prefixWord ++ tailWord_269374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269537 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 5]
def baseStart_269537 : Nat := 118140960795 + 269537 * 2 ^ 59
def prefixEnd_269537 : Nat := 4983230072969 + 3 ^ 40 * 269537 * 2
def baseEnd_269537 : Nat := 61512015631563186199079

theorem tailTrace_269537 : CollatzResearch.WordTrace tailWord_269537 prefixEnd_269537 61512015631563186199079 := by
  unfold tailWord_269537
  simp only [CollatzResearch.WordTrace]
  refine ⟨9830822024520957099814865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6553881349680638066543243 9830822024520957099814865)
  ·
    refine ⟨7373116518390717824861149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9830822024520957099814865 7373116518390717824861149)
    ·
      refine ⟨2764918694396519184322931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7373116518390717824861149 2764918694396519184322931)
      ·
        refine ⟨4147378041594778776484397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2764918694396519184322931 4147378041594778776484397)
        ·
          refine ⟨1555266765598042041181649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4147378041594778776484397 1555266765598042041181649)
          ·
            refine ⟨1166450074198531530886237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1555266765598042041181649 1166450074198531530886237)
            ·
              refine ⟨437418777824449324082339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1166450074198531530886237 437418777824449324082339)
              ·
                refine ⟨656128166736673986123509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437418777824449324082339 656128166736673986123509)
                ·
                  refine ⟨61512015631563186199079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 656128166736673986123509 61512015631563186199079)
                  ·
                    rfl

theorem cell21_269537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 5].length) (baseStart_269537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269537 prefixEnd_269537 := by exact prefixLift 269537
  have htrace : WordTrace (prefixWord ++ tailWord_269537) baseStart_269537 baseEnd_269537 := by
    simpa [prefixWord, tailWord_269537, baseEnd_269537] using wordTrace_append hprefix tailTrace_269537
  have hstable : (prefixWord ++ tailWord_269537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269537).length < 2 ^ (prefixWord ++ tailWord_269537).sum := by decide
  have hdescent : baseEnd_269537 < baseStart_269537 := by decide
  rcases family_descends (prefixWord ++ tailWord_269537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269543 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 4]
def baseStart_269543 : Nat := 118140960795 + 269543 * 2 ^ 59
def prefixEnd_269543 : Nat := 4983230072969 + 3 ^ 40 * 269543 * 2
def baseEnd_269543 : Nat := 61513384913308509099067

theorem tailTrace_269543 : CollatzResearch.WordTrace tailWord_269543 prefixEnd_269543 61513384913308509099067 := by
  unfold tailWord_269543
  simp only [CollatzResearch.WordTrace]
  refine ⟨9831040862499220124533283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6554027241666146749688855 9831040862499220124533283)
  ·
    refine ⟨14746561293748830186799925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9831040862499220124533283 14746561293748830186799925)
    ·
      refine ⟨1382490121288952830012493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14746561293748830186799925 1382490121288952830012493)
      ·
        refine ⟨518433795483357311254685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1382490121288952830012493 518433795483357311254685)
        ·
          refine ⟨194412673306258991720507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 518433795483357311254685 194412673306258991720507)
          ·
            refine ⟨291619009959388487580761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194412673306258991720507 291619009959388487580761)
            ·
              refine ⟨218714257469541365685571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 291619009959388487580761 218714257469541365685571)
              ·
                refine ⟨328071386204312048528357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218714257469541365685571 328071386204312048528357)
                ·
                  refine ⟨61513384913308509099067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 328071386204312048528357 61513384913308509099067)
                  ·
                    rfl

theorem cell21_269543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 4].length) (baseStart_269543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269543 prefixEnd_269543 := by exact prefixLift 269543
  have htrace : WordTrace (prefixWord ++ tailWord_269543) baseStart_269543 baseEnd_269543 := by
    simpa [prefixWord, tailWord_269543, baseEnd_269543] using wordTrace_append hprefix tailTrace_269543
  have hstable : (prefixWord ++ tailWord_269543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269543).length < 2 ^ (prefixWord ++ tailWord_269543).sum := by decide
  have hdescent : baseEnd_269543 < baseStart_269543 := by decide
  rcases family_descends (prefixWord ++ tailWord_269543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269599 : List Nat := [1, 1, 2, 4, 4, 2, 1, 6]
def baseStart_269599 : Nat := 118140960795 + 269599 * 2 ^ 59
def prefixEnd_269599 : Nat := 4983230072969 + 3 ^ 40 * 269599 * 2
def baseEnd_269599 : Nat := 20508721625421618721873

theorem tailTrace_269599 : CollatzResearch.WordTrace tailWord_269599 prefixEnd_269599 20508721625421618721873 := by
  unfold tailWord_269599
  simp only [CollatzResearch.WordTrace]
  refine ⟨9833083350296341688571851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6555388900197561125714567 9833083350296341688571851)
  ·
    refine ⟨14749625025444512532857777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9833083350296341688571851 14749625025444512532857777)
    ·
      refine ⟨11062218769083384399643333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14749625025444512532857777 11062218769083384399643333)
      ·
        refine ⟨2074166019203134574933125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11062218769083384399643333 2074166019203134574933125)
        ·
          refine ⟨388906128600587732799961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2074166019203134574933125 388906128600587732799961)
          ·
            refine ⟨291679596450440799599971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 388906128600587732799961 291679596450440799599971)
            ·
              refine ⟨437519394675661199399957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291679596450440799599971 437519394675661199399957)
              ·
                refine ⟨20508721625421618721873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 437519394675661199399957 20508721625421618721873)
                ·
                  rfl

theorem cell21_269599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 6].length) (baseStart_269599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269599 prefixEnd_269599 := by exact prefixLift 269599
  have htrace : WordTrace (prefixWord ++ tailWord_269599) baseStart_269599 baseEnd_269599 := by
    simpa [prefixWord, tailWord_269599, baseEnd_269599] using wordTrace_append hprefix tailTrace_269599
  have hstable : (prefixWord ++ tailWord_269599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269599).length < 2 ^ (prefixWord ++ tailWord_269599).sum := by decide
  have hdescent : baseEnd_269599 < baseStart_269599 := by decide
  rcases family_descends (prefixWord ++ tailWord_269599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269644 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 4]
def baseStart_269644 : Nat := 118140960795 + 269644 * 2 ^ 59
def prefixEnd_269644 : Nat := 4983230072969 + 3 ^ 40 * 269644 * 2
def baseEnd_269644 : Nat := 61536434489354777915527

theorem tailTrace_269644 : CollatzResearch.WordTrace tailWord_269644 prefixEnd_269644 61536434489354777915527 := by
  unfold tailWord_269644
  simp only [CollatzResearch.WordTrace]
  refine ⟨4917362317566657186979993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6556483090088876249306657 4917362317566657186979993)
  ·
    refine ⟨3688021738174992890234995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4917362317566657186979993 3688021738174992890234995)
    ·
      refine ⟨5532032607262489335352493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3688021738174992890234995 5532032607262489335352493)
      ·
        refine ⟨2074512227723433500757185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5532032607262489335352493 2074512227723433500757185)
        ·
          refine ⟨1555884170792575125567889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2074512227723433500757185 1555884170792575125567889)
          ·
            refine ⟨1166913128094431344175917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1555884170792575125567889 1166913128094431344175917)
            ·
              refine ⟨437592423035411754065969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1166913128094431344175917 437592423035411754065969)
              ·
                refine ⟨328194317276558815549477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437592423035411754065969 328194317276558815549477)
                ·
                  refine ⟨61536434489354777915527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 328194317276558815549477 61536434489354777915527)
                  ·
                    rfl

theorem cell21_269644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_269644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269644 prefixEnd_269644 := by exact prefixLift 269644
  have htrace : WordTrace (prefixWord ++ tailWord_269644) baseStart_269644 baseEnd_269644 := by
    simpa [prefixWord, tailWord_269644, baseEnd_269644] using wordTrace_append hprefix tailTrace_269644
  have hstable : (prefixWord ++ tailWord_269644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269644).length < 2 ^ (prefixWord ++ tailWord_269644).sum := by decide
  have hdescent : baseEnd_269644 < baseStart_269644 := by decide
  rcases family_descends (prefixWord ++ tailWord_269644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269703 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 6]
def baseStart_269703 : Nat := 118140960795 + 269703 * 2 ^ 59
def prefixEnd_269703 : Nat := 4983230072969 + 3 ^ 40 * 269703 * 2
def baseEnd_269703 : Nat := 61549899093183786432073

theorem tailTrace_269703 : CollatzResearch.WordTrace tailWord_269703 prefixEnd_269703 61549899093183786432073 := by
  unfold tailWord_269703
  simp only [CollatzResearch.WordTrace]
  refine ⟨9836876541919567450357763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6557917694613044966905175 9836876541919567450357763)
  ·
    refine ⟨14755314812879351175536645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9836876541919567450357763 14755314812879351175536645)
    ·
      refine ⟨2766621527414878345413121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14755314812879351175536645 2766621527414878345413121)
      ·
        refine ⟨2074966145561158759059841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2766621527414878345413121 2074966145561158759059841)
        ·
          refine ⟨1556224609170869069294881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2074966145561158759059841 1556224609170869069294881)
          ·
            refine ⟨1167168456878151801971161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1556224609170869069294881 1167168456878151801971161)
            ·
              refine ⟨875376342658613851478371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1167168456878151801971161 875376342658613851478371)
              ·
                refine ⟨1313064513987920777217557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 875376342658613851478371 1313064513987920777217557)
                ·
                  refine ⟨61549899093183786432073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1313064513987920777217557 61549899093183786432073)
                  ·
                    rfl

theorem cell21_269703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 6].length) (baseStart_269703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269703 prefixEnd_269703 := by exact prefixLift 269703
  have htrace : WordTrace (prefixWord ++ tailWord_269703) baseStart_269703 baseEnd_269703 := by
    simpa [prefixWord, tailWord_269703, baseEnd_269703] using wordTrace_append hprefix tailTrace_269703
  have hstable : (prefixWord ++ tailWord_269703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269703).length < 2 ^ (prefixWord ++ tailWord_269703).sum := by decide
  have hdescent : baseEnd_269703 < baseStart_269703 := by decide
  rcases family_descends (prefixWord ++ tailWord_269703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269717 : List Nat := [1, 3, 2, 1, 1, 2, 3, 8]
def baseStart_269717 : Nat := 118140960795 + 269717 * 2 ^ 59
def prefixEnd_269717 : Nat := 4983230072969 + 3 ^ 40 * 269717 * 2
def baseEnd_269717 : Nat := 20517698027974291066237

theorem tailTrace_269717 : CollatzResearch.WordTrace tailWord_269717 prefixEnd_269717 20517698027974291066237 := by
  unfold tailWord_269717
  simp only [CollatzResearch.WordTrace]
  refine ⟨9837387163868847841367405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6558258109245898560911603 9837387163868847841367405)
  ·
    refine ⟨3689020186450817940512777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9837387163868847841367405 3689020186450817940512777)
    ·
      refine ⟨2766765139838113455384583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3689020186450817940512777 2766765139838113455384583)
      ·
        refine ⟨4150147709757170183076875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2766765139838113455384583 4150147709757170183076875)
        ·
          refine ⟨6225221564635755274615313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4150147709757170183076875 6225221564635755274615313)
          ·
            refine ⟨4668916173476816455961485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6225221564635755274615313 4668916173476816455961485)
            ·
              refine ⟨1750843565053806170985557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4668916173476816455961485 1750843565053806170985557)
              ·
                refine ⟨20517698027974291066237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1750843565053806170985557 20517698027974291066237)
                ·
                  rfl

theorem cell21_269717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 8].length) (baseStart_269717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269717 prefixEnd_269717 := by exact prefixLift 269717
  have htrace : WordTrace (prefixWord ++ tailWord_269717) baseStart_269717 baseEnd_269717 := by
    simpa [prefixWord, tailWord_269717, baseEnd_269717] using wordTrace_append hprefix tailTrace_269717
  have hstable : (prefixWord ++ tailWord_269717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269717).length < 2 ^ (prefixWord ++ tailWord_269717).sum := by decide
  have hdescent : baseEnd_269717 < baseStart_269717 := by decide
  rcases family_descends (prefixWord ++ tailWord_269717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269782 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_269782 : Nat := 118140960795 + 269782 * 2 ^ 59
def prefixEnd_269782 : Nat := 4983230072969 + 3 ^ 40 * 269782 * 2
def baseEnd_269782 : Nat := 61567927969497204615245

theorem tailTrace_269782 : CollatzResearch.WordTrace tailWord_269782 prefixEnd_269782 61567927969497204615245 := by
  unfold tailWord_269782
  simp only [CollatzResearch.WordTrace]
  refine ⟨614984869289585246405225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6559838605755575961655733 614984869289585246405225)
  ·
    refine ⟨461238651967188934803919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 614984869289585246405225 461238651967188934803919)
    ·
      refine ⟨691857977950783402205879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461238651967188934803919 691857977950783402205879)
      ·
        refine ⟨1037786966926175103308819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 691857977950783402205879 1037786966926175103308819)
        ·
          refine ⟨1556680450389262654963229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1037786966926175103308819 1556680450389262654963229)
          ·
            refine ⟨583755168895973495611211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1556680450389262654963229 583755168895973495611211)
            ·
              refine ⟨875632753343960243416817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583755168895973495611211 875632753343960243416817)
              ·
                refine ⟨656724565007970182562613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 875632753343960243416817 656724565007970182562613)
                ·
                  refine ⟨61567927969497204615245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 656724565007970182562613 61567927969497204615245)
                  ·
                    rfl

theorem cell21_269782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_269782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269782 prefixEnd_269782 := by exact prefixLift 269782
  have htrace : WordTrace (prefixWord ++ tailWord_269782) baseStart_269782 baseEnd_269782 := by
    simpa [prefixWord, tailWord_269782, baseEnd_269782] using wordTrace_append hprefix tailTrace_269782
  have hstable : (prefixWord ++ tailWord_269782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269782).length < 2 ^ (prefixWord ++ tailWord_269782).sum := by decide
  have hdescent : baseEnd_269782 < baseStart_269782 := by decide
  rcases family_descends (prefixWord ++ tailWord_269782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269810 : List Nat := [3, 2, 1, 4, 1, 2, 8]
def baseStart_269810 : Nat := 118140960795 + 269810 * 2 ^ 59
def prefixEnd_269810 : Nat := 4983230072969 + 3 ^ 40 * 269810 * 2
def baseEnd_269810 : Nat := 6841590883441708683169

theorem tailTrace_269810 : CollatzResearch.WordTrace tailWord_269810 prefixEnd_269810 6841590883441708683169 := by
  unfold tailWord_269810
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460194788132981181125721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6560519435021283149668589 2460194788132981181125721)
  ·
    refine ⟨1845146091099735885844291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2460194788132981181125721 1845146091099735885844291)
    ·
      refine ⟨2767719136649603828766437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1845146091099735885844291 2767719136649603828766437)
      ·
        refine ⟨518947338121800717893707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2767719136649603828766437 518947338121800717893707)
        ·
          refine ⟨778421007182701076840561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518947338121800717893707 778421007182701076840561)
          ·
            refine ⟨583815755387025807630421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 778421007182701076840561 583815755387025807630421)
            ·
              refine ⟨6841590883441708683169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 583815755387025807630421 6841590883441708683169)
              ·
                rfl

theorem cell21_269810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 8].length) (baseStart_269810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269810 prefixEnd_269810 := by exact prefixLift 269810
  have htrace : WordTrace (prefixWord ++ tailWord_269810) baseStart_269810 baseEnd_269810 := by
    simpa [prefixWord, tailWord_269810, baseEnd_269810] using wordTrace_append hprefix tailTrace_269810
  have hstable : (prefixWord ++ tailWord_269810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269810).length < 2 ^ (prefixWord ++ tailWord_269810).sum := by decide
  have hdescent : baseEnd_269810 < baseStart_269810 := by decide
  rcases family_descends (prefixWord ++ tailWord_269810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269813 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 4]
def baseStart_269813 : Nat := 118140960795 + 269813 * 2 ^ 59
def prefixEnd_269813 : Nat := 4983230072969 + 3 ^ 40 * 269813 * 2
def baseEnd_269813 : Nat := 61575002591848039598515

theorem tailTrace_269813 : CollatzResearch.WordTrace tailWord_269813 prefixEnd_269813 61575002591848039598515 := by
  unfold tailWord_269813
  simp only [CollatzResearch.WordTrace]
  refine ⟨9840888571521056236862093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6560592381014037491241395 9840888571521056236862093)
  ·
    refine ⟨3690333214320396088823285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9840888571521056236862093 3690333214320396088823285)
    ·
      refine ⟨345968738842537133327183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3690333214320396088823285 345968738842537133327183)
      ·
        refine ⟨518953108263805699990775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345968738842537133327183 518953108263805699990775)
        ·
          refine ⟨778429662395708549986163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518953108263805699990775 778429662395708549986163)
          ·
            refine ⟨1167644493593562824979245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 778429662395708549986163 1167644493593562824979245)
            ·
              refine ⟨437866685097586059367217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1167644493593562824979245 437866685097586059367217)
              ·
                refine ⟨328400013823189544525413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 437866685097586059367217 328400013823189544525413)
                ·
                  refine ⟨61575002591848039598515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 328400013823189544525413 61575002591848039598515)
                  ·
                    rfl

theorem cell21_269813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_269813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269813 prefixEnd_269813 := by exact prefixLift 269813
  have htrace : WordTrace (prefixWord ++ tailWord_269813) baseStart_269813 baseEnd_269813 := by
    simpa [prefixWord, tailWord_269813, baseEnd_269813] using wordTrace_append hprefix tailTrace_269813
  have hstable : (prefixWord ++ tailWord_269813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269813).length < 2 ^ (prefixWord ++ tailWord_269813).sum := by decide
  have hdescent : baseEnd_269813 < baseStart_269813 := by decide
  rcases family_descends (prefixWord ++ tailWord_269813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269858 : List Nat := [3, 3, 1, 1, 1, 1, 5, 3, 3]
def baseStart_269858 : Nat := 118140960795 + 269858 * 2 ^ 59
def prefixEnd_269858 : Nat := 4983230072969 + 3 ^ 40 * 269858 * 2
def baseEnd_269858 : Nat := 61585272204937961348423

theorem tailTrace_269858 : CollatzResearch.WordTrace tailWord_269858 prefixEnd_269858 61585272204937961348423 := by
  unfold tailWord_269858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2460632464089507230562557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6561686570905352614833485 2460632464089507230562557)
  ·
    refine ⟨922737174033565211460959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2460632464089507230562557 922737174033565211460959)
    ·
      refine ⟨1384105761050347817191439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 922737174033565211460959 1384105761050347817191439)
      ·
        refine ⟨2076158641575521725787159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1384105761050347817191439 2076158641575521725787159)
        ·
          refine ⟨3114237962363282588680739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2076158641575521725787159 3114237962363282588680739)
          ·
            refine ⟨4671356943544923883021109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3114237962363282588680739 4671356943544923883021109)
            ·
              refine ⟨437939713457336614033229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4671356943544923883021109 437939713457336614033229)
              ·
                refine ⟨164227392546501230262461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 437939713457336614033229 164227392546501230262461)
                ·
                  refine ⟨61585272204937961348423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164227392546501230262461 61585272204937961348423)
                  ·
                    rfl

theorem cell21_269858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_269858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269858 prefixEnd_269858 := by exact prefixLift 269858
  have htrace : WordTrace (prefixWord ++ tailWord_269858) baseStart_269858 baseEnd_269858 := by
    simpa [prefixWord, tailWord_269858, baseEnd_269858] using wordTrace_append hprefix tailTrace_269858
  have hstable : (prefixWord ++ tailWord_269858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269858).length < 2 ^ (prefixWord ++ tailWord_269858).sum := by decide
  have hdescent : baseEnd_269858 < baseStart_269858 := by decide
  rcases family_descends (prefixWord ++ tailWord_269858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_269914 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_269914 : Nat := 118140960795 + 269914 * 2 ^ 59
def prefixEnd_269914 : Nat := 4983230072969 + 3 ^ 40 * 269914 * 2
def baseEnd_269914 : Nat := 61598052167894308414975

theorem tailTrace_269914 : CollatzResearch.WordTrace tailWord_269914 prefixEnd_269914 61598052167894308414975 := by
  unfold tailWord_269914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2461143086038787621572199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6563048229436766990859197 2461143086038787621572199)
  ·
    refine ⟨3691714629058181432358299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2461143086038787621572199 3691714629058181432358299)
    ·
      refine ⟨5537571943587272148537449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3691714629058181432358299 5537571943587272148537449)
      ·
        refine ⟨4153178957690454111403087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5537571943587272148537449 4153178957690454111403087)
        ·
          refine ⟨6229768436535681167104631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4153178957690454111403087 6229768436535681167104631)
          ·
            refine ⟨9344652654803521750656947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6229768436535681167104631 9344652654803521750656947)
            ·
              refine ⟨14016978982205282625985421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9344652654803521750656947 14016978982205282625985421)
              ·
                refine ⟨5256367118326980984744533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14016978982205282625985421 5256367118326980984744533)
                ·
                  refine ⟨61598052167894308414975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5256367118326980984744533 61598052167894308414975)
                  ·
                    rfl

theorem cell21_269914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_269914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_269914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_269914 prefixEnd_269914 := by exact prefixLift 269914
  have htrace : WordTrace (prefixWord ++ tailWord_269914) baseStart_269914 baseEnd_269914 := by
    simpa [prefixWord, tailWord_269914, baseEnd_269914] using wordTrace_append hprefix tailTrace_269914
  have hstable : (prefixWord ++ tailWord_269914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_269914).length < 2 ^ (prefixWord ++ tailWord_269914).sum := by decide
  have hdescent : baseEnd_269914 < baseStart_269914 := by decide
  rcases family_descends (prefixWord ++ tailWord_269914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270044 : List Nat := [2, 2, 5, 1, 2, 1, 3, 2, 3]
def baseStart_270044 : Nat := 118140960795 + 270044 * 2 ^ 59
def prefixEnd_270044 : Nat := 4983230072969 + 3 ^ 40 * 270044 * 2
def baseEnd_270044 : Nat := 61627719939042971248043

theorem tailTrace_270044 : CollatzResearch.WordTrace tailWord_270044 prefixEnd_270044 61627719939042971248043 := by
  unfold tailWord_270044
  simp only [CollatzResearch.WordTrace]
  refine ⟨4924656916842091344260593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6566209222456121792347457 4924656916842091344260593)
  ·
    refine ⟨3693492687631568508195445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4924656916842091344260593 3693492687631568508195445)
    ·
      refine ⟨346264939465459547643323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3693492687631568508195445 346264939465459547643323)
      ·
        refine ⟨519397409198189321464985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346264939465459547643323 519397409198189321464985)
        ·
          refine ⟨389548056898641991098739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 519397409198189321464985 389548056898641991098739)
          ·
            refine ⟨584322085347962986648109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389548056898641991098739 584322085347962986648109)
            ·
              refine ⟨219120782005486119993041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 584322085347962986648109 219120782005486119993041)
              ·
                refine ⟨164340586504114589994781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219120782005486119993041 164340586504114589994781)
                ·
                  refine ⟨61627719939042971248043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164340586504114589994781 61627719939042971248043)
                  ·
                    rfl

theorem cell21_270044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 3].length) (baseStart_270044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270044 prefixEnd_270044 := by exact prefixLift 270044
  have htrace : WordTrace (prefixWord ++ tailWord_270044) baseStart_270044 baseEnd_270044 := by
    simpa [prefixWord, tailWord_270044, baseEnd_270044] using wordTrace_append hprefix tailTrace_270044
  have hstable : (prefixWord ++ tailWord_270044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270044).length < 2 ^ (prefixWord ++ tailWord_270044).sum := by decide
  have hdescent : baseEnd_270044 < baseStart_270044 := by decide
  rcases family_descends (prefixWord ++ tailWord_270044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270055 : List Nat := [1, 1, 5, 4, 1, 1, 2, 6]
def baseStart_270055 : Nat := 118140960795 + 270055 * 2 ^ 59
def prefixEnd_270055 : Nat := 4983230072969 + 3 ^ 40 * 270055 * 2
def baseEnd_270055 : Nat := 20543410096303132188229

theorem tailTrace_270055 : CollatzResearch.WordTrace tailWord_270055 prefixEnd_270055 20543410096303132188229 := by
  unfold tailWord_270055
  simp only [CollatzResearch.WordTrace]
  refine ⟨9849715036644331567171619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6566476691096221044781079 9849715036644331567171619)
  ·
    refine ⟨14774572554966497350757429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9849715036644331567171619 14774572554966497350757429)
    ·
      refine ⟨1385116177028109126633509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14774572554966497350757429 1385116177028109126633509)
      ·
        refine ⟨259709283192770461243783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1385116177028109126633509 259709283192770461243783)
        ·
          refine ⟨389563924789155691865675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259709283192770461243783 389563924789155691865675)
          ·
            refine ⟨584345887183733537798513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 389563924789155691865675 584345887183733537798513)
            ·
              refine ⟨438259415387800153348885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 584345887183733537798513 438259415387800153348885)
              ·
                refine ⟨20543410096303132188229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 438259415387800153348885 20543410096303132188229)
                ·
                  rfl

theorem cell21_270055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 6].length) (baseStart_270055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270055 prefixEnd_270055 := by exact prefixLift 270055
  have htrace : WordTrace (prefixWord ++ tailWord_270055) baseStart_270055 baseEnd_270055 := by
    simpa [prefixWord, tailWord_270055, baseEnd_270055] using wordTrace_append hprefix tailTrace_270055
  have hstable : (prefixWord ++ tailWord_270055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270055).length < 2 ^ (prefixWord ++ tailWord_270055).sum := by decide
  have hdescent : baseEnd_270055 < baseStart_270055 := by decide
  rcases family_descends (prefixWord ++ tailWord_270055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270103 : List Nat := [1, 1, 3, 4, 2, 3, 2, 2, 3]
def baseStart_270103 : Nat := 118140960795 + 270103 * 2 ^ 59
def prefixEnd_270103 : Nat := 4983230072969 + 3 ^ 40 * 270103 * 2
def baseEnd_270103 : Nat := 61641184542871979764589

theorem tailTrace_270103 : CollatzResearch.WordTrace tailWord_270103 prefixEnd_270103 61641184542871979764589 := by
  unfold tailWord_270103
  simp only [CollatzResearch.WordTrace]
  refine ⟨9851465740470435764918963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6567643826980290509945975 9851465740470435764918963)
  ·
    refine ⟨14777198610705653647378445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9851465740470435764918963 14777198610705653647378445)
    ·
      refine ⟨5541449479014620117766917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14777198610705653647378445 5541449479014620117766917)
      ·
        refine ⟨1039021777315241272081297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5541449479014620117766917 1039021777315241272081297)
        ·
          refine ⟨779266332986430954060973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1039021777315241272081297 779266332986430954060973)
          ·
            refine ⟨292224874869911607772865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 779266332986430954060973 292224874869911607772865)
            ·
              refine ⟨219168656152433705829649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292224874869911607772865 219168656152433705829649)
              ·
                refine ⟨164376492114325279372237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219168656152433705829649 164376492114325279372237)
                ·
                  refine ⟨61641184542871979764589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164376492114325279372237 61641184542871979764589)
                  ·
                    rfl

theorem cell21_270103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 3].length) (baseStart_270103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270103 prefixEnd_270103 := by exact prefixLift 270103
  have htrace : WordTrace (prefixWord ++ tailWord_270103) baseStart_270103 baseEnd_270103 := by
    simpa [prefixWord, tailWord_270103, baseEnd_270103] using wordTrace_append hprefix tailTrace_270103
  have hstable : (prefixWord ++ tailWord_270103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270103).length < 2 ^ (prefixWord ++ tailWord_270103).sum := by decide
  have hdescent : baseEnd_270103 < baseStart_270103 := by decide
  rcases family_descends (prefixWord ++ tailWord_270103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270176 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 4]
def baseStart_270176 : Nat := 118140960795 + 270176 * 2 ^ 59
def prefixEnd_270176 : Nat := 4983230072969 + 3 ^ 40 * 270176 * 2
def baseEnd_270176 : Nat := 61657844137440075047773

theorem tailTrace_270176 : CollatzResearch.WordTrace tailWord_270176 prefixEnd_270176 61657844137440075047773 := by
  unfold tailWord_270176
  simp only [CollatzResearch.WordTrace]
  refine ⟨4927064134602984616163191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6569418846137312821550921 4927064134602984616163191)
  ·
    refine ⟨7390596201904476924244787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4927064134602984616163191 7390596201904476924244787)
    ·
      refine ⟨11085894302856715386367181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7390596201904476924244787 11085894302856715386367181)
      ·
        refine ⟨4157210363571268269887693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11085894302856715386367181 4157210363571268269887693)
        ·
          refine ⟨1558953886339225601207885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4157210363571268269887693 1558953886339225601207885)
          ·
            refine ⟨584607707377209600452957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1558953886339225601207885 584607707377209600452957)
            ·
              refine ⟨219227890266453600169859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 584607707377209600452957 219227890266453600169859)
              ·
                refine ⟨328841835399680400254789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219227890266453600169859 328841835399680400254789)
                ·
                  refine ⟨61657844137440075047773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 328841835399680400254789 61657844137440075047773)
                  ·
                    rfl

theorem cell21_270176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_270176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270176 prefixEnd_270176 := by exact prefixLift 270176
  have htrace : WordTrace (prefixWord ++ tailWord_270176) baseStart_270176 baseEnd_270176 := by
    simpa [prefixWord, tailWord_270176, baseEnd_270176] using wordTrace_append hprefix tailTrace_270176
  have hstable : (prefixWord ++ tailWord_270176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270176).length < 2 ^ (prefixWord ++ tailWord_270176).sum := by decide
  have hdescent : baseEnd_270176 < baseStart_270176 := by decide
  rcases family_descends (prefixWord ++ tailWord_270176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270190 : List Nat := [4, 1, 2, 3, 1, 2, 1, 7]
def baseStart_270190 : Nat := 118140960795 + 270190 * 2 ^ 59
def prefixEnd_270190 : Nat := 4983230072969 + 3 ^ 40 * 270190 * 2
def baseEnd_270190 : Nat := 20553679709393053938137

theorem tailTrace_270190 : CollatzResearch.WordTrace tailWord_270190 prefixEnd_270190 20553679709393053938137 := by
  unfold tailWord_270190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1231829861394406202917003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6569759260770166415557349 1231829861394406202917003)
  ·
    refine ⟨1847744792091609304375505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1231829861394406202917003 1847744792091609304375505)
    ·
      refine ⟨1385808594068706978281629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1847744792091609304375505 1385808594068706978281629)
      ·
        refine ⟨519678222775765116855611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1385808594068706978281629 519678222775765116855611)
        ·
          refine ⟨779517334163647675283417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 519678222775765116855611 779517334163647675283417)
          ·
            refine ⟨584638000622735756462563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 779517334163647675283417 584638000622735756462563)
            ·
              refine ⟨876957000934103634693845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 584638000622735756462563 876957000934103634693845)
              ·
                refine ⟨20553679709393053938137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 876957000934103634693845 20553679709393053938137)
                ·
                  rfl

theorem cell21_270190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_270190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270190 prefixEnd_270190 := by exact prefixLift 270190
  have htrace : WordTrace (prefixWord ++ tailWord_270190) baseStart_270190 baseEnd_270190 := by
    simpa [prefixWord, tailWord_270190, baseEnd_270190] using wordTrace_append hprefix tailTrace_270190
  have hstable : (prefixWord ++ tailWord_270190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270190).length < 2 ^ (prefixWord ++ tailWord_270190).sum := by decide
  have hdescent : baseEnd_270190 < baseStart_270190 := by decide
  rcases family_descends (prefixWord ++ tailWord_270190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270359 : List Nat := [1, 1, 3, 5, 2, 2, 2, 5]
def baseStart_270359 : Nat := 118140960795 + 270359 * 2 ^ 59
def prefixEnd_270359 : Nat := 4983230072969 + 3 ^ 40 * 270359 * 2
def baseEnd_270359 : Nat := 20566535743557474499133

theorem tailTrace_270359 : CollatzResearch.WordTrace tailWord_270359 prefixEnd_270359 20566535743557474499133 := by
  unfold tailWord_270359
  simp only [CollatzResearch.WordTrace]
  refine ⟨9860802827542991486238131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6573868551695327657492087 9860802827542991486238131)
  ·
    refine ⟨14791204241314487229357197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9860802827542991486238131 14791204241314487229357197)
    ·
      refine ⟨5546701590492932711008949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14791204241314487229357197 5546701590492932711008949)
      ·
        refine ⟨520003274108712441657089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5546701590492932711008949 520003274108712441657089)
        ·
          refine ⟨390002455581534331242817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520003274108712441657089 390002455581534331242817)
          ·
            refine ⟨292501841686150748432113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390002455581534331242817 292501841686150748432113)
            ·
              refine ⟨219376381264613061324085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292501841686150748432113 219376381264613061324085)
              ·
                refine ⟨20566535743557474499133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 219376381264613061324085 20566535743557474499133)
                ·
                  rfl

theorem cell21_270359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 5].length) (baseStart_270359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270359 prefixEnd_270359 := by exact prefixLift 270359
  have htrace : WordTrace (prefixWord ++ tailWord_270359) baseStart_270359 baseEnd_270359 := by
    simpa [prefixWord, tailWord_270359, baseEnd_270359] using wordTrace_append hprefix tailTrace_270359
  have hstable : (prefixWord ++ tailWord_270359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270359).length < 2 ^ (prefixWord ++ tailWord_270359).sum := by decide
  have hdescent : baseEnd_270359 < baseStart_270359 := by decide
  rcases family_descends (prefixWord ++ tailWord_270359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270370 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 8]
def baseStart_270370 : Nat := 118140960795 + 270370 * 2 ^ 59
def prefixEnd_270370 : Nat := 4983230072969 + 3 ^ 40 * 270370 * 2
def baseEnd_270370 : Nat := 61702117580538848814043

theorem tailTrace_270370 : CollatzResearch.WordTrace tailWord_270370 prefixEnd_270370 61702117580538848814043 := by
  unfold tailWord_270370
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465301007625785091222141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6574136020335426909925709 2465301007625785091222141)
  ·
    refine ⟨924487877859669409208303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2465301007625785091222141 924487877859669409208303)
    ·
      refine ⟨1386731816789504113812455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 924487877859669409208303 1386731816789504113812455)
      ·
        refine ⟨2080097725184256170718683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1386731816789504113812455 2080097725184256170718683)
        ·
          refine ⟨3120146587776384256078025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2080097725184256170718683 3120146587776384256078025)
          ·
            refine ⟨2340109940832288192058519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3120146587776384256078025 2340109940832288192058519)
            ·
              refine ⟨3510164911248432288087779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2340109940832288192058519 3510164911248432288087779)
              ·
                refine ⟨5265247366872648432131669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3510164911248432288087779 5265247366872648432131669)
                ·
                  refine ⟨61702117580538848814043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5265247366872648432131669 61702117580538848814043)
                  ·
                    rfl

theorem cell21_270370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_270370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270370 prefixEnd_270370 := by exact prefixLift 270370
  have htrace : WordTrace (prefixWord ++ tailWord_270370) baseStart_270370 baseEnd_270370 := by
    simpa [prefixWord, tailWord_270370, baseEnd_270370] using wordTrace_append hprefix tailTrace_270370
  have hstable : (prefixWord ++ tailWord_270370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270370).length < 2 ^ (prefixWord ++ tailWord_270370).sum := by decide
  have hdescent : baseEnd_270370 < baseStart_270370 := by decide
  rcases family_descends (prefixWord ++ tailWord_270370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270373 : List Nat := [1, 3, 1, 2, 2, 3, 3, 3, 3]
def baseStart_270373 : Nat := 118140960795 + 270373 * 2 ^ 59
def prefixEnd_270373 : Nat := 4983230072969 + 3 ^ 40 * 270373 * 2
def baseEnd_270373 : Nat := 61702802221411510264037

theorem tailTrace_270373 : CollatzResearch.WordTrace tailWord_270373 prefixEnd_270373 61702802221411510264037 := by
  unfold tailWord_270373
  simp only [CollatzResearch.WordTrace]
  refine ⟨9861313449492271877247773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6574208966328181251498515 9861313449492271877247773)
  ·
    refine ⟨3697992543559601953967915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9861313449492271877247773 3697992543559601953967915)
    ·
      refine ⟨5546988815339402930951873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3697992543559601953967915 5546988815339402930951873)
      ·
        refine ⟨4160241611504552198213905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5546988815339402930951873 4160241611504552198213905)
        ·
          refine ⟨3120181208628414148660429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4160241611504552198213905 3120181208628414148660429)
          ·
            refine ⟨1170067953235655305747661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3120181208628414148660429 1170067953235655305747661)
            ·
              refine ⟨438775482463370739655373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1170067953235655305747661 438775482463370739655373)
              ·
                refine ⟨164540805923764027370765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 438775482463370739655373 164540805923764027370765)
                ·
                  refine ⟨61702802221411510264037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164540805923764027370765 61702802221411510264037)
                  ·
                    rfl

theorem cell21_270373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 3].length) (baseStart_270373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270373 prefixEnd_270373 := by exact prefixLift 270373
  have htrace : WordTrace (prefixWord ++ tailWord_270373) baseStart_270373 baseEnd_270373 := by
    simpa [prefixWord, tailWord_270373, baseEnd_270373] using wordTrace_append hprefix tailTrace_270373
  have hstable : (prefixWord ++ tailWord_270373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270373).length < 2 ^ (prefixWord ++ tailWord_270373).sum := by decide
  have hdescent : baseEnd_270373 < baseStart_270373 := by decide
  rcases family_descends (prefixWord ++ tailWord_270373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270384 : List Nat := [2, 1, 1, 1, 2, 5, 9]
def baseStart_270384 : Nat := 118140960795 + 270384 * 2 ^ 59
def prefixEnd_270384 : Nat := 4983230072969 + 3 ^ 40 * 270384 * 2
def baseEnd_270384 : Nat := 6856145841253103953409

theorem tailTrace_270384 : CollatzResearch.WordTrace tailWord_270384 prefixEnd_270384 6856145841253103953409 := by
  unfold tailWord_270384
  simp only [CollatzResearch.WordTrace]
  refine ⟨4930857326226210377949103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6574476434968280503932137 4930857326226210377949103)
  ·
    refine ⟨7396285989339315566923655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4930857326226210377949103 7396285989339315566923655)
    ·
      refine ⟨11094428984008973350385483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7396285989339315566923655 11094428984008973350385483)
      ·
        refine ⟨16641643476013460025578225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11094428984008973350385483 16641643476013460025578225)
        ·
          refine ⟨12481232607010095019183669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16641643476013460025578225 12481232607010095019183669)
          ·
            refine ⟨1170115556907196408048469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12481232607010095019183669 1170115556907196408048469)
            ·
              refine ⟨6856145841253103953409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1170115556907196408048469 6856145841253103953409)
              ·
                rfl

theorem cell21_270384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 9].length) (baseStart_270384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270384 prefixEnd_270384 := by exact prefixLift 270384
  have htrace : WordTrace (prefixWord ++ tailWord_270384) baseStart_270384 baseEnd_270384 := by
    simpa [prefixWord, tailWord_270384, baseEnd_270384] using wordTrace_append hprefix tailTrace_270384
  have hstable : (prefixWord ++ tailWord_270384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270384).length < 2 ^ (prefixWord ++ tailWord_270384).sum := by decide
  have hdescent : baseEnd_270384 < baseStart_270384 := by decide
  rcases family_descends (prefixWord ++ tailWord_270384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270401 : List Nat := [1, 2, 5, 1, 2, 1, 1, 8]
def baseStart_270401 : Nat := 118140960795 + 270401 * 2 ^ 59
def prefixEnd_270401 : Nat := 4983230072969 + 3 ^ 40 * 270401 * 2
def baseEnd_270401 : Nat := 20569730734296561265771

theorem tailTrace_270401 : CollatzResearch.WordTrace tailWord_270401 prefixEnd_270401 20569730734296561265771 := by
  unfold tailWord_270401
  simp only [CollatzResearch.WordTrace]
  refine ⟨9862334693390832659267057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6574889795593888439511371 9862334693390832659267057)
  ·
    refine ⟨7396751020043124494450293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9862334693390832659267057 7396751020043124494450293)
    ·
      refine ⟨693445408129042921354715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7396751020043124494450293 693445408129042921354715)
      ·
        refine ⟨1040168112193564382032073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693445408129042921354715 1040168112193564382032073)
        ·
          refine ⟨780126084145173286524055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1040168112193564382032073 780126084145173286524055)
          ·
            refine ⟨1170189126217759929786083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780126084145173286524055 1170189126217759929786083)
            ·
              refine ⟨1755283689326639894679125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1170189126217759929786083 1755283689326639894679125)
              ·
                refine ⟨20569730734296561265771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1755283689326639894679125 20569730734296561265771)
                ·
                  rfl

theorem cell21_270401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 8].length) (baseStart_270401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270401 prefixEnd_270401 := by exact prefixLift 270401
  have htrace : WordTrace (prefixWord ++ tailWord_270401) baseStart_270401 baseEnd_270401 := by
    simpa [prefixWord, tailWord_270401, baseEnd_270401] using wordTrace_append hprefix tailTrace_270401
  have hstable : (prefixWord ++ tailWord_270401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270401).length < 2 ^ (prefixWord ++ tailWord_270401).sum := by decide
  have hdescent : baseEnd_270401 < baseStart_270401 := by decide
  rcases family_descends (prefixWord ++ tailWord_270401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270494 : List Nat := [4, 3, 1, 1, 3, 1, 8]
def baseStart_270494 : Nat := 118140960795 + 270494 * 2 ^ 59
def prefixEnd_270494 : Nat := 4983230072969 + 3 ^ 40 * 270494 * 2
def baseEnd_270494 : Nat := 6858935118882465416347

theorem tailTrace_270494 : CollatzResearch.WordTrace tailWord_270494 prefixEnd_270494 6858935118882465416347 := by
  unfold tailWord_270494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1233215835256738692800317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6577151121369273028268357 1233215835256738692800317)
  ·
    refine ⟨462455938221277009800119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1233215835256738692800317 462455938221277009800119)
    ·
      refine ⟨693683907331915514700179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 462455938221277009800119 693683907331915514700179)
      ·
        refine ⟨1040525860997873272050269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 693683907331915514700179 1040525860997873272050269)
        ·
          refine ⟨390197197874202477018851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1040525860997873272050269 390197197874202477018851)
          ·
            refine ⟨585295796811303715528277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390197197874202477018851 585295796811303715528277)
            ·
              refine ⟨6858935118882465416347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 585295796811303715528277 6858935118882465416347)
              ·
                rfl

theorem cell21_270494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 8].length) (baseStart_270494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270494 prefixEnd_270494 := by exact prefixLift 270494
  have htrace : WordTrace (prefixWord ++ tailWord_270494) baseStart_270494 baseEnd_270494 := by
    simpa [prefixWord, tailWord_270494, baseEnd_270494] using wordTrace_append hprefix tailTrace_270494
  have hstable : (prefixWord ++ tailWord_270494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270494).length < 2 ^ (prefixWord ++ tailWord_270494).sum := by decide
  have hdescent : baseEnd_270494 < baseStart_270494 := by decide
  rcases family_descends (prefixWord ++ tailWord_270494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270522 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_270522 : Nat := 118140960795 + 270522 * 2 ^ 59
def prefixEnd_270522 : Nat := 4983230072969 + 3 ^ 40 * 270522 * 2
def baseEnd_270522 : Nat := 61736806051420362280399

theorem tailTrace_270522 : CollatzResearch.WordTrace tailWord_270522 prefixEnd_270522 61736806051420362280399 := by
  unfold tailWord_270522
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466686981488117581105455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6577831950634980216281213 2466686981488117581105455)
  ·
    refine ⟨3700030472232176371658183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2466686981488117581105455 3700030472232176371658183)
    ·
      refine ⟨5550045708348264557487275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3700030472232176371658183 5550045708348264557487275)
      ·
        refine ⟨8325068562522396836230913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5550045708348264557487275 8325068562522396836230913)
        ·
          refine ⟨6243801421891797627173185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8325068562522396836230913 6243801421891797627173185)
          ·
            refine ⟨4682851066418848220379889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6243801421891797627173185 4682851066418848220379889)
            ·
              refine ⟨3512138299814136165284917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4682851066418848220379889 3512138299814136165284917)
              ·
                refine ⟨329262965607575265495461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3512138299814136165284917 329262965607575265495461)
                ·
                  refine ⟨61736806051420362280399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 329262965607575265495461 61736806051420362280399)
                  ·
                    rfl

theorem cell21_270522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_270522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270522 prefixEnd_270522 := by exact prefixLift 270522
  have htrace : WordTrace (prefixWord ++ tailWord_270522) baseStart_270522 baseEnd_270522 := by
    simpa [prefixWord, tailWord_270522, baseEnd_270522] using wordTrace_append hprefix tailTrace_270522
  have hstable : (prefixWord ++ tailWord_270522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270522).length < 2 ^ (prefixWord ++ tailWord_270522).sum := by decide
  have hdescent : baseEnd_270522 < baseStart_270522 := by decide
  rcases family_descends (prefixWord ++ tailWord_270522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270542 : List Nat := [4, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_270542 : Nat := 118140960795 + 270542 * 2 ^ 59
def prefixEnd_270542 : Nat := 4983230072969 + 3 ^ 40 * 270542 * 2
def baseEnd_270542 : Nat := 61741370323904771947025

theorem tailTrace_270542 : CollatzResearch.WordTrace tailWord_270542 prefixEnd_270542 61741370323904771947025 := by
  unfold tailWord_270542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1233434673235001717518735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6578318257253342493433253 1233434673235001717518735)
  ·
    refine ⟨1850152009852502576278103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1233434673235001717518735 1850152009852502576278103)
    ·
      refine ⟨2775228014778753864417155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1850152009852502576278103 2775228014778753864417155)
      ·
        refine ⟨4162842022168130796625733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775228014778753864417155 4162842022168130796625733)
        ·
          refine ⟨780532879156524524367325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4162842022168130796625733 780532879156524524367325)
          ·
            refine ⟨292699829683696696637747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 780532879156524524367325 292699829683696696637747)
            ·
              refine ⟨439049744525545044956621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292699829683696696637747 439049744525545044956621)
              ·
                refine ⟨164643654197079391858733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 439049744525545044956621 164643654197079391858733)
                ·
                  refine ⟨61741370323904771947025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164643654197079391858733 61741370323904771947025)
                  ·
                    rfl

theorem cell21_270542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_270542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270542 prefixEnd_270542 := by exact prefixLift 270542
  have htrace : WordTrace (prefixWord ++ tailWord_270542) baseStart_270542 baseEnd_270542 := by
    simpa [prefixWord, tailWord_270542, baseEnd_270542] using wordTrace_append hprefix tailTrace_270542
  have hstable : (prefixWord ++ tailWord_270542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270542).length < 2 ^ (prefixWord ++ tailWord_270542).sum := by decide
  have hdescent : baseEnd_270542 < baseStart_270542 := by decide
  rcases family_descends (prefixWord ++ tailWord_270542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270573 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 4]
def baseStart_270573 : Nat := 118140960795 + 270573 * 2 ^ 59
def prefixEnd_270573 : Nat := 4983230072969 + 3 ^ 40 * 270573 * 2
def baseEnd_270573 : Nat := 61748444946255606930295

theorem tailTrace_270573 : CollatzResearch.WordTrace tailWord_270573 prefixEnd_270573 61748444946255606930295 := by
  unfold tailWord_270573
  simp only [CollatzResearch.WordTrace]
  refine ⟨9868608048767706034528373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6579072032511804023018915 9868608048767706034528373)
  ·
    refine ⟨925182004571972440737035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9868608048767706034528373 925182004571972440737035)
    ·
      refine ⟨1387773006857958661105553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 925182004571972440737035 1387773006857958661105553)
      ·
        refine ⟨1040829755143468995829165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1387773006857958661105553 1040829755143468995829165)
        ·
          refine ⟨390311158178800873435937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1040829755143468995829165 390311158178800873435937)
          ·
            refine ⟨292733368634100655076953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390311158178800873435937 292733368634100655076953)
            ·
              refine ⟨219550026475575491307715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 292733368634100655076953 219550026475575491307715)
              ·
                refine ⟨329325039713363236961573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219550026475575491307715 329325039713363236961573)
                ·
                  refine ⟨61748444946255606930295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 329325039713363236961573 61748444946255606930295)
                  ·
                    rfl

theorem cell21_270573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_270573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270573 prefixEnd_270573 := by exact prefixLift 270573
  have htrace : WordTrace (prefixWord ++ tailWord_270573) baseStart_270573 baseEnd_270573 := by
    simpa [prefixWord, tailWord_270573, baseEnd_270573] using wordTrace_append hprefix tailTrace_270573
  have hstable : (prefixWord ++ tailWord_270573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270573).length < 2 ^ (prefixWord ++ tailWord_270573).sum := by decide
  have hdescent : baseEnd_270573 < baseStart_270573 := by decide
  rcases family_descends (prefixWord ++ tailWord_270573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270615 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 4]
def baseStart_270615 : Nat := 118140960795 + 270615 * 2 ^ 59
def prefixEnd_270615 : Nat := 4983230072969 + 3 ^ 40 * 270615 * 2
def baseEnd_270615 : Nat := 61758029918472867230209

theorem tailTrace_270615 : CollatzResearch.WordTrace tailWord_270615 prefixEnd_270615 61758029918472867230209 := by
  unfold tailWord_270615
  simp only [CollatzResearch.WordTrace]
  refine ⟨9870139914615547207557299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6580093276410364805038199 9870139914615547207557299)
  ·
    refine ⟨14805209871923320811335949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9870139914615547207557299 14805209871923320811335949)
    ·
      refine ⟨5551953701971245304250981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14805209871923320811335949 5551953701971245304250981)
      ·
        refine ⟨1040991319119608494547059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5551953701971245304250981 1040991319119608494547059)
        ·
          refine ⟨1561486978679412741820589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1040991319119608494547059 1561486978679412741820589)
          ·
            refine ⟨585557617004779778182721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1561486978679412741820589 585557617004779778182721)
            ·
              refine ⟨439168212753584833637041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585557617004779778182721 439168212753584833637041)
              ·
                refine ⟨329376159565188625227781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439168212753584833637041 329376159565188625227781)
                ·
                  refine ⟨61758029918472867230209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 329376159565188625227781 61758029918472867230209)
                  ·
                    rfl

theorem cell21_270615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 4].length) (baseStart_270615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270615 prefixEnd_270615 := by exact prefixLift 270615
  have htrace : WordTrace (prefixWord ++ tailWord_270615) baseStart_270615 baseEnd_270615 := by
    simpa [prefixWord, tailWord_270615, baseEnd_270615] using wordTrace_append hprefix tailTrace_270615
  have hstable : (prefixWord ++ tailWord_270615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270615).length < 2 ^ (prefixWord ++ tailWord_270615).sum := by decide
  have hdescent : baseEnd_270615 < baseStart_270615 := by decide
  rcases family_descends (prefixWord ++ tailWord_270615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270643 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 5]
def baseStart_270643 : Nat := 118140960795 + 270643 * 2 ^ 59
def prefixEnd_270643 : Nat := 4983230072969 + 3 ^ 40 * 270643 * 2
def baseEnd_270643 : Nat := 61764419899951040763485

theorem tailTrace_270643 : CollatzResearch.WordTrace tailWord_270643 prefixEnd_270643 61764419899951040763485 := by
  unfold tailWord_270643
  simp only [CollatzResearch.WordTrace]
  refine ⟨9871161158514107989576583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6580774105676071993051055 9871161158514107989576583)
  ·
    refine ⟨14806741737771161984364875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9871161158514107989576583 14806741737771161984364875)
    ·
      refine ⟨22210112606656742976547313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14806741737771161984364875 22210112606656742976547313)
      ·
        refine ⟨16657584454992557232410485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22210112606656742976547313 16657584454992557232410485)
        ·
          refine ⟨1561648542655552240538483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16657584454992557232410485 1561648542655552240538483)
          ·
            refine ⟨2342472813983328360807725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561648542655552240538483 2342472813983328360807725)
            ·
              refine ⟨878427305243748135302897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2342472813983328360807725 878427305243748135302897)
              ·
                refine ⟨658820478932811101477173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 878427305243748135302897 658820478932811101477173)
                ·
                  refine ⟨61764419899951040763485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 658820478932811101477173 61764419899951040763485)
                  ·
                    rfl

theorem cell21_270643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 5].length) (baseStart_270643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270643 prefixEnd_270643 := by exact prefixLift 270643
  have htrace : WordTrace (prefixWord ++ tailWord_270643) baseStart_270643 baseEnd_270643 := by
    simpa [prefixWord, tailWord_270643, baseEnd_270643] using wordTrace_append hprefix tailTrace_270643
  have hstable : (prefixWord ++ tailWord_270643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270643).length < 2 ^ (prefixWord ++ tailWord_270643).sum := by decide
  have hdescent : baseEnd_270643 < baseStart_270643 := by decide
  rcases family_descends (prefixWord ++ tailWord_270643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270691 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 4]
def baseStart_270691 : Nat := 118140960795 + 270691 * 2 ^ 59
def prefixEnd_270691 : Nat := 4983230072969 + 3 ^ 40 * 270691 * 2
def baseEnd_270691 : Nat := 61775374153913623963387

theorem tailTrace_270691 : CollatzResearch.WordTrace tailWord_270691 prefixEnd_270691 61775374153913623963387 := by
  unfold tailWord_270691
  simp only [CollatzResearch.WordTrace]
  refine ⟨9872911862340212187323927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6581941241560141458215951 9872911862340212187323927)
  ·
    refine ⟨14809367793510318280985891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9872911862340212187323927 14809367793510318280985891)
    ·
      refine ⟨22214051690265477421478837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14809367793510318280985891 22214051690265477421478837)
      ·
        refine ⟨2082567345962388508263641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22214051690265477421478837 2082567345962388508263641)
        ·
          refine ⟨1561925509471791381197731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2082567345962388508263641 1561925509471791381197731)
          ·
            refine ⟨2342888264207687071796597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1561925509471791381197731 2342888264207687071796597)
            ·
              refine ⟨219645774769470662980931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2342888264207687071796597 219645774769470662980931)
              ·
                refine ⟨329468662154205994471397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219645774769470662980931 329468662154205994471397)
                ·
                  refine ⟨61775374153913623963387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 329468662154205994471397 61775374153913623963387)
                  ·
                    rfl

theorem cell21_270691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 4].length) (baseStart_270691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270691 prefixEnd_270691 := by exact prefixLift 270691
  have htrace : WordTrace (prefixWord ++ tailWord_270691) baseStart_270691 baseEnd_270691 := by
    simpa [prefixWord, tailWord_270691, baseEnd_270691] using wordTrace_append hprefix tailTrace_270691
  have hstable : (prefixWord ++ tailWord_270691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270691).length < 2 ^ (prefixWord ++ tailWord_270691).sum := by decide
  have hdescent : baseEnd_270691 < baseStart_270691 := by decide
  rcases family_descends (prefixWord ++ tailWord_270691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270742 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_270742 : Nat := 118140960795 + 270742 * 2 ^ 59
def prefixEnd_270742 : Nat := 4983230072969 + 3 ^ 40 * 270742 * 2
def baseEnd_270742 : Nat := 61787013048748868613283

theorem tailTrace_270742 : CollatzResearch.WordTrace tailWord_270742 prefixEnd_270742 61787013048748868613283 := by
  unfold tailWord_270742
  simp only [CollatzResearch.WordTrace]
  refine ⟨617173249072215493589405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6583181323436965264953653 617173249072215493589405)
  ·
    refine ⟨231439968402080810096027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 617173249072215493589405 231439968402080810096027)
    ·
      refine ⟨347159952603121215144041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231439968402080810096027 347159952603121215144041)
      ·
        refine ⟨260369964452340911358031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347159952603121215144041 260369964452340911358031)
        ·
          refine ⟨390554946678511367037047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260369964452340911358031 390554946678511367037047)
          ·
            refine ⟨585832420017767050555571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390554946678511367037047 585832420017767050555571)
            ·
              refine ⟨878748630026650575833357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585832420017767050555571 878748630026650575833357)
              ·
                refine ⟨329530736259993965937509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 878748630026650575833357 329530736259993965937509)
                ·
                  refine ⟨61787013048748868613283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 329530736259993965937509 61787013048748868613283)
                  ·
                    rfl

theorem cell21_270742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_270742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270742 prefixEnd_270742 := by exact prefixLift 270742
  have htrace : WordTrace (prefixWord ++ tailWord_270742) baseStart_270742 baseEnd_270742 := by
    simpa [prefixWord, tailWord_270742, baseEnd_270742] using wordTrace_append hprefix tailTrace_270742
  have hstable : (prefixWord ++ tailWord_270742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270742).length < 2 ^ (prefixWord ++ tailWord_270742).sum := by decide
  have hdescent : baseEnd_270742 < baseStart_270742 := by decide
  rcases family_descends (prefixWord ++ tailWord_270742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270829 : List Nat := [1, 5, 1, 3, 1, 1, 1, 5, 3]
def baseStart_270829 : Nat := 118140960795 + 270829 * 2 ^ 59
def prefixEnd_270829 : Nat := 4983230072969 + 3 ^ 40 * 270829 * 2
def baseEnd_270829 : Nat := 61806867634056050663105

theorem tailTrace_270829 : CollatzResearch.WordTrace tailWord_270829 prefixEnd_270829 61806867634056050663105 := by
  unfold tailWord_270829
  simp only [CollatzResearch.WordTrace]
  refine ⟨9877945135840261755847541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6585296757226841170565027 9877945135840261755847541)
  ·
    refine ⟨926057356485024539610707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9877945135840261755847541 926057356485024539610707)
    ·
      refine ⟨1389086034727536809416061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 926057356485024539610707 1389086034727536809416061)
      ·
        refine ⟨520907263022826303531023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1389086034727536809416061 520907263022826303531023)
        ·
          refine ⟨781360894534239455296535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520907263022826303531023 781360894534239455296535)
          ·
            refine ⟨1172041341801359182944803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781360894534239455296535 1172041341801359182944803)
            ·
              refine ⟨1758062012702038774417205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172041341801359182944803 1758062012702038774417205)
              ·
                refine ⟨164818313690816135101613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1758062012702038774417205 164818313690816135101613)
                ·
                  refine ⟨61806867634056050663105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164818313690816135101613 61806867634056050663105)
                  ·
                    rfl

theorem cell21_270829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_270829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270829 prefixEnd_270829 := by exact prefixLift 270829
  have htrace : WordTrace (prefixWord ++ tailWord_270829) baseStart_270829 baseEnd_270829 := by
    simpa [prefixWord, tailWord_270829, baseEnd_270829] using wordTrace_append hprefix tailTrace_270829
  have hstable : (prefixWord ++ tailWord_270829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270829).length < 2 ^ (prefixWord ++ tailWord_270829).sum := by decide
  have hdescent : baseEnd_270829 < baseStart_270829 := by decide
  rcases family_descends (prefixWord ++ tailWord_270829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270885 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 6]
def baseStart_270885 : Nat := 118140960795 + 270885 * 2 ^ 59
def prefixEnd_270885 : Nat := 4983230072969 + 3 ^ 40 * 270885 * 2
def baseEnd_270885 : Nat := 61819647597012397729657

theorem tailTrace_270885 : CollatzResearch.WordTrace tailWord_270885 prefixEnd_270885 61819647597012397729657 := by
  unfold tailWord_270885
  simp only [CollatzResearch.WordTrace]
  refine ⟨9879987623637383319886109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6586658415758255546590739 9879987623637383319886109)
  ·
    refine ⟨3704995358864018744957291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9879987623637383319886109 3704995358864018744957291)
    ·
      refine ⟨5557493038296028117435937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3704995358864018744957291 5557493038296028117435937)
      ·
        refine ⟨4168119778722021088076953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5557493038296028117435937 4168119778722021088076953)
        ·
          refine ⟨3126089834041515816057715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4168119778722021088076953 3126089834041515816057715)
          ·
            refine ⟨4689134751062273724086573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3126089834041515816057715 4689134751062273724086573)
            ·
              refine ⟨1758425531648352646532465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4689134751062273724086573 1758425531648352646532465)
              ·
                refine ⟨1318819148736264484899349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1758425531648352646532465 1318819148736264484899349)
                ·
                  refine ⟨61819647597012397729657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1318819148736264484899349 61819647597012397729657)
                  ·
                    rfl

theorem cell21_270885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 6].length) (baseStart_270885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270885 prefixEnd_270885 := by exact prefixLift 270885
  have htrace : WordTrace (prefixWord ++ tailWord_270885) baseStart_270885 baseEnd_270885 := by
    simpa [prefixWord, tailWord_270885, baseEnd_270885] using wordTrace_append hprefix tailTrace_270885
  have hstable : (prefixWord ++ tailWord_270885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270885).length < 2 ^ (prefixWord ++ tailWord_270885).sum := by decide
  have hdescent : baseEnd_270885 < baseStart_270885 := by decide
  rcases family_descends (prefixWord ++ tailWord_270885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270905 : List Nat := [1, 2, 1, 5, 1, 1, 5, 2, 3]
def baseStart_270905 : Nat := 118140960795 + 270905 * 2 ^ 59
def prefixEnd_270905 : Nat := 4983230072969 + 3 ^ 40 * 270905 * 2
def baseEnd_270905 : Nat := 61824211869496807396283

theorem tailTrace_270905 : CollatzResearch.WordTrace tailWord_270905 prefixEnd_270905 61824211869496807396283 := by
  unfold tailWord_270905
  simp only [CollatzResearch.WordTrace]
  refine ⟨9880717083564926735614169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6587144722376617823742779 9880717083564926735614169)
  ·
    refine ⟨7410537812673695051710627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9880717083564926735614169 7410537812673695051710627)
    ·
      refine ⟨11115806719010542577565941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7410537812673695051710627 11115806719010542577565941)
      ·
        refine ⟨1042106879907238366646807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11115806719010542577565941 1042106879907238366646807)
        ·
          refine ⟨1563160319860857549970211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042106879907238366646807 1563160319860857549970211)
          ·
            refine ⟨2344740479791286324955317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563160319860857549970211 2344740479791286324955317)
            ·
              refine ⟨219819419980433092964561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2344740479791286324955317 219819419980433092964561)
              ·
                refine ⟨164864564985324819723421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219819419980433092964561 164864564985324819723421)
                ·
                  refine ⟨61824211869496807396283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164864564985324819723421 61824211869496807396283)
                  ·
                    rfl

theorem cell21_270905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 3].length) (baseStart_270905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270905 prefixEnd_270905 := by exact prefixLift 270905
  have htrace : WordTrace (prefixWord ++ tailWord_270905) baseStart_270905 baseEnd_270905 := by
    simpa [prefixWord, tailWord_270905, baseEnd_270905] using wordTrace_append hprefix tailTrace_270905
  have hstable : (prefixWord ++ tailWord_270905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270905).length < 2 ^ (prefixWord ++ tailWord_270905).sum := by decide
  have hdescent : baseEnd_270905 < baseStart_270905 := by decide
  rcases family_descends (prefixWord ++ tailWord_270905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270919 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 4]
def baseStart_270919 : Nat := 118140960795 + 270919 * 2 ^ 59
def prefixEnd_270919 : Nat := 4983230072969 + 3 ^ 40 * 270919 * 2
def baseEnd_270919 : Nat := 61827406860235894162921

theorem tailTrace_270919 : CollatzResearch.WordTrace tailWord_270919 prefixEnd_270919 61827406860235894162921 := by
  unfold tailWord_270919
  simp only [CollatzResearch.WordTrace]
  refine ⟨9881227705514207126623811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6587485137009471417749207 9881227705514207126623811)
  ·
    refine ⟨14821841558271310689935717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9881227705514207126623811 14821841558271310689935717)
    ·
      refine ⟨2779095292175870754362947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14821841558271310689935717 2779095292175870754362947)
      ·
        refine ⟨4168642938263806131544421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2779095292175870754362947 4168642938263806131544421)
        ·
          refine ⟨781620550924463649664579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4168642938263806131544421 781620550924463649664579)
          ·
            refine ⟨1172430826386695474496869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781620550924463649664579 1172430826386695474496869)
            ·
              refine ⟨219830779947505401468163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1172430826386695474496869 219830779947505401468163)
              ·
                refine ⟨329746169921258102202245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219830779947505401468163 329746169921258102202245)
                ·
                  refine ⟨61827406860235894162921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 329746169921258102202245 61827406860235894162921)
                  ·
                    rfl

theorem cell21_270919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 4].length) (baseStart_270919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270919 prefixEnd_270919 := by exact prefixLift 270919
  have htrace : WordTrace (prefixWord ++ tailWord_270919) baseStart_270919 baseEnd_270919 := by
    simpa [prefixWord, tailWord_270919, baseEnd_270919] using wordTrace_append hprefix tailTrace_270919
  have hstable : (prefixWord ++ tailWord_270919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270919).length < 2 ^ (prefixWord ++ tailWord_270919).sum := by decide
  have hdescent : baseEnd_270919 < baseStart_270919 := by decide
  rcases family_descends (prefixWord ++ tailWord_270919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_270975 : List Nat := [1, 1, 2, 2, 1, 1, 1, 12]
def baseStart_270975 : Nat := 118140960795 + 270975 * 2 ^ 59
def prefixEnd_270975 : Nat := 4983230072969 + 3 ^ 40 * 270975 * 2
def baseEnd_270975 : Nat := 20613395607730747076491

theorem tailTrace_270975 : CollatzResearch.WordTrace tailWord_270975 prefixEnd_270975 20613395607730747076491 := by
  unfold tailWord_270975
  simp only [CollatzResearch.WordTrace]
  refine ⟨9883270193311328690662379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6588846795540885793774919 9883270193311328690662379)
  ·
    refine ⟨14824905289966993035993569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9883270193311328690662379 14824905289966993035993569)
    ·
      refine ⟨11118678967475244776995177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14824905289966993035993569 11118678967475244776995177)
      ·
        refine ⟨8339009225606433582746383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11118678967475244776995177 8339009225606433582746383)
        ·
          refine ⟨12508513838409650374119575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8339009225606433582746383 12508513838409650374119575)
          ·
            refine ⟨18762770757614475561179363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12508513838409650374119575 18762770757614475561179363)
            ·
              refine ⟨28144156136421713341769045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18762770757614475561179363 28144156136421713341769045)
              ·
                refine ⟨20613395607730747076491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 28144156136421713341769045 20613395607730747076491)
                ·
                  rfl

theorem cell21_270975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 12].length) (baseStart_270975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_270975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_270975 prefixEnd_270975 := by exact prefixLift 270975
  have htrace : WordTrace (prefixWord ++ tailWord_270975) baseStart_270975 baseEnd_270975 := by
    simpa [prefixWord, tailWord_270975, baseEnd_270975] using wordTrace_append hprefix tailTrace_270975
  have hstable : (prefixWord ++ tailWord_270975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_270975).length < 2 ^ (prefixWord ++ tailWord_270975).sum := by decide
  have hdescent : baseEnd_270975 < baseStart_270975 := by decide
  rcases family_descends (prefixWord ++ tailWord_270975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271023 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 5]
def baseStart_271023 : Nat := 118140960795 + 271023 * 2 ^ 59
def prefixEnd_271023 : Nat := 4983230072969 + 3 ^ 40 * 271023 * 2
def baseEnd_271023 : Nat := 61851141077154824429375

theorem tailTrace_271023 : CollatzResearch.WordTrace tailWord_271023 prefixEnd_271023 61851141077154824429375 := by
  unfold tailWord_271023
  simp only [CollatzResearch.WordTrace]
  refine ⟨9885020897137432888409723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6590013931424955258939815 9885020897137432888409723)
  ·
    refine ⟨14827531345706149332614585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9885020897137432888409723 14827531345706149332614585)
    ·
      refine ⟨11120648509279611999460939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14827531345706149332614585 11120648509279611999460939)
      ·
        refine ⟨16680972763919417999191409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11120648509279611999460939 16680972763919417999191409)
        ·
          refine ⟨12510729572939563499393557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16680972763919417999191409 12510729572939563499393557)
          ·
            refine ⟨586440448731542039034073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 12510729572939563499393557 586440448731542039034073)
            ·
              refine ⟨439830336548656529275555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586440448731542039034073 439830336548656529275555)
              ·
                refine ⟨659745504822984793913333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439830336548656529275555 659745504822984793913333)
                ·
                  refine ⟨61851141077154824429375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 659745504822984793913333 61851141077154824429375)
                  ·
                    rfl

theorem cell21_271023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 5].length) (baseStart_271023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271023 prefixEnd_271023 := by exact prefixLift 271023
  have htrace : WordTrace (prefixWord ++ tailWord_271023) baseStart_271023 baseEnd_271023 := by
    simpa [prefixWord, tailWord_271023, baseEnd_271023] using wordTrace_append hprefix tailTrace_271023
  have hstable : (prefixWord ++ tailWord_271023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271023).length < 2 ^ (prefixWord ++ tailWord_271023).sum := by decide
  have hdescent : baseEnd_271023 < baseStart_271023 := by decide
  rcases family_descends (prefixWord ++ tailWord_271023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271127 : List Nat := [1, 1, 3, 4, 12]
def baseStart_271127 : Nat := 118140960795 + 271127 * 2 ^ 59
def prefixEnd_271127 : Nat := 4983230072969 + 3 ^ 40 * 271127 * 2
def baseEnd_271127 : Nat := 763887349309552527109

theorem tailTrace_271127 : CollatzResearch.WordTrace tailWord_271127 prefixEnd_271127 763887349309552527109 := by
  unfold tailWord_271127
  simp only [CollatzResearch.WordTrace]
  refine ⟨9888814088760658650195635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6592542725840439100130423 9888814088760658650195635)
  ·
    refine ⟨14833221133140987975293453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9888814088760658650195635 14833221133140987975293453)
    ·
      refine ⟨5562457924927870490735045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14833221133140987975293453 5562457924927870490735045)
      ·
        refine ⟨1042960860923975717012821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5562457924927870490735045 1042960860923975717012821)
        ·
          refine ⟨763887349309552527109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 1042960860923975717012821 763887349309552527109)
          ·
            rfl

theorem cell21_271127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 12].length) (baseStart_271127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271127 prefixEnd_271127 := by exact prefixLift 271127
  have htrace : WordTrace (prefixWord ++ tailWord_271127) baseStart_271127 baseEnd_271127 := by
    simpa [prefixWord, tailWord_271127, baseEnd_271127] using wordTrace_append hprefix tailTrace_271127
  have hstable : (prefixWord ++ tailWord_271127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271127).length < 2 ^ (prefixWord ++ tailWord_271127).sum := by decide
  have hdescent : baseEnd_271127 < baseStart_271127 := by decide
  rcases family_descends (prefixWord ++ tailWord_271127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271130 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_271130 : Nat := 118140960795 + 271130 * 2 ^ 59
def prefixEnd_271130 : Nat := 4983230072969 + 3 ^ 40 * 271130 * 2
def baseEnd_271130 : Nat := 61875559934946416145823

theorem tailTrace_271130 : CollatzResearch.WordTrace tailWord_271130 prefixEnd_271130 61875559934946416145823 := by
  unfold tailWord_271130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2472230876937447540638711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6592615671833193441703229 2472230876937447540638711)
  ·
    refine ⟨3708346315406171310958067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2472230876937447540638711 3708346315406171310958067)
    ·
      refine ⟨5562519473109256966437101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3708346315406171310958067 5562519473109256966437101)
      ·
        refine ⟨2085944802415971362413913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5562519473109256966437101 2085944802415971362413913)
        ·
          refine ⟨1564458601811978521810435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2085944802415971362413913 1564458601811978521810435)
          ·
            refine ⟨2346687902717967782715653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564458601811978521810435 2346687902717967782715653)
            ·
              refine ⟨440003981759618959259185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2346687902717967782715653 440003981759618959259185)
              ·
                refine ⟨330002986319714219444389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440003981759618959259185 330002986319714219444389)
                ·
                  refine ⟨61875559934946416145823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 330002986319714219444389 61875559934946416145823)
                  ·
                    rfl

theorem cell21_271130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_271130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271130 prefixEnd_271130 := by exact prefixLift 271130
  have htrace : WordTrace (prefixWord ++ tailWord_271130) baseStart_271130 baseEnd_271130 := by
    simpa [prefixWord, tailWord_271130, baseEnd_271130] using wordTrace_append hprefix tailTrace_271130
  have hstable : (prefixWord ++ tailWord_271130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271130).length < 2 ^ (prefixWord ++ tailWord_271130).sum := by decide
  have hdescent : baseEnd_271130 < baseStart_271130 := by decide
  rcases family_descends (prefixWord ++ tailWord_271130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271181 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 4]
def baseStart_271181 : Nat := 118140960795 + 271181 * 2 ^ 59
def prefixEnd_271181 : Nat := 4983230072969 + 3 ^ 40 * 271181 * 2
def baseEnd_271181 : Nat := 61887198829781660795719

theorem tailTrace_271181 : CollatzResearch.WordTrace tailWord_271181 prefixEnd_271181 61887198829781660795719 := by
  unfold tailWord_271181
  simp only [CollatzResearch.WordTrace]
  refine ⟨9890783630565025872661397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6593855753710017248440931 9890783630565025872661397)
  ·
    refine ⟨463630482682735587781003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9890783630565025872661397 463630482682735587781003)
    ·
      refine ⟨695445724024103381671505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 463630482682735587781003 695445724024103381671505)
      ·
        refine ⟨521584293018077536253629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 695445724024103381671505 521584293018077536253629)
        ·
          refine ⟨195594109881779076095111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 521584293018077536253629 195594109881779076095111)
          ·
            refine ⟨293391164822668614142667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195594109881779076095111 293391164822668614142667)
            ·
              refine ⟨440086747234002921214001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293391164822668614142667 440086747234002921214001)
              ·
                refine ⟨330065060425502190910501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440086747234002921214001 330065060425502190910501)
                ·
                  refine ⟨61887198829781660795719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 330065060425502190910501 61887198829781660795719)
                  ·
                    rfl

theorem cell21_271181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_271181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271181 prefixEnd_271181 := by exact prefixLift 271181
  have htrace : WordTrace (prefixWord ++ tailWord_271181) baseStart_271181 baseEnd_271181 := by
    simpa [prefixWord, tailWord_271181, baseEnd_271181] using wordTrace_append hprefix tailTrace_271181
  have hstable : (prefixWord ++ tailWord_271181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271181).length < 2 ^ (prefixWord ++ tailWord_271181).sum := by decide
  have hdescent : baseEnd_271181 < baseStart_271181 := by decide
  rcases family_descends (prefixWord ++ tailWord_271181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271189 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 6]
def baseStart_271189 : Nat := 118140960795 + 271189 * 2 ^ 59
def prefixEnd_271189 : Nat := 4983230072969 + 3 ^ 40 * 271189 * 2
def baseEnd_271189 : Nat := 61889024538775424662369

theorem tailTrace_271189 : CollatzResearch.WordTrace tailWord_271189 prefixEnd_271189 61889024538775424662369 := by
  unfold tailWord_271189
  simp only [CollatzResearch.WordTrace]
  refine ⟨9891075414536043238952621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6594050276357362159301747 9891075414536043238952621)
  ·
    refine ⟨3709153280451016214607233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9891075414536043238952621 3709153280451016214607233)
    ·
      refine ⟨2781864960338262160955425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3709153280451016214607233 2781864960338262160955425)
      ·
        refine ⟨2086398720253696620716569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2781864960338262160955425 2086398720253696620716569)
        ·
          refine ⟨1564799040190272465537427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2086398720253696620716569 1564799040190272465537427)
          ·
            refine ⟨2347198560285408698306141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564799040190272465537427 2347198560285408698306141)
            ·
              refine ⟨880199460107028261864803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2347198560285408698306141 880199460107028261864803)
              ·
                refine ⟨1320299190160542392797205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880199460107028261864803 1320299190160542392797205)
                ·
                  refine ⟨61889024538775424662369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1320299190160542392797205 61889024538775424662369)
                  ·
                    rfl

theorem cell21_271189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_271189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271189 prefixEnd_271189 := by exact prefixLift 271189
  have htrace : WordTrace (prefixWord ++ tailWord_271189) baseStart_271189 baseEnd_271189 := by
    simpa [prefixWord, tailWord_271189, baseEnd_271189] using wordTrace_append hprefix tailTrace_271189
  have hstable : (prefixWord ++ tailWord_271189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271189).length < 2 ^ (prefixWord ++ tailWord_271189).sum := by decide
  have hdescent : baseEnd_271189 < baseStart_271189 := by decide
  rcases family_descends (prefixWord ++ tailWord_271189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271248 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 10]
def baseStart_271248 : Nat := 118140960795 + 271248 * 2 ^ 59
def prefixEnd_271248 : Nat := 4983230072969 + 3 ^ 40 * 271248 * 2
def baseEnd_271248 : Nat := 61902489142604433178915

theorem tailTrace_271248 : CollatzResearch.WordTrace tailWord_271248 prefixEnd_271248 61902489142604433178915 := by
  unfold tailWord_271248
  simp only [CollatzResearch.WordTrace]
  refine ⟨4946613660661148157675199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6595484880881530876900265 4946613660661148157675199)
  ·
    refine ⟨7419920490991722236512799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4946613660661148157675199 7419920490991722236512799)
    ·
      refine ⟨11129880736487583354769199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7419920490991722236512799 11129880736487583354769199)
      ·
        refine ⟨16694821104731375032153799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11129880736487583354769199 16694821104731375032153799)
        ·
          refine ⟨25042231657097062548230699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16694821104731375032153799 25042231657097062548230699)
          ·
            refine ⟨37563347485645593822346049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25042231657097062548230699 37563347485645593822346049)
            ·
              refine ⟨28172510614234195366759537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37563347485645593822346049 28172510614234195366759537)
              ·
                refine ⟨21129382960675646525069653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28172510614234195366759537 21129382960675646525069653)
                ·
                  refine ⟨61902489142604433178915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 21129382960675646525069653 61902489142604433178915)
                  ·
                    rfl

theorem cell21_271248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_271248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271248 prefixEnd_271248 := by exact prefixLift 271248
  have htrace : WordTrace (prefixWord ++ tailWord_271248) baseStart_271248 baseEnd_271248 := by
    simpa [prefixWord, tailWord_271248, baseEnd_271248] using wordTrace_append hprefix tailTrace_271248
  have hstable : (prefixWord ++ tailWord_271248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271248).length < 2 ^ (prefixWord ++ tailWord_271248).sum := by decide
  have hdescent : baseEnd_271248 < baseStart_271248 := by decide
  rcases family_descends (prefixWord ++ tailWord_271248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271254 : List Nat := [5, 3, 1, 1, 1, 1, 1, 8]
def baseStart_271254 : Nat := 118140960795 + 271254 * 2 ^ 59
def prefixEnd_271254 : Nat := 4983230072969 + 3 ^ 40 * 271254 * 2
def baseEnd_271254 : Nat := 20634619474783252026301

theorem tailTrace_271254 : CollatzResearch.WordTrace tailWord_271254 prefixEnd_271254 20634619474783252026301 := by
  unfold tailWord_271254
  simp only [CollatzResearch.WordTrace]
  refine ⟨618340384956284958754301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6595630772867039560045877 618340384956284958754301)
  ·
    refine ⟨231877644358606859532863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 618340384956284958754301 231877644358606859532863)
    ·
      refine ⟨347816466537910289299295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231877644358606859532863 347816466537910289299295)
      ·
        refine ⟨521724699806865433948943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347816466537910289299295 521724699806865433948943)
        ·
          refine ⟨782587049710298150923415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521724699806865433948943 782587049710298150923415)
          ·
            refine ⟨1173880574565447226385123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782587049710298150923415 1173880574565447226385123)
            ·
              refine ⟨1760820861848170839577685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173880574565447226385123 1760820861848170839577685)
              ·
                refine ⟨20634619474783252026301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1760820861848170839577685 20634619474783252026301)
                ·
                  rfl

theorem cell21_271254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_271254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271254 prefixEnd_271254 := by exact prefixLift 271254
  have htrace : WordTrace (prefixWord ++ tailWord_271254) baseStart_271254 baseEnd_271254 := by
    simpa [prefixWord, tailWord_271254, baseEnd_271254] using wordTrace_append hprefix tailTrace_271254
  have hstable : (prefixWord ++ tailWord_271254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271254).length < 2 ^ (prefixWord ++ tailWord_271254).sum := by decide
  have hdescent : baseEnd_271254 < baseStart_271254 := by decide
  rcases family_descends (prefixWord ++ tailWord_271254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271327 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 5]
def baseStart_271327 : Nat := 118140960795 + 271327 * 2 ^ 59
def prefixEnd_271327 : Nat := 4983230072969 + 3 ^ 40 * 271327 * 2
def baseEnd_271327 : Nat := 61920518018917851362087

theorem tailTrace_271327 : CollatzResearch.WordTrace tailWord_271327 prefixEnd_271327 61920518018917851362087 := by
  unfold tailWord_271327
  simp only [CollatzResearch.WordTrace]
  refine ⟨9896108688036092807476235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6597405792024061871650823 9896108688036092807476235)
  ·
    refine ⟨14844163032054139211214353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9896108688036092807476235 14844163032054139211214353)
    ·
      refine ⟨11133122274040604408410765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14844163032054139211214353 11133122274040604408410765)
      ·
        refine ⟨4174920852765226653154037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11133122274040604408410765 4174920852765226653154037)
        ·
          refine ⟨391398829946739998733191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4174920852765226653154037 391398829946739998733191)
          ·
            refine ⟨587098244920109998099787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391398829946739998733191 587098244920109998099787)
            ·
              refine ⟨880647367380164997149681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587098244920109998099787 880647367380164997149681)
              ·
                refine ⟨660485525535123747862261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880647367380164997149681 660485525535123747862261)
                ·
                  refine ⟨61920518018917851362087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 660485525535123747862261 61920518018917851362087)
                  ·
                    rfl

theorem cell21_271327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 5].length) (baseStart_271327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271327 prefixEnd_271327 := by exact prefixLift 271327
  have htrace : WordTrace (prefixWord ++ tailWord_271327) baseStart_271327 baseEnd_271327 := by
    simpa [prefixWord, tailWord_271327, baseEnd_271327] using wordTrace_append hprefix tailTrace_271327
  have hstable : (prefixWord ++ tailWord_271327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271327).length < 2 ^ (prefixWord ++ tailWord_271327).sum := by decide
  have hdescent : baseEnd_271327 < baseStart_271327 := by decide
  rcases family_descends (prefixWord ++ tailWord_271327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271330 : List Nat := [3, 3, 3, 1, 1, 2, 3, 5]
def baseStart_271330 : Nat := 118140960795 + 271330 * 2 ^ 59
def prefixEnd_271330 : Nat := 4983230072969 + 3 ^ 40 * 271330 * 2
def baseEnd_271330 : Nat := 20640400886596837604027

theorem tailTrace_271330 : CollatzResearch.WordTrace tailWord_271330 prefixEnd_271330 20640400886596837604027 := by
  unfold tailWord_271330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474054526756306079958861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6597478738016816213223629 2474054526756306079958861)
  ·
    refine ⟨927770447533614779984573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2474054526756306079958861 927770447533614779984573)
    ·
      refine ⟨347913917825105542494215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 927770447533614779984573 347913917825105542494215)
      ·
        refine ⟨521870876737658313741323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347913917825105542494215 521870876737658313741323)
        ·
          refine ⟨782806315106487470611985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521870876737658313741323 782806315106487470611985)
          ·
            refine ⟨587104736329865602958989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 782806315106487470611985 587104736329865602958989)
            ·
              refine ⟨220164276123699601109621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 587104736329865602958989 220164276123699601109621)
              ·
                refine ⟨20640400886596837604027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 220164276123699601109621 20640400886596837604027)
                ·
                  rfl

theorem cell21_271330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_271330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271330 prefixEnd_271330 := by exact prefixLift 271330
  have htrace : WordTrace (prefixWord ++ tailWord_271330) baseStart_271330 baseEnd_271330 := by
    simpa [prefixWord, tailWord_271330, baseEnd_271330] using wordTrace_append hprefix tailTrace_271330
  have hstable : (prefixWord ++ tailWord_271330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271330).length < 2 ^ (prefixWord ++ tailWord_271330).sum := by decide
  have hdescent : baseEnd_271330 < baseStart_271330 := by decide
  rcases family_descends (prefixWord ++ tailWord_271330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271386 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_271386 : Nat := 118140960795 + 271386 * 2 ^ 59
def prefixEnd_271386 : Nat := 4983230072969 + 3 ^ 40 * 271386 * 2
def baseEnd_271386 : Nat := 61933982622746859878633

theorem tailTrace_271386 : CollatzResearch.WordTrace tailWord_271386 prefixEnd_271386 61933982622746859878633 := by
  unfold tailWord_271386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474565148705586470968503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6598840396548230589249341 2474565148705586470968503)
  ·
    refine ⟨3711847723058379706452755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2474565148705586470968503 3711847723058379706452755)
    ·
      refine ⟨5567771584587569559679133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3711847723058379706452755 5567771584587569559679133)
      ·
        refine ⟨2087914344220338584879675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5567771584587569559679133 2087914344220338584879675)
        ·
          refine ⟨3131871516330507877319513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087914344220338584879675 3131871516330507877319513)
          ·
            refine ⟨2348903637247880907989635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3131871516330507877319513 2348903637247880907989635)
            ·
              refine ⟨3523355455871821361984453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348903637247880907989635 3523355455871821361984453)
              ·
                refine ⟨660629147975966505372085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3523355455871821361984453 660629147975966505372085)
                ·
                  refine ⟨61933982622746859878633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 660629147975966505372085 61933982622746859878633)
                  ·
                    rfl

theorem cell21_271386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_271386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271386 prefixEnd_271386 := by exact prefixLift 271386
  have htrace : WordTrace (prefixWord ++ tailWord_271386) baseStart_271386 baseEnd_271386 := by
    simpa [prefixWord, tailWord_271386, baseEnd_271386] using wordTrace_append hprefix tailTrace_271386
  have hstable : (prefixWord ++ tailWord_271386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271386).length < 2 ^ (prefixWord ++ tailWord_271386).sum := by decide
  have hdescent : baseEnd_271386 < baseStart_271386 := by decide
  rcases family_descends (prefixWord ++ tailWord_271386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271417 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 6]
def baseStart_271417 : Nat := 118140960795 + 271417 * 2 ^ 59
def prefixEnd_271417 : Nat := 4983230072969 + 3 ^ 40 * 271417 * 2
def baseEnd_271417 : Nat := 61941057245097694861903

theorem tailTrace_271417 : CollatzResearch.WordTrace tailWord_271417 prefixEnd_271417 61941057245097694861903 := by
  unfold tailWord_271417
  simp only [CollatzResearch.WordTrace]
  refine ⟨9899391257710038178252505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6599594171806692118835003 9899391257710038178252505)
  ·
    refine ⟨7424543443282528633689379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9899391257710038178252505 7424543443282528633689379)
    ·
      refine ⟨11136815164923792950534069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7424543443282528633689379 11136815164923792950534069)
      ·
        refine ⟨1044076421711605589112569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11136815164923792950534069 1044076421711605589112569)
        ·
          refine ⟨783057316283704191834427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1044076421711605589112569 783057316283704191834427)
          ·
            refine ⟨1174585974425556287751641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783057316283704191834427 1174585974425556287751641)
            ·
              refine ⟨880939480819167215813731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174585974425556287751641 880939480819167215813731)
              ·
                refine ⟨1321409221228750823720597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880939480819167215813731 1321409221228750823720597)
                ·
                  refine ⟨61941057245097694861903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1321409221228750823720597 61941057245097694861903)
                  ·
                    rfl

theorem cell21_271417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_271417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271417 prefixEnd_271417 := by exact prefixLift 271417
  have htrace : WordTrace (prefixWord ++ tailWord_271417) baseStart_271417 baseEnd_271417 := by
    simpa [prefixWord, tailWord_271417, baseEnd_271417] using wordTrace_append hprefix tailTrace_271417
  have hstable : (prefixWord ++ tailWord_271417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271417).length < 2 ^ (prefixWord ++ tailWord_271417).sum := by decide
  have hdescent : baseEnd_271417 < baseStart_271417 := by decide
  rcases family_descends (prefixWord ++ tailWord_271417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271431 : List Nat := [1, 1, 4, 1, 3, 2, 1, 8]
def baseStart_271431 : Nat := 118140960795 + 271431 * 2 ^ 59
def prefixEnd_271431 : Nat := 4983230072969 + 3 ^ 40 * 271431 * 2
def baseEnd_271431 : Nat := 20648084078612260542847

theorem tailTrace_271431 : CollatzResearch.WordTrace tailWord_271431 prefixEnd_271431 20648084078612260542847 := by
  unfold tailWord_271431
  simp only [CollatzResearch.WordTrace]
  refine ⟨9899901879659318569262147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6599934586439545712841431 9899901879659318569262147)
  ·
    refine ⟨14849852819488977853893221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9899901879659318569262147 14849852819488977853893221)
    ·
      refine ⟨2784347403654183347604979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14849852819488977853893221 2784347403654183347604979)
      ·
        refine ⟨4176521105481275021407469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2784347403654183347604979 4176521105481275021407469)
        ·
          refine ⟨1566195414555478133027801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4176521105481275021407469 1566195414555478133027801)
          ·
            refine ⟨1174646560916608599770851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1566195414555478133027801 1174646560916608599770851)
            ·
              refine ⟨1761969841374912899656277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174646560916608599770851 1761969841374912899656277)
              ·
                refine ⟨20648084078612260542847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1761969841374912899656277 20648084078612260542847)
                ·
                  rfl

theorem cell21_271431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 8].length) (baseStart_271431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271431 prefixEnd_271431 := by exact prefixLift 271431
  have htrace : WordTrace (prefixWord ++ tailWord_271431) baseStart_271431 baseEnd_271431 := by
    simpa [prefixWord, tailWord_271431, baseEnd_271431] using wordTrace_append hprefix tailTrace_271431
  have hstable : (prefixWord ++ tailWord_271431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271431).length < 2 ^ (prefixWord ++ tailWord_271431).sum := by decide
  have hdescent : baseEnd_271431 < baseStart_271431 := by decide
  rcases family_descends (prefixWord ++ tailWord_271431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271434 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 4]
def baseStart_271434 : Nat := 118140960795 + 271434 * 2 ^ 59
def prefixEnd_271434 : Nat := 4983230072969 + 3 ^ 40 * 271434 * 2
def baseEnd_271434 : Nat := 61944936876709443078535

theorem tailTrace_271434 : CollatzResearch.WordTrace tailWord_271434 prefixEnd_271434 61944936876709443078535 := by
  unfold tailWord_271434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2475002824662112520405339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6600007532432300054414237 2475002824662112520405339)
  ·
    refine ⟨3712504236993168780608009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2475002824662112520405339 3712504236993168780608009)
    ·
      refine ⟨2784378177744876585456007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3712504236993168780608009 2784378177744876585456007)
      ·
        refine ⟨4176567266617314878184011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2784378177744876585456007 4176567266617314878184011)
        ·
          refine ⟨6264850899925972317276017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4176567266617314878184011 6264850899925972317276017)
          ·
            refine ⟨4698638174944479237957013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6264850899925972317276017 4698638174944479237957013)
            ·
              refine ⟨220248664450522464279235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4698638174944479237957013 220248664450522464279235)
              ·
                refine ⟨330372996675783696418853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220248664450522464279235 330372996675783696418853)
                ·
                  refine ⟨61944936876709443078535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 330372996675783696418853 61944936876709443078535)
                  ·
                    rfl

theorem cell21_271434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_271434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271434 prefixEnd_271434 := by exact prefixLift 271434
  have htrace : WordTrace (prefixWord ++ tailWord_271434) baseStart_271434 baseEnd_271434 := by
    simpa [prefixWord, tailWord_271434, baseEnd_271434] using wordTrace_append hprefix tailTrace_271434
  have hstable : (prefixWord ++ tailWord_271434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271434).length < 2 ^ (prefixWord ++ tailWord_271434).sum := by decide
  have hdescent : baseEnd_271434 < baseStart_271434 := by decide
  rcases family_descends (prefixWord ++ tailWord_271434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271479 : List Nat := [1, 1, 3, 1, 1, 4, 3, 4, 3]
def baseStart_271479 : Nat := 118140960795 + 271479 * 2 ^ 59
def prefixEnd_271479 : Nat := 4983230072969 + 3 ^ 40 * 271479 * 2
def baseEnd_271479 : Nat := 61955206489799364828443

theorem tailTrace_271479 : CollatzResearch.WordTrace tailWord_271479 prefixEnd_271479 61955206489799364828443 := by
  unfold tailWord_271479
  simp only [CollatzResearch.WordTrace]
  refine ⟨9901652583485422767009491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6601101722323615178006327 9901652583485422767009491)
  ·
    refine ⟨14852478875228134150514237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9901652583485422767009491 14852478875228134150514237)
    ·
      refine ⟨5569679578210550306442839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14852478875228134150514237 5569679578210550306442839)
      ·
        refine ⟨8354519367315825459664259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5569679578210550306442839 8354519367315825459664259)
        ·
          refine ⟨12531779050973738189496389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8354519367315825459664259 12531779050973738189496389)
          ·
            refine ⟨2349708572057575910530573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12531779050973738189496389 2349708572057575910530573)
            ·
              refine ⟨881140714521590966448965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2349708572057575910530573 881140714521590966448965)
              ·
                refine ⟨165213883972798306209181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 881140714521590966448965 165213883972798306209181)
                ·
                  refine ⟨61955206489799364828443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165213883972798306209181 61955206489799364828443)
                  ·
                    rfl

theorem cell21_271479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 3].length) (baseStart_271479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271479 prefixEnd_271479 := by exact prefixLift 271479
  have htrace : WordTrace (prefixWord ++ tailWord_271479) baseStart_271479 baseEnd_271479 := by
    simpa [prefixWord, tailWord_271479, baseEnd_271479] using wordTrace_append hprefix tailTrace_271479
  have hstable : (prefixWord ++ tailWord_271479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271479).length < 2 ^ (prefixWord ++ tailWord_271479).sum := by decide
  have hdescent : baseEnd_271479 < baseStart_271479 := by decide
  rcases family_descends (prefixWord ++ tailWord_271479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271527 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 4]
def baseStart_271527 : Nat := 118140960795 + 271527 * 2 ^ 59
def prefixEnd_271527 : Nat := 4983230072969 + 3 ^ 40 * 271527 * 2
def baseEnd_271527 : Nat := 61966160743761948028345

theorem tailTrace_271527 : CollatzResearch.WordTrace tailWord_271527 prefixEnd_271527 61966160743761948028345 := by
  unfold tailWord_271527
  simp only [CollatzResearch.WordTrace]
  refine ⟨9903403287311526964756835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6602268858207684643171223 9903403287311526964756835)
  ·
    refine ⟨14855104930967290447135253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9903403287311526964756835 14855104930967290447135253)
    ·
      refine ⟨696333043639091739709465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14855104930967290447135253 696333043639091739709465)
      ·
        refine ⟨522249782729318804782099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 696333043639091739709465 522249782729318804782099)
        ·
          refine ⟨783374674093978207173149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522249782729318804782099 783374674093978207173149)
          ·
            refine ⟨293765502785241827689931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 783374674093978207173149 293765502785241827689931)
            ·
              refine ⟨440648254177862741534897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293765502785241827689931 440648254177862741534897)
              ·
                refine ⟨330486190633397056151173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440648254177862741534897 330486190633397056151173)
                ·
                  refine ⟨61966160743761948028345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 330486190633397056151173 61966160743761948028345)
                  ·
                    rfl

theorem cell21_271527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 4].length) (baseStart_271527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271527 prefixEnd_271527 := by exact prefixLift 271527
  have htrace : WordTrace (prefixWord ++ tailWord_271527) baseStart_271527 baseEnd_271527 := by
    simpa [prefixWord, tailWord_271527, baseEnd_271527] using wordTrace_append hprefix tailTrace_271527
  have hstable : (prefixWord ++ tailWord_271527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271527).length < 2 ^ (prefixWord ++ tailWord_271527).sum := by decide
  have hdescent : baseEnd_271527 < baseStart_271527 := by decide
  rcases family_descends (prefixWord ++ tailWord_271527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271538 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 5]
def baseStart_271538 : Nat := 118140960795 + 271538 * 2 ^ 59
def prefixEnd_271538 : Nat := 4983230072969 + 3 ^ 40 * 271538 * 2
def baseEnd_271538 : Nat := 61968671093628373344989

theorem tailTrace_271538 : CollatzResearch.WordTrace tailWord_271538 prefixEnd_271538 61968671093628373344989 := by
  unfold tailWord_271538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2475951122567918960851817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6602536326847783895604845 2475951122567918960851817)
  ·
    refine ⟨1856963341925939220638863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2475951122567918960851817 1856963341925939220638863)
    ·
      refine ⟨2785445012888908830958295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1856963341925939220638863 2785445012888908830958295)
      ·
        refine ⟨4178167519333363246437443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2785445012888908830958295 4178167519333363246437443)
        ·
          refine ⟨6267251279000044869656165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4178167519333363246437443 6267251279000044869656165)
          ·
            refine ⟨1175109614812508413060531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6267251279000044869656165 1175109614812508413060531)
            ·
              refine ⟨1762664422218762619590797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175109614812508413060531 1762664422218762619590797)
              ·
                refine ⟨660999158332035982346549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1762664422218762619590797 660999158332035982346549)
                ·
                  refine ⟨61968671093628373344989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 660999158332035982346549 61968671093628373344989)
                  ·
                    rfl

theorem cell21_271538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_271538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271538 prefixEnd_271538 := by exact prefixLift 271538
  have htrace : WordTrace (prefixWord ++ tailWord_271538) baseStart_271538 baseEnd_271538 := by
    simpa [prefixWord, tailWord_271538, baseEnd_271538] using wordTrace_append hprefix tailTrace_271538
  have hstable : (prefixWord ++ tailWord_271538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271538).length < 2 ^ (prefixWord ++ tailWord_271538).sum := by decide
  have hdescent : baseEnd_271538 < baseStart_271538 := by decide
  rcases family_descends (prefixWord ++ tailWord_271538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271589 : List Nat := [1, 3, 1, 4, 3, 1, 3, 2, 3]
def baseStart_271589 : Nat := 118140960795 + 271589 * 2 ^ 59
def prefixEnd_271589 : Nat := 4983230072969 + 3 ^ 40 * 271589 * 2
def baseEnd_271589 : Nat := 61980309988463617994885

theorem tailTrace_271589 : CollatzResearch.WordTrace tailWord_271589 prefixEnd_271589 61980309988463617994885 := by
  unfold tailWord_271589
  simp only [CollatzResearch.WordTrace]
  refine ⟨9905664613086911553513821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6603776408724607702342547 9905664613086911553513821)
  ·
    refine ⟨3714624229907591832567683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9905664613086911553513821 3714624229907591832567683)
    ·
      refine ⟨5571936344861387748851525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3714624229907591832567683 5571936344861387748851525)
      ·
        refine ⟨1044738064661510202909661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5571936344861387748851525 1044738064661510202909661)
        ·
          refine ⟨391776774248066326091123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1044738064661510202909661 391776774248066326091123)
          ·
            refine ⟨587665161372099489136685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391776774248066326091123 587665161372099489136685)
            ·
              refine ⟨220374435514537308426257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 587665161372099489136685 220374435514537308426257)
              ·
                refine ⟨165280826635902981319693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220374435514537308426257 165280826635902981319693)
                ·
                  refine ⟨61980309988463617994885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165280826635902981319693 61980309988463617994885)
                  ·
                    rfl

theorem cell21_271589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_271589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271589 prefixEnd_271589 := by exact prefixLift 271589
  have htrace : WordTrace (prefixWord ++ tailWord_271589) baseStart_271589 baseEnd_271589 := by
    simpa [prefixWord, tailWord_271589, baseEnd_271589] using wordTrace_append hprefix tailTrace_271589
  have hstable : (prefixWord ++ tailWord_271589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271589).length < 2 ^ (prefixWord ++ tailWord_271589).sum := by decide
  have hdescent : baseEnd_271589 < baseStart_271589 := by decide
  rcases family_descends (prefixWord ++ tailWord_271589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271648 : List Nat := [2, 1, 1, 5, 3, 1, 1, 4, 3]
def baseStart_271648 : Nat := 118140960795 + 271648 * 2 ^ 59
def prefixEnd_271648 : Nat := 4983230072969 + 3 ^ 40 * 271648 * 2
def baseEnd_271648 : Nat := 61993774592292626511431

theorem tailTrace_271648 : CollatzResearch.WordTrace tailWord_271648 prefixEnd_271648 61993774592292626511431 := by
  unfold tailWord_271648
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953908259936582314955799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6605211013248776419941065 4953908259936582314955799)
  ·
    refine ⟨7430862389904873472433699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4953908259936582314955799 7430862389904873472433699)
    ·
      refine ⟨11146293584857310208650549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7430862389904873472433699 11146293584857310208650549)
      ·
        refine ⟨1044965023580372832060989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11146293584857310208650549 1044965023580372832060989)
        ·
          refine ⟨391861883842639812022871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1044965023580372832060989 391861883842639812022871)
          ·
            refine ⟨587792825763959718034307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391861883842639812022871 587792825763959718034307)
            ·
              refine ⟨881689238645939577051461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 587792825763959718034307 881689238645939577051461)
              ·
                refine ⟨165316732246113670697149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 881689238645939577051461 165316732246113670697149)
                ·
                  refine ⟨61993774592292626511431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165316732246113670697149 61993774592292626511431)
                  ·
                    rfl

theorem cell21_271648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 3].length) (baseStart_271648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271648 prefixEnd_271648 := by exact prefixLift 271648
  have htrace : WordTrace (prefixWord ++ tailWord_271648) baseStart_271648 baseEnd_271648 := by
    simpa [prefixWord, tailWord_271648, baseEnd_271648] using wordTrace_append hprefix tailTrace_271648
  have hstable : (prefixWord ++ tailWord_271648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271648).length < 2 ^ (prefixWord ++ tailWord_271648).sum := by decide
  have hdescent : baseEnd_271648 < baseStart_271648 := by decide
  rcases family_descends (prefixWord ++ tailWord_271648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271676 : List Nat := [2, 2, 2, 2, 1, 4, 3, 5]
def baseStart_271676 : Nat := 118140960795 + 271676 * 2 ^ 59
def prefixEnd_271676 : Nat := 4983230072969 + 3 ^ 40 * 271676 * 2
def baseEnd_271676 : Nat := 20666721524590266681569

theorem tailTrace_271676 : CollatzResearch.WordTrace tailWord_271676 prefixEnd_271676 20666721524590266681569 := by
  unfold tailWord_271676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954418881885862705965441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6605891842514483607953921 4954418881885862705965441)
  ·
    refine ⟨3715814161414397029474081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4954418881885862705965441 3715814161414397029474081)
    ·
      refine ⟨2786860621060797772105561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3715814161414397029474081 2786860621060797772105561)
      ·
        refine ⟨2090145465795598329079171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2786860621060797772105561 2090145465795598329079171)
        ·
          refine ⟨3135218198693397493618757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090145465795598329079171 3135218198693397493618757)
          ·
            refine ⟨587853412255012030053517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3135218198693397493618757 587853412255012030053517)
            ·
              refine ⟨220445029595629511270069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 587853412255012030053517 220445029595629511270069)
              ·
                refine ⟨20666721524590266681569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 220445029595629511270069 20666721524590266681569)
                ·
                  rfl

theorem cell21_271676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_271676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271676 prefixEnd_271676 := by exact prefixLift 271676
  have htrace : WordTrace (prefixWord ++ tailWord_271676) baseStart_271676 baseEnd_271676 := by
    simpa [prefixWord, tailWord_271676, baseEnd_271676] using wordTrace_append hprefix tailTrace_271676
  have hstable : (prefixWord ++ tailWord_271676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271676).length < 2 ^ (prefixWord ++ tailWord_271676).sum := by decide
  have hdescent : baseEnd_271676 < baseStart_271676 := by decide
  rcases family_descends (prefixWord ++ tailWord_271676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271693 : List Nat := [1, 6, 1, 3, 1, 1, 8]
def baseStart_271693 : Nat := 118140960795 + 271693 * 2 ^ 59
def prefixEnd_271693 : Nat := 4983230072969 + 3 ^ 40 * 271693 * 2
def baseEnd_271693 : Nat := 6889338245042505362371

theorem tailTrace_271693 : CollatzResearch.WordTrace tailWord_271693 prefixEnd_271693 6889338245042505362371 := by
  unfold tailWord_271693
  simp only [CollatzResearch.WordTrace]
  refine ⟨9909457804710137315299733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6606305203140091543533155 9909457804710137315299733)
  ·
    refine ⟨464505834595787686654675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9909457804710137315299733 464505834595787686654675)
    ·
      refine ⟨696758751893681529982013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 464505834595787686654675 696758751893681529982013)
      ·
        refine ⟨261284531960130573743255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 696758751893681529982013 261284531960130573743255)
        ·
          refine ⟨391926797940195860614883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261284531960130573743255 391926797940195860614883)
          ·
            refine ⟨587890196910293790922325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391926797940195860614883 587890196910293790922325)
            ·
              refine ⟨6889338245042505362371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 587890196910293790922325 6889338245042505362371)
              ·
                rfl

theorem cell21_271693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 8].length) (baseStart_271693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271693 prefixEnd_271693 := by exact prefixLift 271693
  have htrace : WordTrace (prefixWord ++ tailWord_271693) baseStart_271693 baseEnd_271693 := by
    simpa [prefixWord, tailWord_271693, baseEnd_271693] using wordTrace_append hprefix tailTrace_271693
  have hstable : (prefixWord ++ tailWord_271693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271693).length < 2 ^ (prefixWord ++ tailWord_271693).sum := by decide
  have hdescent : baseEnd_271693 < baseStart_271693 := by decide
  rcases family_descends (prefixWord ++ tailWord_271693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271704 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 6]
def baseStart_271704 : Nat := 118140960795 + 271704 * 2 ^ 59
def prefixEnd_271704 : Nat := 4983230072969 + 3 ^ 40 * 271704 * 2
def baseEnd_271704 : Nat := 62006554555248973577983

theorem tailTrace_271704 : CollatzResearch.WordTrace tailWord_271704 prefixEnd_271704 62006554555248973577983 := by
  unfold tailWord_271704
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954929503835143096975083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6606572671780190795966777 4954929503835143096975083)
  ·
    refine ⟨7432394255752714645462625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4954929503835143096975083 7432394255752714645462625)
    ·
      refine ⟨5574295691814535984096969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7432394255752714645462625 5574295691814535984096969)
      ·
        refine ⟨4180721768860901988072727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5574295691814535984096969 4180721768860901988072727)
        ·
          refine ⟨6271082653291352982109091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4180721768860901988072727 6271082653291352982109091)
          ·
            refine ⟨9406623979937029473163637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6271082653291352982109091 9406623979937029473163637)
            ·
              refine ⟨881870998119096513109091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9406623979937029473163637 881870998119096513109091)
              ·
                refine ⟨1322806497178644769663637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881870998119096513109091 1322806497178644769663637)
                ·
                  refine ⟨62006554555248973577983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1322806497178644769663637 62006554555248973577983)
                  ·
                    rfl

theorem cell21_271704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_271704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271704 prefixEnd_271704 := by exact prefixLift 271704
  have htrace : WordTrace (prefixWord ++ tailWord_271704) baseStart_271704 baseEnd_271704 := by
    simpa [prefixWord, tailWord_271704, baseEnd_271704] using wordTrace_append hprefix tailTrace_271704
  have hstable : (prefixWord ++ tailWord_271704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271704).length < 2 ^ (prefixWord ++ tailWord_271704).sum := by decide
  have hdescent : baseEnd_271704 < baseStart_271704 := by decide
  rcases family_descends (prefixWord ++ tailWord_271704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271749 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 7]
def baseStart_271749 : Nat := 118140960795 + 271749 * 2 ^ 59
def prefixEnd_271749 : Nat := 4983230072969 + 3 ^ 40 * 271749 * 2
def baseEnd_271749 : Nat := 62016824168338895327891

theorem tailTrace_271749 : CollatzResearch.WordTrace tailWord_271749 prefixEnd_271749 62016824168338895327891 := by
  unfold tailWord_271749
  simp only [CollatzResearch.WordTrace]
  refine ⟨9911500292507258879338301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6607666861671505919558867 9911500292507258879338301)
  ·
    refine ⟨3716812609690222079751863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9911500292507258879338301 3716812609690222079751863)
    ·
      refine ⟨5575218914535333119627795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3716812609690222079751863 5575218914535333119627795)
      ·
        refine ⟨8362828371802999679441693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5575218914535333119627795 8362828371802999679441693)
        ·
          refine ⟨3136060639426124879790635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8362828371802999679441693 3136060639426124879790635)
          ·
            refine ⟨4704090959139187319685953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3136060639426124879790635 4704090959139187319685953)
            ·
              refine ⟨3528068219354390489764465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4704090959139187319685953 3528068219354390489764465)
              ·
                refine ⟨2646051164515792867323349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3528068219354390489764465 2646051164515792867323349)
                ·
                  refine ⟨62016824168338895327891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2646051164515792867323349 62016824168338895327891)
                  ·
                    rfl

theorem cell21_271749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 7].length) (baseStart_271749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271749 prefixEnd_271749 := by exact prefixLift 271749
  have htrace : WordTrace (prefixWord ++ tailWord_271749) baseStart_271749 baseEnd_271749 := by
    simpa [prefixWord, tailWord_271749, baseEnd_271749] using wordTrace_append hprefix tailTrace_271749
  have hstable : (prefixWord ++ tailWord_271749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271749).length < 2 ^ (prefixWord ++ tailWord_271749).sum := by decide
  have hdescent : baseEnd_271749 < baseStart_271749 := by decide
  rcases family_descends (prefixWord ++ tailWord_271749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271772 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 4]
def baseStart_271772 : Nat := 118140960795 + 271772 * 2 ^ 59
def prefixEnd_271772 : Nat := 4983230072969 + 3 ^ 40 * 271772 * 2
def baseEnd_271772 : Nat := 62022073081695966444511

theorem tailTrace_271772 : CollatzResearch.WordTrace tailWord_271772 prefixEnd_271772 62022073081695966444511 := by
  unfold tailWord_271772
  simp only [CollatzResearch.WordTrace]
  refine ⟨4956169585711966903712785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6608226114282622538283713 4956169585711966903712785)
  ·
    refine ⟨3717127189283975177784589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4956169585711966903712785 3717127189283975177784589)
    ·
      refine ⟨1393922695981490691669221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3717127189283975177784589 1393922695981490691669221)
      ·
        refine ⟨261360505496529504687979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1393922695981490691669221 261360505496529504687979)
        ·
          refine ⟨392040758244794257031969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 261360505496529504687979 392040758244794257031969)
          ·
            refine ⟨294030568683595692773977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392040758244794257031969 294030568683595692773977)
            ·
              refine ⟨220522926512696769580483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294030568683595692773977 220522926512696769580483)
              ·
                refine ⟨330784389769045154370725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220522926512696769580483 330784389769045154370725)
                ·
                  refine ⟨62022073081695966444511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 330784389769045154370725 62022073081695966444511)
                  ·
                    rfl

theorem cell21_271772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_271772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271772 prefixEnd_271772 := by exact prefixLift 271772
  have htrace : WordTrace (prefixWord ++ tailWord_271772) baseStart_271772 baseEnd_271772 := by
    simpa [prefixWord, tailWord_271772, baseEnd_271772] using wordTrace_append hprefix tailTrace_271772
  have hstable : (prefixWord ++ tailWord_271772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271772).length < 2 ^ (prefixWord ++ tailWord_271772).sum := by decide
  have hdescent : baseEnd_271772 < baseStart_271772 := by decide
  rcases family_descends (prefixWord ++ tailWord_271772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271873 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 6]
def baseStart_271873 : Nat := 118140960795 + 271873 * 2 ^ 59
def prefixEnd_271873 : Nat := 4983230072969 + 3 ^ 40 * 271873 * 2
def baseEnd_271873 : Nat := 62045122657742235260971

theorem tailTrace_271873 : CollatzResearch.WordTrace tailWord_271873 prefixEnd_271873 62045122657742235260971 := by
  unfold tailWord_271873
  simp only [CollatzResearch.WordTrace]
  refine ⟨9916022944058028056852273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6610681962705352037901515 9916022944058028056852273)
  ·
    refine ⟨7437017208043521042639205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9916022944058028056852273 7437017208043521042639205)
    ·
      refine ⟨1394440726508160195494851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7437017208043521042639205 1394440726508160195494851)
      ·
        refine ⟨2091661089762240293242277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1394440726508160195494851 2091661089762240293242277)
        ·
          refine ⟨392186454330420054982927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2091661089762240293242277 392186454330420054982927)
          ·
            refine ⟨588279681495630082474391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392186454330420054982927 588279681495630082474391)
            ·
              refine ⟨882419522243445123711587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 588279681495630082474391 882419522243445123711587)
              ·
                refine ⟨1323629283365167685567381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882419522243445123711587 1323629283365167685567381)
                ·
                  refine ⟨62045122657742235260971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1323629283365167685567381 62045122657742235260971)
                  ·
                    rfl

theorem cell21_271873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_271873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271873 prefixEnd_271873 := by exact prefixLift 271873
  have htrace : WordTrace (prefixWord ++ tailWord_271873) baseStart_271873 baseEnd_271873 := by
    simpa [prefixWord, tailWord_271873, baseEnd_271873] using wordTrace_append hprefix tailTrace_271873
  have hstable : (prefixWord ++ tailWord_271873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271873).length < 2 ^ (prefixWord ++ tailWord_271873).sum := by decide
  have hdescent : baseEnd_271873 < baseStart_271873 := by decide
  rcases family_descends (prefixWord ++ tailWord_271873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_271904 : List Nat := [2, 1, 1, 6, 1, 1, 4, 5]
def baseStart_271904 : Nat := 118140960795 + 271904 * 2 ^ 59
def prefixEnd_271904 : Nat := 4983230072969 + 3 ^ 40 * 271904 * 2
def baseEnd_271904 : Nat := 20684065760031023414747

theorem tailTrace_271904 : CollatzResearch.WordTrace tailWord_271904 prefixEnd_271904 20684065760031023414747 := by
  unfold tailWord_271904
  simp only [CollatzResearch.WordTrace]
  refine ⟨4958576803472860175615383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6611435737963813567487177 4958576803472860175615383)
  ·
    refine ⟨7437865205209290263423075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4958576803472860175615383 7437865205209290263423075)
    ·
      refine ⟨11156797807813935395134613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7437865205209290263423075 11156797807813935395134613)
      ·
        refine ⟨522974897241278221646935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11156797807813935395134613 522974897241278221646935)
        ·
          refine ⟨784462345861917332470403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 522974897241278221646935 784462345861917332470403)
          ·
            refine ⟨1176693518792875998705605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784462345861917332470403 1176693518792875998705605)
            ·
              refine ⟨220630034773664249757301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1176693518792875998705605 220630034773664249757301)
              ·
                refine ⟨20684065760031023414747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 220630034773664249757301 20684065760031023414747)
                ·
                  rfl

theorem cell21_271904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_271904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_271904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_271904 prefixEnd_271904 := by exact prefixLift 271904
  have htrace : WordTrace (prefixWord ++ tailWord_271904) baseStart_271904 baseEnd_271904 := by
    simpa [prefixWord, tailWord_271904, baseEnd_271904] using wordTrace_append hprefix tailTrace_271904
  have hstable : (prefixWord ++ tailWord_271904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_271904).length < 2 ^ (prefixWord ++ tailWord_271904).sum := by decide
  have hdescent : baseEnd_271904 < baseStart_271904 := by decide
  rcases family_descends (prefixWord ++ tailWord_271904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272028 : List Nat := [2, 2, 3, 2, 3, 1, 2, 3, 3]
def baseStart_272028 : Nat := 118140960795 + 272028 * 2 ^ 59
def prefixEnd_272028 : Nat := 4983230072969 + 3 ^ 40 * 272028 * 2
def baseEnd_272028 : Nat := 62080495769496410177321

theorem tailTrace_272028 : CollatzResearch.WordTrace tailWord_272028 prefixEnd_272028 62080495769496410177321 := by
  unfold tailWord_272028
  simp only [CollatzResearch.WordTrace]
  refine ⟨4960838129248244764372369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6614450838997659685829825 4960838129248244764372369)
  ·
    refine ⟨3720628596936183573279277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4960838129248244764372369 3720628596936183573279277)
    ·
      refine ⟨1395235723851068839979729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3720628596936183573279277 1395235723851068839979729)
      ·
        refine ⟨1046426792888301629984797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1395235723851068839979729 1046426792888301629984797)
        ·
          refine ⟨392410047333113111244299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1046426792888301629984797 392410047333113111244299)
          ·
            refine ⟨588615070999669666866449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 392410047333113111244299 588615070999669666866449)
            ·
              refine ⟨441461303249752250149837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 588615070999669666866449 441461303249752250149837)
              ·
                refine ⟨165547988718657093806189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441461303249752250149837 165547988718657093806189)
                ·
                  refine ⟨62080495769496410177321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165547988718657093806189 62080495769496410177321)
                  ·
                    rfl

theorem cell21_272028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_272028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272028 prefixEnd_272028 := by exact prefixLift 272028
  have htrace : WordTrace (prefixWord ++ tailWord_272028) baseStart_272028 baseEnd_272028 := by
    simpa [prefixWord, tailWord_272028, baseEnd_272028] using wordTrace_append hprefix tailTrace_272028
  have hstable : (prefixWord ++ tailWord_272028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272028).length < 2 ^ (prefixWord ++ tailWord_272028).sum := by decide
  have hdescent : baseEnd_272028 < baseStart_272028 := by decide
  rcases family_descends (prefixWord ++ tailWord_272028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272104 : List Nat := [2, 1, 4, 1, 3, 2, 3, 2, 3]
def baseStart_272104 : Nat := 118140960795 + 272104 * 2 ^ 59
def prefixEnd_272104 : Nat := 4983230072969 + 3 ^ 40 * 272104 * 2
def baseEnd_272104 : Nat := 62097840004937166910499

theorem tailTrace_272104 : CollatzResearch.WordTrace tailWord_272104 prefixEnd_272104 62097840004937166910499 := by
  unfold tailWord_272104
  simp only [CollatzResearch.WordTrace]
  refine ⟨4962224103110577254255683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6616298804147436339007577 4962224103110577254255683)
  ·
    refine ⟨7443336154665865881383525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4962224103110577254255683 7443336154665865881383525)
    ·
      refine ⟨1395625528999849852759411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7443336154665865881383525 1395625528999849852759411)
      ·
        refine ⟨2093438293499774779139117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395625528999849852759411 2093438293499774779139117)
        ·
          refine ⟨785039360062415542177169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2093438293499774779139117 785039360062415542177169)
          ·
            refine ⟨588779520046811656632877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 785039360062415542177169 588779520046811656632877)
            ·
              refine ⟨220792320017554371237329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 588779520046811656632877 220792320017554371237329)
              ·
                refine ⟨165594240013165778427997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220792320017554371237329 165594240013165778427997)
                ·
                  refine ⟨62097840004937166910499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165594240013165778427997 62097840004937166910499)
                  ·
                    rfl

theorem cell21_272104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 3].length) (baseStart_272104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272104 prefixEnd_272104 := by exact prefixLift 272104
  have htrace : WordTrace (prefixWord ++ tailWord_272104) baseStart_272104 baseEnd_272104 := by
    simpa [prefixWord, tailWord_272104, baseEnd_272104] using wordTrace_append hprefix tailTrace_272104
  have hstable : (prefixWord ++ tailWord_272104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272104).length < 2 ^ (prefixWord ++ tailWord_272104).sum := by decide
  have hdescent : baseEnd_272104 < baseStart_272104 := by decide
  rcases family_descends (prefixWord ++ tailWord_272104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272118 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 4]
def baseStart_272118 : Nat := 118140960795 + 272118 * 2 ^ 59
def prefixEnd_272118 : Nat := 4983230072969 + 3 ^ 40 * 272118 * 2
def baseEnd_272118 : Nat := 62101034995676253677137

theorem tailTrace_272118 : CollatzResearch.WordTrace tailWord_272118 prefixEnd_272118 62101034995676253677137 := by
  unfold tailWord_272118
  simp only [CollatzResearch.WordTrace]
  refine ⟨620309926760652181220063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6616639218780289933014005 620309926760652181220063)
  ·
    refine ⟨930464890140978271830095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 620309926760652181220063 930464890140978271830095)
    ·
      refine ⟨1395697335211467407745143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 930464890140978271830095 1395697335211467407745143)
      ·
        refine ⟨2093546002817201111617715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395697335211467407745143 2093546002817201111617715)
        ·
          refine ⟨3140319004225801667426573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093546002817201111617715 3140319004225801667426573)
          ·
            refine ⟨1177619626584675625284965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3140319004225801667426573 1177619626584675625284965)
            ·
              refine ⟨220803679984626679740931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1177619626584675625284965 220803679984626679740931)
              ·
                refine ⟨331205519976940019611397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220803679984626679740931 331205519976940019611397)
                ·
                  refine ⟨62101034995676253677137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 331205519976940019611397 62101034995676253677137)
                  ·
                    rfl

theorem cell21_272118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_272118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272118 prefixEnd_272118 := by exact prefixLift 272118
  have htrace : WordTrace (prefixWord ++ tailWord_272118) baseStart_272118 baseEnd_272118 := by
    simpa [prefixWord, tailWord_272118, baseEnd_272118] using wordTrace_append hprefix tailTrace_272118
  have hstable : (prefixWord ++ tailWord_272118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272118).length < 2 ^ (prefixWord ++ tailWord_272118).sum := by decide
  have hdescent : baseEnd_272118 < baseStart_272118 := by decide
  rcases family_descends (prefixWord ++ tailWord_272118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272129 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 5]
def baseStart_272129 : Nat := 118140960795 + 272129 * 2 ^ 59
def prefixEnd_272129 : Nat := 4983230072969 + 3 ^ 40 * 272129 * 2
def baseEnd_272129 : Nat := 62103545345542678993781

theorem tailTrace_272129 : CollatzResearch.WordTrace tailWord_272129 prefixEnd_272129 62103545345542678993781 := by
  unfold tailWord_272129
  simp only [CollatzResearch.WordTrace]
  refine ⟨9925360031130583778171441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6616906687420389185447627 9925360031130583778171441)
  ·
    refine ⟨7444020023347937833628581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9925360031130583778171441 7444020023347937833628581)
    ·
      refine ⟨1395753754377738343805359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7444020023347937833628581 1395753754377738343805359)
      ·
        refine ⟨2093630631566607515708039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395753754377738343805359 2093630631566607515708039)
        ·
          refine ⟨3140445947349911273562059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093630631566607515708039 3140445947349911273562059)
          ·
            refine ⟨4710668921024866910343089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140445947349911273562059 4710668921024866910343089)
            ·
              refine ⟨3533001690768650182757317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4710668921024866910343089 3533001690768650182757317)
              ·
                refine ⟨662437817019121909266997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3533001690768650182757317 662437817019121909266997)
                ·
                  refine ⟨62103545345542678993781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 662437817019121909266997 62103545345542678993781)
                  ·
                    rfl

theorem cell21_272129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_272129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272129 prefixEnd_272129 := by exact prefixLift 272129
  have htrace : WordTrace (prefixWord ++ tailWord_272129) baseStart_272129 baseEnd_272129 := by
    simpa [prefixWord, tailWord_272129, baseEnd_272129] using wordTrace_append hprefix tailTrace_272129
  have hstable : (prefixWord ++ tailWord_272129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272129).length < 2 ^ (prefixWord ++ tailWord_272129).sum := by decide
  have hdescent : baseEnd_272129 < baseStart_272129 := by decide
  rcases family_descends (prefixWord ++ tailWord_272129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272143 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 6]
def baseStart_272143 : Nat := 118140960795 + 272143 * 2 ^ 59
def prefixEnd_272143 : Nat := 4983230072969 + 3 ^ 40 * 272143 * 2
def baseEnd_272143 : Nat := 62106740336281765760419

theorem tailTrace_272143 : CollatzResearch.WordTrace tailWord_272143 prefixEnd_272143 62106740336281765760419 := by
  unfold tailWord_272143
  simp only [CollatzResearch.WordTrace]
  refine ⟨9925870653079864169181083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6617247102053242779454055 9925870653079864169181083)
  ·
    refine ⟨14888805979619796253771625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9925870653079864169181083 14888805979619796253771625)
    ·
      refine ⟨11166604484714847190328719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14888805979619796253771625 11166604484714847190328719)
      ·
        refine ⟨16749906727072270785493079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11166604484714847190328719 16749906727072270785493079)
        ·
          refine ⟨25124860090608406178239619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16749906727072270785493079 25124860090608406178239619)
          ·
            refine ⟨37687290135912609267359429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25124860090608406178239619 37687290135912609267359429)
            ·
              refine ⟨7066366900483614237629893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37687290135912609267359429 7066366900483614237629893)
              ·
                refine ⟨1324943793840677669555605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7066366900483614237629893 1324943793840677669555605)
                ·
                  refine ⟨62106740336281765760419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1324943793840677669555605 62106740336281765760419)
                  ·
                    rfl

theorem cell21_272143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_272143 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272143 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272143 prefixEnd_272143 := by exact prefixLift 272143
  have htrace : WordTrace (prefixWord ++ tailWord_272143) baseStart_272143 baseEnd_272143 := by
    simpa [prefixWord, tailWord_272143, baseEnd_272143] using wordTrace_append hprefix tailTrace_272143
  have hstable : (prefixWord ++ tailWord_272143).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272143).length < 2 ^ (prefixWord ++ tailWord_272143).sum := by decide
  have hdescent : baseEnd_272143 < baseStart_272143 := by decide
  rcases family_descends (prefixWord ++ tailWord_272143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272163 : List Nat := [1, 1, 1, 4, 2, 1, 6, 2, 3]
def baseStart_272163 : Nat := 118140960795 + 272163 * 2 ^ 59
def prefixEnd_272163 : Nat := 4983230072969 + 3 ^ 40 * 272163 * 2
def baseEnd_272163 : Nat := 62111304608766175427045

theorem tailTrace_272163 : CollatzResearch.WordTrace tailWord_272163 prefixEnd_272163 62111304608766175427045 := by
  unfold tailWord_272163
  simp only [CollatzResearch.WordTrace]
  refine ⟨9926600113007407584909143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6617733408671605056606095 9926600113007407584909143)
  ·
    refine ⟨14889900169511111377363715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9926600113007407584909143 14889900169511111377363715)
    ·
      refine ⟨22334850254266667066045573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14889900169511111377363715 22334850254266667066045573)
      ·
        refine ⟨4187784422675000074883545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22334850254266667066045573 4187784422675000074883545)
        ·
          refine ⟨3140838317006250056162659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4187784422675000074883545 3140838317006250056162659)
          ·
            refine ⟨4711257475509375084243989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140838317006250056162659 4711257475509375084243989)
            ·
              refine ⟨220840194164501957073937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4711257475509375084243989 220840194164501957073937)
              ·
                refine ⟨165630145623376467805453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220840194164501957073937 165630145623376467805453)
                ·
                  refine ⟨62111304608766175427045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165630145623376467805453 62111304608766175427045)
                  ·
                    rfl

theorem cell21_272163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 3].length) (baseStart_272163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272163 prefixEnd_272163 := by exact prefixLift 272163
  have htrace : WordTrace (prefixWord ++ tailWord_272163) baseStart_272163 baseEnd_272163 := by
    simpa [prefixWord, tailWord_272163, baseEnd_272163] using wordTrace_append hprefix tailTrace_272163
  have hstable : (prefixWord ++ tailWord_272163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272163).length < 2 ^ (prefixWord ++ tailWord_272163).sum := by decide
  have hdescent : baseEnd_272163 < baseStart_272163 := by decide
  rcases family_descends (prefixWord ++ tailWord_272163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272281 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 5]
def baseStart_272281 : Nat := 118140960795 + 272281 * 2 ^ 59
def prefixEnd_272281 : Nat := 4983230072969 + 3 ^ 40 * 272281 * 2
def baseEnd_272281 : Nat := 62138233816424192460137

theorem tailTrace_272281 : CollatzResearch.WordTrace tailWord_272281 prefixEnd_272281 62138233816424192460137 := by
  unfold tailWord_272281
  simp only [CollatzResearch.WordTrace]
  refine ⟨9930903926579913737704697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6620602617719942491803131 9930903926579913737704697)
  ·
    refine ⟨7448177944934935303278523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9930903926579913737704697 7448177944934935303278523)
    ·
      refine ⟨11172266917402402954917785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7448177944934935303278523 11172266917402402954917785)
      ·
        refine ⟨8379200188051802216188339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11172266917402402954917785 8379200188051802216188339)
        ·
          refine ⟨12568800282077703324282509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8379200188051802216188339 12568800282077703324282509)
          ·
            refine ⟨4713300105779138746605941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12568800282077703324282509 4713300105779138746605941)
            ·
              refine ⟨441871884916794257494307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4713300105779138746605941 441871884916794257494307)
              ·
                refine ⟨662807827375191386241461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 441871884916794257494307 662807827375191386241461)
                ·
                  refine ⟨62138233816424192460137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 662807827375191386241461 62138233816424192460137)
                  ·
                    rfl

theorem cell21_272281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 5].length) (baseStart_272281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272281 prefixEnd_272281 := by exact prefixLift 272281
  have htrace : WordTrace (prefixWord ++ tailWord_272281) baseStart_272281 baseEnd_272281 := by
    simpa [prefixWord, tailWord_272281, baseEnd_272281] using wordTrace_append hprefix tailTrace_272281
  have hstable : (prefixWord ++ tailWord_272281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272281).length < 2 ^ (prefixWord ++ tailWord_272281).sum := by decide
  have hdescent : baseEnd_272281 < baseStart_272281 := by decide
  rcases family_descends (prefixWord ++ tailWord_272281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272287 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 4]
def baseStart_272287 : Nat := 118140960795 + 272287 * 2 ^ 59
def prefixEnd_272287 : Nat := 4983230072969 + 3 ^ 40 * 272287 * 2
def baseEnd_272287 : Nat := 62139603098169515360125

theorem tailTrace_272287 : CollatzResearch.WordTrace tailWord_272287 prefixEnd_272287 62139603098169515360125 := by
  unfold tailWord_272287
  simp only [CollatzResearch.WordTrace]
  refine ⟨9931122764558176762423115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6620748509705451174948743 9931122764558176762423115)
  ·
    refine ⟨14896684146837265143634673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9931122764558176762423115 14896684146837265143634673)
    ·
      refine ⟨11172513110127948857726005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14896684146837265143634673 11172513110127948857726005)
      ·
        refine ⟨1047423104074495205411813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11172513110127948857726005 1047423104074495205411813)
        ·
          refine ⟨196391832013967851014715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1047423104074495205411813 196391832013967851014715)
          ·
            refine ⟨294587748020951776522073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196391832013967851014715 294587748020951776522073)
            ·
              refine ⟨220940811015713832391555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294587748020951776522073 220940811015713832391555)
              ·
                refine ⟨331411216523570748587333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220940811015713832391555 331411216523570748587333)
                ·
                  refine ⟨62139603098169515360125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 331411216523570748587333 62139603098169515360125)
                  ·
                    rfl

theorem cell21_272287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 4].length) (baseStart_272287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272287 prefixEnd_272287 := by exact prefixLift 272287
  have htrace : WordTrace (prefixWord ++ tailWord_272287) baseStart_272287 baseEnd_272287 := by
    simpa [prefixWord, tailWord_272287, baseEnd_272287] using wordTrace_append hprefix tailTrace_272287
  have hstable : (prefixWord ++ tailWord_272287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272287).length < 2 ^ (prefixWord ++ tailWord_272287).sum := by decide
  have hdescent : baseEnd_272287 < baseStart_272287 := by decide
  rcases family_descends (prefixWord ++ tailWord_272287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272332 : List Nat := [2, 2, 1, 4, 1, 4, 2, 2, 3]
def baseStart_272332 : Nat := 118140960795 + 272332 * 2 ^ 59
def prefixEnd_272332 : Nat := 4983230072969 + 3 ^ 40 * 272332 * 2
def baseEnd_272332 : Nat := 62149872711259437110033

theorem tailTrace_272332 : CollatzResearch.WordTrace tailWord_272332 prefixEnd_272332 62149872711259437110033 := by
  unfold tailWord_272332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4966382024697574723905625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6621842699596766298540833 4966382024697574723905625)
  ·
    refine ⟨3724786518523181042929219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4966382024697574723905625 3724786518523181042929219)
    ·
      refine ⟨5587179777784771564393829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3724786518523181042929219 5587179777784771564393829)
      ·
        refine ⟨1047596208334644668323843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5587179777784771564393829 1047596208334644668323843)
        ·
          refine ⟨1571394312501967002485765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1047596208334644668323843 1571394312501967002485765)
          ·
            refine ⟨294636433594118812966081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1571394312501967002485765 294636433594118812966081)
            ·
              refine ⟨220977325195589109724561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 294636433594118812966081 220977325195589109724561)
              ·
                refine ⟨165732993896691832293421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220977325195589109724561 165732993896691832293421)
                ·
                  refine ⟨62149872711259437110033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165732993896691832293421 62149872711259437110033)
                  ·
                    rfl

theorem cell21_272332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_272332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272332 prefixEnd_272332 := by exact prefixLift 272332
  have htrace : WordTrace (prefixWord ++ tailWord_272332) baseStart_272332 baseEnd_272332 := by
    simpa [prefixWord, tailWord_272332, baseEnd_272332] using wordTrace_append hprefix tailTrace_272332
  have hstable : (prefixWord ++ tailWord_272332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272332).length < 2 ^ (prefixWord ++ tailWord_272332).sum := by decide
  have hdescent : baseEnd_272332 < baseStart_272332 := by decide
  rcases family_descends (prefixWord ++ tailWord_272332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272436 : List Nat := [2, 5, 1, 2, 2, 2, 7]
def baseStart_272436 : Nat := 118140960795 + 272436 * 2 ^ 59
def prefixEnd_272436 : Nat := 4983230072969 + 3 ^ 40 * 272436 * 2
def baseEnd_272436 : Nat := 6908178547575374152943

theorem tailTrace_272436 : CollatzResearch.WordTrace tailWord_272436 prefixEnd_272436 6908178547575374152943 := by
  unfold tailWord_272436
  simp only [CollatzResearch.WordTrace]
  refine ⟨4968278620509187604798581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6624371494012250139731441 4968278620509187604798581)
  ·
    refine ⟨465776120672736337949867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4968278620509187604798581 465776120672736337949867)
    ·
      refine ⟨698664181009104506924801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 465776120672736337949867 698664181009104506924801)
      ·
        refine ⟨523998135756828380193601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 698664181009104506924801 523998135756828380193601)
        ·
          refine ⟨392998601817621285145201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 523998135756828380193601 392998601817621285145201)
          ·
            refine ⟨294748951363215963858901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 392998601817621285145201 294748951363215963858901)
            ·
              refine ⟨6908178547575374152943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 294748951363215963858901 6908178547575374152943)
              ·
                rfl

theorem cell21_272436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 7].length) (baseStart_272436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272436 prefixEnd_272436 := by exact prefixLift 272436
  have htrace : WordTrace (prefixWord ++ tailWord_272436) baseStart_272436 baseEnd_272436 := by
    simpa [prefixWord, tailWord_272436, baseEnd_272436] using wordTrace_append hprefix tailTrace_272436
  have hstable : (prefixWord ++ tailWord_272436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272436).length < 2 ^ (prefixWord ++ tailWord_272436).sum := by decide
  have hdescent : baseEnd_272436 < baseStart_272436 := by decide
  rcases family_descends (prefixWord ++ tailWord_272436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272447 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 6]
def baseStart_272447 : Nat := 118140960795 + 272447 * 2 ^ 59
def prefixEnd_272447 : Nat := 4983230072969 + 3 ^ 40 * 272447 * 2
def baseEnd_272447 : Nat := 62176117278044792693131

theorem tailTrace_272447 : CollatzResearch.WordTrace tailWord_272447 prefixEnd_272447 62176117278044792693131 := by
  unfold tailWord_272447
  simp only [CollatzResearch.WordTrace]
  refine ⟨9936958443978524088247595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6624638962652349392165063 9936958443978524088247595)
  ·
    refine ⟨14905437665967786132371393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9936958443978524088247595 14905437665967786132371393)
    ·
      refine ⟨11179078249475839599278545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14905437665967786132371393 11179078249475839599278545)
      ·
        refine ⟨8384308687106879699458909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11179078249475839599278545 8384308687106879699458909)
        ·
          refine ⟨3144115757665079887297091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8384308687106879699458909 3144115757665079887297091)
          ·
            refine ⟨4716173636497619830945637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3144115757665079887297091 4716173636497619830945637)
            ·
              refine ⟨884282556843303718302307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4716173636497619830945637 884282556843303718302307)
              ·
                refine ⟨1326423835264955577453461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 884282556843303718302307 1326423835264955577453461)
                ·
                  refine ⟨62176117278044792693131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1326423835264955577453461 62176117278044792693131)
                  ·
                    rfl

theorem cell21_272447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_272447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272447 prefixEnd_272447 := by exact prefixLift 272447
  have htrace : WordTrace (prefixWord ++ tailWord_272447) baseStart_272447 baseEnd_272447 := by
    simpa [prefixWord, tailWord_272447, baseEnd_272447] using wordTrace_append hprefix tailTrace_272447
  have hstable : (prefixWord ++ tailWord_272447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272447).length < 2 ^ (prefixWord ++ tailWord_272447).sum := by decide
  have hdescent : baseEnd_272447 < baseStart_272447 := by decide
  rcases family_descends (prefixWord ++ tailWord_272447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272526 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 5]
def baseStart_272526 : Nat := 118140960795 + 272526 * 2 ^ 59
def prefixEnd_272526 : Nat := 4983230072969 + 3 ^ 40 * 272526 * 2
def baseEnd_272526 : Nat := 62194146154358210876303

theorem tailTrace_272526 : CollatzResearch.WordTrace tailWord_272526 prefixEnd_272526 62194146154358210876303 := by
  unfold tailWord_272526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1242479976336540072546679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6626559873794880386915621 1242479976336540072546679)
  ·
    refine ⟨1863719964504810108820019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1242479976336540072546679 1863719964504810108820019)
    ·
      refine ⟨2795579946757215163230029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1863719964504810108820019 2795579946757215163230029)
      ·
        refine ⟨1048342480033955686211261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2795579946757215163230029 1048342480033955686211261)
        ·
          refine ⟨393128430012733382329223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1048342480033955686211261 393128430012733382329223)
          ·
            refine ⟨589692645019100073493835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393128430012733382329223 589692645019100073493835)
            ·
              refine ⟨884538967528650110240753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 589692645019100073493835 884538967528650110240753)
              ·
                refine ⟨663404225646487582680565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884538967528650110240753 663404225646487582680565)
                ·
                  refine ⟨62194146154358210876303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 663404225646487582680565 62194146154358210876303)
                  ·
                    rfl

theorem cell21_272526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_272526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272526 prefixEnd_272526 := by exact prefixLift 272526
  have htrace : WordTrace (prefixWord ++ tailWord_272526) baseStart_272526 baseEnd_272526 := by
    simpa [prefixWord, tailWord_272526, baseEnd_272526] using wordTrace_append hprefix tailTrace_272526
  have hstable : (prefixWord ++ tailWord_272526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272526).length < 2 ^ (prefixWord ++ tailWord_272526).sum := by decide
  have hdescent : baseEnd_272526 < baseStart_272526 := by decide
  rcases family_descends (prefixWord ++ tailWord_272526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272537 : List Nat := [1, 2, 1, 2, 1, 2, 1, 11]
def baseStart_272537 : Nat := 118140960795 + 272537 * 2 ^ 59
def prefixEnd_272537 : Nat := 4983230072969 + 3 ^ 40 * 272537 * 2
def baseEnd_272537 : Nat := 20732218834741545397649

theorem tailTrace_272537 : CollatzResearch.WordTrace tailWord_272537 prefixEnd_272537 20732218834741545397649 := by
  unfold tailWord_272537
  simp only [CollatzResearch.WordTrace]
  refine ⟨9940241013652469459023865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6626827342434979639349243 9940241013652469459023865)
  ·
    refine ⟨7455180760239352094267899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9940241013652469459023865 7455180760239352094267899)
    ·
      refine ⟨11182771140359028141401849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7455180760239352094267899 11182771140359028141401849)
      ·
        refine ⟨8387078355269271106051387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11182771140359028141401849 8387078355269271106051387)
        ·
          refine ⟨12580617532903906659077081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8387078355269271106051387 12580617532903906659077081)
          ·
            refine ⟨9435463149677929994307811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12580617532903906659077081 9435463149677929994307811)
            ·
              refine ⟨14153194724516894991461717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9435463149677929994307811 14153194724516894991461717)
              ·
                refine ⟨20732218834741545397649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 14153194724516894991461717 20732218834741545397649)
                ·
                  rfl

theorem cell21_272537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 11].length) (baseStart_272537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272537 prefixEnd_272537 := by exact prefixLift 272537
  have htrace : WordTrace (prefixWord ++ tailWord_272537) baseStart_272537 baseEnd_272537 := by
    simpa [prefixWord, tailWord_272537, baseEnd_272537] using wordTrace_append hprefix tailTrace_272537
  have hstable : (prefixWord ++ tailWord_272537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272537).length < 2 ^ (prefixWord ++ tailWord_272537).sum := by decide
  have hdescent : baseEnd_272537 < baseStart_272537 := by decide
  rcases family_descends (prefixWord ++ tailWord_272537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272543 : List Nat := [1, 1, 2, 6, 1, 2, 2, 3, 3]
def baseStart_272543 : Nat := 118140960795 + 272543 * 2 ^ 59
def prefixEnd_272543 : Nat := 4983230072969 + 3 ^ 40 * 272543 * 2
def baseEnd_272543 : Nat := 62198025785969959092935

theorem tailTrace_272543 : CollatzResearch.WordTrace tailWord_272543 prefixEnd_272543 62198025785969959092935 := by
  unfold tailWord_272543
  simp only [CollatzResearch.WordTrace]
  refine ⟨9940459851630732483742283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6626973234420488322494855 9940459851630732483742283)
  ·
    refine ⟨14910689777446098725613425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9940459851630732483742283 14910689777446098725613425)
    ·
      refine ⟨11183017333084574044210069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14910689777446098725613425 11183017333084574044210069)
      ·
        refine ⟨524203937488339408322347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11183017333084574044210069 524203937488339408322347)
        ·
          refine ⟨786305906232509112483521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524203937488339408322347 786305906232509112483521)
          ·
            refine ⟨589729429674381834362641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786305906232509112483521 589729429674381834362641)
            ·
              refine ⟨442297072255786375771981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 589729429674381834362641 442297072255786375771981)
              ·
                refine ⟨165861402095919890914493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 442297072255786375771981 165861402095919890914493)
                ·
                  refine ⟨62198025785969959092935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165861402095919890914493 62198025785969959092935)
                  ·
                    rfl

theorem cell21_272543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 3].length) (baseStart_272543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272543 prefixEnd_272543 := by exact prefixLift 272543
  have htrace : WordTrace (prefixWord ++ tailWord_272543) baseStart_272543 baseEnd_272543 := by
    simpa [prefixWord, tailWord_272543, baseEnd_272543] using wordTrace_append hprefix tailTrace_272543
  have hstable : (prefixWord ++ tailWord_272543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272543).length < 2 ^ (prefixWord ++ tailWord_272543).sum := by decide
  have hdescent : baseEnd_272543 < baseStart_272543 := by decide
  rcases family_descends (prefixWord ++ tailWord_272543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272557 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 4]
def baseStart_272557 : Nat := 118140960795 + 272557 * 2 ^ 59
def prefixEnd_272557 : Nat := 4983230072969 + 3 ^ 40 * 272557 * 2
def baseEnd_272557 : Nat := 62201220776709045859573

theorem tailTrace_272557 : CollatzResearch.WordTrace tailWord_272557 prefixEnd_272557 62201220776709045859573 := by
  unfold tailWord_272557
  simp only [CollatzResearch.WordTrace]
  refine ⟨9940970473580012874751925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6627313649053341916501283 9940970473580012874751925)
  ·
    refine ⟨931965981898126207007993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9940970473580012874751925 931965981898126207007993)
    ·
      refine ⟨698974486423594655255995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 931965981898126207007993 698974486423594655255995)
      ·
        refine ⟨1048461729635391982883993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 698974486423594655255995 1048461729635391982883993)
        ·
          refine ⟨786346297226543987162995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1048461729635391982883993 786346297226543987162995)
          ·
            refine ⟨1179519445839815980744493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786346297226543987162995 1179519445839815980744493)
            ·
              refine ⟨442319792189930992779185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1179519445839815980744493 442319792189930992779185)
              ·
                refine ⟨331739844142448244584389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442319792189930992779185 331739844142448244584389)
                ·
                  refine ⟨62201220776709045859573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 331739844142448244584389 62201220776709045859573)
                  ·
                    rfl

theorem cell21_272557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_272557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272557 prefixEnd_272557 := by exact prefixLift 272557
  have htrace : WordTrace (prefixWord ++ tailWord_272557) baseStart_272557 baseEnd_272557 := by
    simpa [prefixWord, tailWord_272557, baseEnd_272557] using wordTrace_append hprefix tailTrace_272557
  have hstable : (prefixWord ++ tailWord_272557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272557).length < 2 ^ (prefixWord ++ tailWord_272557).sum := by decide
  have hdescent : baseEnd_272557 < baseStart_272557 := by decide
  rcases family_descends (prefixWord ++ tailWord_272557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272574 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_272574 : Nat := 118140960795 + 272574 * 2 ^ 59
def prefixEnd_272574 : Nat := 4983230072969 + 3 ^ 40 * 272574 * 2
def baseEnd_272574 : Nat := 62205100408320794076205

theorem tailTrace_272574 : CollatzResearch.WordTrace tailWord_272574 prefixEnd_272574 62205100408320794076205 := by
  unfold tailWord_272574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1242698814314803097265097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6627727009678949852080517 1242698814314803097265097)
  ·
    refine ⟨932024110736102322948823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1242698814314803097265097 932024110736102322948823)
    ·
      refine ⟨1398036166104153484423235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 932024110736102322948823 1398036166104153484423235)
      ·
        refine ⟨2097054249156230226634853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398036166104153484423235 2097054249156230226634853)
        ·
          refine ⟨393197671716793167494035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2097054249156230226634853 393197671716793167494035)
          ·
            refine ⟨589796507575189751241053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393197671716793167494035 589796507575189751241053)
            ·
              refine ⟨221173690340696156715395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 589796507575189751241053 221173690340696156715395)
              ·
                refine ⟨331760535511044235073093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221173690340696156715395 331760535511044235073093)
                ·
                  refine ⟨62205100408320794076205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 331760535511044235073093 62205100408320794076205)
                  ·
                    rfl

theorem cell21_272574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_272574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272574 prefixEnd_272574 := by exact prefixLift 272574
  have htrace : WordTrace (prefixWord ++ tailWord_272574) baseStart_272574 baseEnd_272574 := by
    simpa [prefixWord, tailWord_272574, baseEnd_272574] using wordTrace_append hprefix tailTrace_272574
  have hstable : (prefixWord ++ tailWord_272574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272574).length < 2 ^ (prefixWord ++ tailWord_272574).sum := by decide
  have hdescent : baseEnd_272574 < baseStart_272574 := by decide
  rcases family_descends (prefixWord ++ tailWord_272574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272602 : List Nat := [3, 1, 1, 2, 2, 1, 5, 3, 3]
def baseStart_272602 : Nat := 118140960795 + 272602 * 2 ^ 59
def prefixEnd_272602 : Nat := 4983230072969 + 3 ^ 40 * 272602 * 2
def baseEnd_272602 : Nat := 62211490389798967609481

theorem tailTrace_272602 : CollatzResearch.WordTrace tailWord_272602 prefixEnd_272602 62211490389798967609481 := by
  unfold tailWord_272602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2485652939604246390035015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6628407838944657040093373 2485652939604246390035015)
  ·
    refine ⟨3728479409406369585052523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2485652939604246390035015 3728479409406369585052523)
    ·
      refine ⟨5592719114109554377578785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3728479409406369585052523 5592719114109554377578785)
      ·
        refine ⟨4194539335582165783184089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5592719114109554377578785 4194539335582165783184089)
        ·
          refine ⟨3145904501686624337388067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4194539335582165783184089 3145904501686624337388067)
          ·
            refine ⟨4718856752529936506082101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3145904501686624337388067 4718856752529936506082101)
            ·
              refine ⟨442392820549681547445197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4718856752529936506082101 442392820549681547445197)
              ·
                refine ⟨165897307706130580291949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 442392820549681547445197 165897307706130580291949)
                ·
                  refine ⟨62211490389798967609481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 165897307706130580291949 62211490389798967609481)
                  ·
                    rfl

theorem cell21_272602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_272602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272602 prefixEnd_272602 := by exact prefixLift 272602
  have htrace : WordTrace (prefixWord ++ tailWord_272602) baseStart_272602 baseEnd_272602 := by
    simpa [prefixWord, tailWord_272602, baseEnd_272602] using wordTrace_append hprefix tailTrace_272602
  have hstable : (prefixWord ++ tailWord_272602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272602).length < 2 ^ (prefixWord ++ tailWord_272602).sum := by decide
  have hdescent : baseEnd_272602 < baseStart_272602 := by decide
  rcases family_descends (prefixWord ++ tailWord_272602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272630 : List Nat := [5, 1, 1, 1, 1, 1, 3, 8]
def baseStart_272630 : Nat := 118140960795 + 272630 * 2 ^ 59
def prefixEnd_272630 : Nat := 4983230072969 + 3 ^ 40 * 272630 * 2
def baseEnd_272630 : Nat := 20739293457092380380919

theorem tailTrace_272630 : CollatzResearch.WordTrace tailWord_272630 prefixEnd_272630 20739293457092380380919 := by
  unfold tailWord_272630
  simp only [CollatzResearch.WordTrace]
  refine ⟨621477062644721646384959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6629088668210364228106229 621477062644721646384959)
  ·
    refine ⟨932215593967082469577439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 621477062644721646384959 932215593967082469577439)
    ·
      refine ⟨1398323390950623704366159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 932215593967082469577439 1398323390950623704366159)
      ·
        refine ⟨2097485086425935556549239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398323390950623704366159 2097485086425935556549239)
        ·
          refine ⟨3146227629638903334823859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2097485086425935556549239 3146227629638903334823859)
          ·
            refine ⟨4719341444458355002235789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3146227629638903334823859 4719341444458355002235789)
            ·
              refine ⟨1769753041671883125838421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4719341444458355002235789 1769753041671883125838421)
              ·
                refine ⟨20739293457092380380919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1769753041671883125838421 20739293457092380380919)
                ·
                  rfl

theorem cell21_272630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_272630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272630 prefixEnd_272630 := by exact prefixLift 272630
  have htrace : WordTrace (prefixWord ++ tailWord_272630) baseStart_272630 baseEnd_272630 := by
    simpa [prefixWord, tailWord_272630, baseEnd_272630] using wordTrace_append hprefix tailTrace_272630
  have hstable : (prefixWord ++ tailWord_272630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272630).length < 2 ^ (prefixWord ++ tailWord_272630).sum := by decide
  have hdescent : baseEnd_272630 < baseStart_272630 := by decide
  rcases family_descends (prefixWord ++ tailWord_272630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272771 : List Nat := [1, 1, 1, 3, 6, 2, 1, 3, 3]
def baseStart_272771 : Nat := 118140960795 + 272771 * 2 ^ 59
def prefixEnd_272771 : Nat := 4983230072969 + 3 ^ 40 * 272771 * 2
def baseEnd_272771 : Nat := 62250058492292229292469

theorem tailTrace_272771 : CollatzResearch.WordTrace tailWord_272771 prefixEnd_272771 62250058492292229292469 := by
  unfold tailWord_272771
  simp only [CollatzResearch.WordTrace]
  refine ⟨9948775694804727423042167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6632517129869818282028111 9948775694804727423042167)
  ·
    refine ⟨14923163542207091134563251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9948775694804727423042167 14923163542207091134563251)
    ·
      refine ⟨22384745313310636701844877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14923163542207091134563251 22384745313310636701844877)
      ·
        refine ⟨8394279492491488763191829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22384745313310636701844877 8394279492491488763191829)
        ·
          refine ⟨393481851210538535774617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8394279492491488763191829 393481851210538535774617)
          ·
            refine ⟨295111388407903901830963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 393481851210538535774617 295111388407903901830963)
            ·
              refine ⟨442667082611855852746445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295111388407903901830963 442667082611855852746445)
              ·
                refine ⟨166000155979445944779917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 442667082611855852746445 166000155979445944779917)
                ·
                  refine ⟨62250058492292229292469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166000155979445944779917 62250058492292229292469)
                  ·
                    rfl

theorem cell21_272771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 3].length) (baseStart_272771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272771 prefixEnd_272771 := by exact prefixLift 272771
  have htrace : WordTrace (prefixWord ++ tailWord_272771) baseStart_272771 baseEnd_272771 := by
    simpa [prefixWord, tailWord_272771, baseEnd_272771] using wordTrace_append hprefix tailTrace_272771
  have hstable : (prefixWord ++ tailWord_272771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272771).length < 2 ^ (prefixWord ++ tailWord_272771).sum := by decide
  have hdescent : baseEnd_272771 < baseStart_272771 := by decide
  rcases family_descends (prefixWord ++ tailWord_272771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272782 : List Nat := [4, 1, 1, 4, 1, 1, 9]
def baseStart_272782 : Nat := 118140960795 + 272782 * 2 ^ 59
def prefixEnd_272782 : Nat := 4983230072969 + 3 ^ 40 * 272782 * 2
def baseEnd_272782 : Nat := 6916952093573183845457

theorem tailTrace_272782 : CollatzResearch.WordTrace tailWord_272782 prefixEnd_272782 6916952093573183845457 := by
  unfold tailWord_272782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1243647112220609537711575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6632784598509917534461733 1243647112220609537711575)
  ·
    refine ⟨1865470668330914306567363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1243647112220609537711575 1865470668330914306567363)
    ·
      refine ⟨2798206002496371459851045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1865470668330914306567363 2798206002496371459851045)
      ·
        refine ⟨524663625468069648722071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2798206002496371459851045 524663625468069648722071)
        ·
          refine ⟨786995438202104473083107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524663625468069648722071 786995438202104473083107)
          ·
            refine ⟨1180493157303156709624661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786995438202104473083107 1180493157303156709624661)
            ·
              refine ⟨6916952093573183845457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1180493157303156709624661 6916952093573183845457)
              ·
                rfl

theorem cell21_272782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 9].length) (baseStart_272782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272782 prefixEnd_272782 := by exact prefixLift 272782
  have htrace : WordTrace (prefixWord ++ tailWord_272782) baseStart_272782 baseEnd_272782 := by
    simpa [prefixWord, tailWord_272782, baseEnd_272782] using wordTrace_append hprefix tailTrace_272782
  have hstable : (prefixWord ++ tailWord_272782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272782).length < 2 ^ (prefixWord ++ tailWord_272782).sum := by decide
  have hdescent : baseEnd_272782 < baseStart_272782 := by decide
  rcases family_descends (prefixWord ++ tailWord_272782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272788 : List Nat := [2, 4, 2, 1, 3, 1, 3, 2, 3]
def baseStart_272788 : Nat := 118140960795 + 272788 * 2 ^ 59
def prefixEnd_272788 : Nat := 4983230072969 + 3 ^ 40 * 272788 * 2
def baseEnd_272788 : Nat := 62253938123903977509101

theorem tailTrace_272788 : CollatzResearch.WordTrace tailWord_272788 prefixEnd_272788 62253938123903977509101 := by
  unfold tailWord_272788
  simp only [CollatzResearch.WordTrace]
  refine ⟨4974697867871569663205509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6632930490495426217607345 4974697867871569663205509)
  ·
    refine ⟨932755850225919311851033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4974697867871569663205509 932755850225919311851033)
    ·
      refine ⟨699566887669439483888275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 932755850225919311851033 699566887669439483888275)
      ·
        refine ⟨1049350331504159225832413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 699566887669439483888275 1049350331504159225832413)
        ·
          refine ⟨393506374314059709687155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1049350331504159225832413 393506374314059709687155)
          ·
            refine ⟨590259561471089564530733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393506374314059709687155 590259561471089564530733)
            ·
              refine ⟨221347335551658586699025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 590259561471089564530733 221347335551658586699025)
              ·
                refine ⟨166010501663743940024269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221347335551658586699025 166010501663743940024269)
                ·
                  refine ⟨62253938123903977509101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166010501663743940024269 62253938123903977509101)
                  ·
                    rfl

theorem cell21_272788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_272788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272788 prefixEnd_272788 := by exact prefixLift 272788
  have htrace : WordTrace (prefixWord ++ tailWord_272788) baseStart_272788 baseEnd_272788 := by
    simpa [prefixWord, tailWord_272788, baseEnd_272788] using wordTrace_append hprefix tailTrace_272788
  have hstable : (prefixWord ++ tailWord_272788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272788).length < 2 ^ (prefixWord ++ tailWord_272788).sum := by decide
  have hdescent : baseEnd_272788 < baseStart_272788 := by decide
  rcases family_descends (prefixWord ++ tailWord_272788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272872 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 7]
def baseStart_272872 : Nat := 118140960795 + 272872 * 2 ^ 59
def prefixEnd_272872 : Nat := 4983230072969 + 3 ^ 40 * 272872 * 2
def baseEnd_272872 : Nat := 62273108068338498108929

theorem tailTrace_272872 : CollatzResearch.WordTrace tailWord_272872 prefixEnd_272872 62273108068338498108929 := by
  unfold tailWord_272872
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976229733719410836234435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6634972978292547781645913 4976229733719410836234435)
  ·
    refine ⟨7464344600579116254351653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4976229733719410836234435 7464344600579116254351653)
    ·
      refine ⟨1399564612608584297690935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7464344600579116254351653 1399564612608584297690935)
      ·
        refine ⟨2099346918912876446536403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1399564612608584297690935 2099346918912876446536403)
        ·
          refine ⟨3149020378369314669804605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2099346918912876446536403 3149020378369314669804605)
          ·
            refine ⟨1180882641888493001176727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3149020378369314669804605 1180882641888493001176727)
            ·
              refine ⟨1771323962832739501765091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1180882641888493001176727 1771323962832739501765091)
              ·
                refine ⟨2656985944249109252647637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1771323962832739501765091 2656985944249109252647637)
                ·
                  refine ⟨62273108068338498108929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2656985944249109252647637 62273108068338498108929)
                  ·
                    rfl

theorem cell21_272872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_272872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272872 prefixEnd_272872 := by exact prefixLift 272872
  have htrace : WordTrace (prefixWord ++ tailWord_272872) baseStart_272872 baseEnd_272872 := by
    simpa [prefixWord, tailWord_272872, baseEnd_272872] using wordTrace_append hprefix tailTrace_272872
  have hstable : (prefixWord ++ tailWord_272872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272872).length < 2 ^ (prefixWord ++ tailWord_272872).sum := by decide
  have hdescent : baseEnd_272872 < baseStart_272872 := by decide
  rcases family_descends (prefixWord ++ tailWord_272872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272889 : List Nat := [1, 2, 1, 3, 1, 2, 3, 5, 3]
def baseStart_272889 : Nat := 118140960795 + 272889 * 2 ^ 59
def prefixEnd_272889 : Nat := 4983230072969 + 3 ^ 40 * 272889 * 2
def baseEnd_272889 : Nat := 62276987699950246325561

theorem tailTrace_272889 : CollatzResearch.WordTrace tailWord_272889 prefixEnd_272889 62276987699950246325561 := by
  unfold tailWord_272889
  simp only [CollatzResearch.WordTrace]
  refine ⟨9953079508377233575837721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6635386338918155717225147 9953079508377233575837721)
  ·
    refine ⟨7464809631282925181878291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9953079508377233575837721 7464809631282925181878291)
    ·
      refine ⟨11197214446924387772817437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7464809631282925181878291 11197214446924387772817437)
      ·
        refine ⟨4198955417596645414806539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11197214446924387772817437 4198955417596645414806539)
        ·
          refine ⟨6298433126394968122209809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4198955417596645414806539 6298433126394968122209809)
          ·
            refine ⟨4723824844796226091657357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6298433126394968122209809 4723824844796226091657357)
            ·
              refine ⟨1771434316798584784371509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4723824844796226091657357 1771434316798584784371509)
              ·
                refine ⟨166071967199867323534829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1771434316798584784371509 166071967199867323534829)
                ·
                  refine ⟨62276987699950246325561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166071967199867323534829 62276987699950246325561)
                  ·
                    rfl

theorem cell21_272889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 3].length) (baseStart_272889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272889 prefixEnd_272889 := by exact prefixLift 272889
  have htrace : WordTrace (prefixWord ++ tailWord_272889) baseStart_272889 baseEnd_272889 := by
    simpa [prefixWord, tailWord_272889, baseEnd_272889] using wordTrace_append hprefix tailTrace_272889
  have hstable : (prefixWord ++ tailWord_272889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272889).length < 2 ^ (prefixWord ++ tailWord_272889).sum := by decide
  have hdescent : baseEnd_272889 < baseStart_272889 := by decide
  rcases family_descends (prefixWord ++ tailWord_272889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272917 : List Nat := [1, 3, 2, 1, 3, 1, 2, 8]
def baseStart_272917 : Nat := 118140960795 + 272917 * 2 ^ 59
def prefixEnd_272917 : Nat := 4983230072969 + 3 ^ 40 * 272917 * 2
def baseEnd_272917 : Nat := 20761125893809473286279

theorem tailTrace_272917 : CollatzResearch.WordTrace tailWord_272917 prefixEnd_272917 20761125893809473286279 := by
  unfold tailWord_272917
  simp only [CollatzResearch.WordTrace]
  refine ⟨9954100752275794357857005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6636067168183862905238003 9954100752275794357857005)
  ·
    refine ⟨3732787782103422884196377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9954100752275794357857005 3732787782103422884196377)
    ·
      refine ⟨2799590836577567163147283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3732787782103422884196377 2799590836577567163147283)
      ·
        refine ⟨4199386254866350744720925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2799590836577567163147283 4199386254866350744720925)
        ·
          refine ⟨1574769845574881529270347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4199386254866350744720925 1574769845574881529270347)
          ·
            refine ⟨2362154768362322293905521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1574769845574881529270347 2362154768362322293905521)
            ·
              refine ⟨1771616076271741720429141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2362154768362322293905521 1771616076271741720429141)
              ·
                refine ⟨20761125893809473286279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1771616076271741720429141 20761125893809473286279)
                ·
                  rfl

theorem cell21_272917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 8].length) (baseStart_272917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272917 prefixEnd_272917 := by exact prefixLift 272917
  have htrace : WordTrace (prefixWord ++ tailWord_272917) baseStart_272917 baseEnd_272917 := by
    simpa [prefixWord, tailWord_272917, baseEnd_272917] using wordTrace_append hprefix tailTrace_272917
  have hstable : (prefixWord ++ tailWord_272917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272917).length < 2 ^ (prefixWord ++ tailWord_272917).sum := by decide
  have hdescent : baseEnd_272917 < baseStart_272917 := by decide
  rcases family_descends (prefixWord ++ tailWord_272917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272965 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 5]
def baseStart_272965 : Nat := 118140960795 + 272965 * 2 ^ 59
def prefixEnd_272965 : Nat := 4983230072969 + 3 ^ 40 * 272965 * 2
def baseEnd_272965 : Nat := 62294331935391003058739

theorem tailTrace_272965 : CollatzResearch.WordTrace tailWord_272965 prefixEnd_272965 62294331935391003058739 := by
  unfold tailWord_272965
  simp only [CollatzResearch.WordTrace]
  refine ⟨9955851456101898555604349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6637234304067932370402899 9955851456101898555604349)
  ·
    refine ⟨3733444296038211958351631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9955851456101898555604349 3733444296038211958351631)
    ·
      refine ⟨5600166444057317937527447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3733444296038211958351631 5600166444057317937527447)
      ·
        refine ⟨8400249666085976906291171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5600166444057317937527447 8400249666085976906291171)
        ·
          refine ⟨12600374499128965359436757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8400249666085976906291171 12600374499128965359436757)
          ·
            refine ⟨295321277323335125611799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 12600374499128965359436757 295321277323335125611799)
            ·
              refine ⟨442981915985002688417699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295321277323335125611799 442981915985002688417699)
              ·
                refine ⟨664472873977504032626549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442981915985002688417699 664472873977504032626549)
                ·
                  refine ⟨62294331935391003058739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 664472873977504032626549 62294331935391003058739)
                  ·
                    rfl

theorem cell21_272965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_272965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272965 prefixEnd_272965 := by exact prefixLift 272965
  have htrace : WordTrace (prefixWord ++ tailWord_272965) baseStart_272965 baseEnd_272965 := by
    simpa [prefixWord, tailWord_272965, baseEnd_272965] using wordTrace_append hprefix tailTrace_272965
  have hstable : (prefixWord ++ tailWord_272965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272965).length < 2 ^ (prefixWord ++ tailWord_272965).sum := by decide
  have hdescent : baseEnd_272965 < baseStart_272965 := by decide
  rcases family_descends (prefixWord ++ tailWord_272965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_272993 : List Nat := [1, 2, 3, 1, 1, 4, 2, 7]
def baseStart_272993 : Nat := 118140960795 + 272993 * 2 ^ 59
def prefixEnd_272993 : Nat := 4983230072969 + 3 ^ 40 * 272993 * 2
def baseEnd_272993 : Nat := 20766907305623058864005

theorem tailTrace_272993 : CollatzResearch.WordTrace tailWord_272993 prefixEnd_272993 20766907305623058864005 := by
  unfold tailWord_272993
  simp only [CollatzResearch.WordTrace]
  refine ⟨9956872700000459337623633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6637915133333639558415755 9956872700000459337623633)
  ·
    refine ⟨7467654525000344503217725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9956872700000459337623633 7467654525000344503217725)
    ·
      refine ⟨2800370446875129188706647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7467654525000344503217725 2800370446875129188706647)
      ·
        refine ⟨4200555670312693783059971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2800370446875129188706647 4200555670312693783059971)
        ·
          refine ⟨6300833505469040674589957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4200555670312693783059971 6300833505469040674589957)
          ·
            refine ⟨1181406282275445126485617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6300833505469040674589957 1181406282275445126485617)
            ·
              refine ⟨886054711706583844864213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1181406282275445126485617 886054711706583844864213)
              ·
                refine ⟨20766907305623058864005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 886054711706583844864213 20766907305623058864005)
                ·
                  rfl

theorem cell21_272993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 7].length) (baseStart_272993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_272993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_272993 prefixEnd_272993 := by exact prefixLift 272993
  have htrace : WordTrace (prefixWord ++ tailWord_272993) baseStart_272993 baseEnd_272993 := by
    simpa [prefixWord, tailWord_272993, baseEnd_272993] using wordTrace_append hprefix tailTrace_272993
  have hstable : (prefixWord ++ tailWord_272993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_272993).length < 2 ^ (prefixWord ++ tailWord_272993).sum := by decide
  have hdescent : baseEnd_272993 < baseStart_272993 := by decide
  rcases family_descends (prefixWord ++ tailWord_272993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273010 : List Nat := [3, 2, 1, 2, 5, 8]
def baseStart_273010 : Nat := 118140960795 + 273010 * 2 ^ 59
def prefixEnd_273010 : Nat := 4983230072969 + 3 ^ 40 * 273010 * 2
def baseEnd_273010 : Nat := 2307577835128923141061

theorem tailTrace_273010 : CollatzResearch.WordTrace tailWord_273010 prefixEnd_273010 2307577835128923141061 := by
  unfold tailWord_273010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2489373185234717810248121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6638328493959247493994989 2489373185234717810248121)
  ·
    refine ⟨1867029888926038357686091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2489373185234717810248121 1867029888926038357686091)
    ·
      refine ⟨2800544833389057536529137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1867029888926038357686091 2800544833389057536529137)
      ·
        refine ⟨2100408625041793152396853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2800544833389057536529137 2100408625041793152396853)
        ·
          refine ⟨196913308597668108037205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2100408625041793152396853 196913308597668108037205)
          ·
            refine ⟨2307577835128923141061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 196913308597668108037205 2307577835128923141061)
            ·
              rfl

theorem cell21_273010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 8].length) (baseStart_273010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273010 prefixEnd_273010 := by exact prefixLift 273010
  have htrace : WordTrace (prefixWord ++ tailWord_273010) baseStart_273010 baseEnd_273010 := by
    simpa [prefixWord, tailWord_273010, baseEnd_273010] using wordTrace_append hprefix tailTrace_273010
  have hstable : (prefixWord ++ tailWord_273010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273010).length < 2 ^ (prefixWord ++ tailWord_273010).sum := by decide
  have hdescent : baseEnd_273010 < baseStart_273010 := by decide
  rcases family_descends (prefixWord ++ tailWord_273010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273013 : List Nat := [1, 3, 4, 2, 2, 1, 2, 2, 4]
def baseStart_273013 : Nat := 118140960795 + 273013 * 2 ^ 59
def prefixEnd_273013 : Nat := 4983230072969 + 3 ^ 40 * 273013 * 2
def baseEnd_273013 : Nat := 62305286189353586258641

theorem tailTrace_273013 : CollatzResearch.WordTrace tailWord_273013 prefixEnd_273013 62305286189353586258641 := by
  unfold tailWord_273013
  simp only [CollatzResearch.WordTrace]
  refine ⟨9957602159928002753351693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6638401439952001835567795 9957602159928002753351693)
  ·
    refine ⟨3734100809973001032506885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9957602159928002753351693 3734100809973001032506885)
    ·
      refine ⟨700143901869937693595041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3734100809973001032506885 700143901869937693595041)
      ·
        refine ⟨525107926402453270196281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 700143901869937693595041 525107926402453270196281)
        ·
          refine ⟨393830944801839952647211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525107926402453270196281 393830944801839952647211)
          ·
            refine ⟨590746417202759928970817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393830944801839952647211 590746417202759928970817)
            ·
              refine ⟨443059812902069946728113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590746417202759928970817 443059812902069946728113)
              ·
                refine ⟨332294859676552460046085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443059812902069946728113 332294859676552460046085)
                ·
                  refine ⟨62305286189353586258641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332294859676552460046085 62305286189353586258641)
                  ·
                    rfl

theorem cell21_273013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_273013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273013 prefixEnd_273013 := by exact prefixLift 273013
  have htrace : WordTrace (prefixWord ++ tailWord_273013) baseStart_273013 baseEnd_273013 := by
    simpa [prefixWord, tailWord_273013, baseEnd_273013] using wordTrace_append hprefix tailTrace_273013
  have hstable : (prefixWord ++ tailWord_273013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273013).length < 2 ^ (prefixWord ++ tailWord_273013).sum := by decide
  have hdescent : baseEnd_273013 < baseStart_273013 := by decide
  rcases family_descends (prefixWord ++ tailWord_273013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273114 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_273114 : Nat := 118140960795 + 273114 * 2 ^ 59
def prefixEnd_273114 : Nat := 4983230072969 + 3 ^ 40 * 273114 * 2
def baseEnd_273114 : Nat := 62328335765399855075101

theorem tailTrace_273114 : CollatzResearch.WordTrace tailWord_273114 prefixEnd_273114 62328335765399855075101 := by
  unfold tailWord_273114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490321483140524250694599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6640857288374731335185597 2490321483140524250694599)
  ·
    refine ⟨3735482224710786376041899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2490321483140524250694599 3735482224710786376041899)
    ·
      refine ⟨5603223337066179564062849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3735482224710786376041899 5603223337066179564062849)
      ·
        refine ⟨4202417502799634673047137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5603223337066179564062849 4202417502799634673047137)
        ·
          refine ⟨3151813127099726004785353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4202417502799634673047137 3151813127099726004785353)
          ·
            refine ⟨2363859845324794503589015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3151813127099726004785353 2363859845324794503589015)
            ·
              refine ⟨3545789767987191755383523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2363859845324794503589015 3545789767987191755383523)
              ·
                refine ⟨5318684651980787633075285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3545789767987191755383523 5318684651980787633075285)
                ·
                  refine ⟨62328335765399855075101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5318684651980787633075285 62328335765399855075101)
                  ·
                    rfl

theorem cell21_273114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_273114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273114 prefixEnd_273114 := by exact prefixLift 273114
  have htrace : WordTrace (prefixWord ++ tailWord_273114) baseStart_273114 baseEnd_273114 := by
    simpa [prefixWord, tailWord_273114, baseEnd_273114] using wordTrace_append hprefix tailTrace_273114
  have hstable : (prefixWord ++ tailWord_273114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273114).length < 2 ^ (prefixWord ++ tailWord_273114).sum := by decide
  have hdescent : baseEnd_273114 < baseStart_273114 := by decide
  rcases family_descends (prefixWord ++ tailWord_273114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273140 : List Nat := [2, 6, 1, 1, 3, 1, 2, 1, 4]
def baseStart_273140 : Nat := 118140960795 + 273140 * 2 ^ 59
def prefixEnd_273140 : Nat := 4983230072969 + 3 ^ 40 * 273140 * 2
def baseEnd_273140 : Nat := 62334269319629587641715

theorem tailTrace_273140 : CollatzResearch.WordTrace tailWord_273140 prefixEnd_273140 62334269319629587641715 := by
  unfold tailWord_273140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981117115233951721612437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6641489486978602295483249 4981117115233951721612437)
  ·
    refine ⟨233489864776591486950583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4981117115233951721612437 233489864776591486950583)
    ·
      refine ⟨350234797164887230425875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233489864776591486950583 350234797164887230425875)
      ·
        refine ⟨525352195747330845638813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350234797164887230425875 525352195747330845638813)
        ·
          refine ⟨197007073405249067114555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 525352195747330845638813 197007073405249067114555)
          ·
            refine ⟨295510610107873600671833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197007073405249067114555 295510610107873600671833)
            ·
              refine ⟨221632957580905200503875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295510610107873600671833 221632957580905200503875)
              ·
                refine ⟨332449436371357800755813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221632957580905200503875 332449436371357800755813)
                ·
                  refine ⟨62334269319629587641715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332449436371357800755813 62334269319629587641715)
                  ·
                    rfl

theorem cell21_273140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_273140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273140 prefixEnd_273140 := by exact prefixLift 273140
  have htrace : WordTrace (prefixWord ++ tailWord_273140) baseStart_273140 baseEnd_273140 := by
    simpa [prefixWord, tailWord_273140, baseEnd_273140] using wordTrace_append hprefix tailTrace_273140
  have hstable : (prefixWord ++ tailWord_273140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273140).length < 2 ^ (prefixWord ++ tailWord_273140).sum := by decide
  have hdescent : baseEnd_273140 < baseStart_273140 := by decide
  rcases family_descends (prefixWord ++ tailWord_273140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273148 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 4]
def baseStart_273148 : Nat := 118140960795 + 273148 * 2 ^ 59
def prefixEnd_273148 : Nat := 4983230072969 + 3 ^ 40 * 273148 * 2
def baseEnd_273148 : Nat := 62336095028623351508365

theorem tailTrace_273148 : CollatzResearch.WordTrace tailWord_273148 prefixEnd_273148 62336095028623351508365 := by
  unfold tailWord_273148
  simp only [CollatzResearch.WordTrace]
  refine ⟨4981263007219460404758049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6641684009625947206344065 4981263007219460404758049)
  ·
    refine ⟨3735947255414595303568537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4981263007219460404758049 3735947255414595303568537)
    ·
      refine ⟨2801960441560946477676403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3735947255414595303568537 2801960441560946477676403)
      ·
        refine ⟨4202940662341419716514605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2801960441560946477676403 4202940662341419716514605)
        ·
          refine ⟨1576102748378032393692977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4202940662341419716514605 1576102748378032393692977)
          ·
            refine ⟨1182077061283524295269733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1576102748378032393692977 1182077061283524295269733)
            ·
              refine ⟨221639448990660805363075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1182077061283524295269733 221639448990660805363075)
              ·
                refine ⟨332459173485991208044613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221639448990660805363075 332459173485991208044613)
                ·
                  refine ⟨62336095028623351508365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332459173485991208044613 62336095028623351508365)
                  ·
                    rfl

theorem cell21_273148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_273148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273148 prefixEnd_273148 := by exact prefixLift 273148
  have htrace : WordTrace (prefixWord ++ tailWord_273148) baseStart_273148 baseEnd_273148 := by
    simpa [prefixWord, tailWord_273148, baseEnd_273148] using wordTrace_append hprefix tailTrace_273148
  have hstable : (prefixWord ++ tailWord_273148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273148).length < 2 ^ (prefixWord ++ tailWord_273148).sum := by decide
  have hdescent : baseEnd_273148 < baseStart_273148 := by decide
  rcases family_descends (prefixWord ++ tailWord_273148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273252 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 5]
def baseStart_273252 : Nat := 118140960795 + 273252 * 2 ^ 59
def prefixEnd_273252 : Nat := 4983230072969 + 3 ^ 40 * 273252 * 2
def baseEnd_273252 : Nat := 62359829245542281774819

theorem tailTrace_273252 : CollatzResearch.WordTrace tailWord_273252 prefixEnd_273252 62359829245542281774819 := by
  unfold tailWord_273252
  simp only [CollatzResearch.WordTrace]
  refine ⟨4983159603031073285651005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6644212804041431047534673 4983159603031073285651005)
  ·
    refine ⟨1868684851136652482119127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4983159603031073285651005 1868684851136652482119127)
    ·
      refine ⟨2803027276704978723178691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1868684851136652482119127 2803027276704978723178691)
      ·
        refine ⟨4204540915057468084768037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2803027276704978723178691 4204540915057468084768037)
        ·
          refine ⟨788351421573275265894007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4204540915057468084768037 788351421573275265894007)
          ·
            refine ⟨1182527132359912898841011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 788351421573275265894007 1182527132359912898841011)
            ·
              refine ⟨1773790698539869348261517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1182527132359912898841011 1773790698539869348261517)
              ·
                refine ⟨665171511952451005598069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1773790698539869348261517 665171511952451005598069)
                ·
                  refine ⟨62359829245542281774819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 665171511952451005598069 62359829245542281774819)
                  ·
                    rfl

theorem cell21_273252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_273252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273252 prefixEnd_273252 := by exact prefixLift 273252
  have htrace : WordTrace (prefixWord ++ tailWord_273252) baseStart_273252 baseEnd_273252 := by
    simpa [prefixWord, tailWord_273252, baseEnd_273252] using wordTrace_append hprefix tailTrace_273252
  have hstable : (prefixWord ++ tailWord_273252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273252).length < 2 ^ (prefixWord ++ tailWord_273252).sum := by decide
  have hdescent : baseEnd_273252 < baseStart_273252 := by decide
  rcases family_descends (prefixWord ++ tailWord_273252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273314 : List Nat := [3, 3, 1, 2, 2, 2, 2, 6]
def baseStart_273314 : Nat := 118140960795 + 273314 * 2 ^ 59
def prefixEnd_273314 : Nat := 4983230072969 + 3 ^ 40 * 273314 * 2
def baseEnd_273314 : Nat := 20791326163414650580453

theorem tailTrace_273314 : CollatzResearch.WordTrace tailWord_273314 prefixEnd_273314 20791326163414650580453 := by
  unfold tailWord_273314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2492145132959382790014749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6645720354558354106705997 2492145132959382790014749)
  ·
    refine ⟨934554424859768546255531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2492145132959382790014749 934554424859768546255531)
    ·
      refine ⟨1401831637289652819383297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 934554424859768546255531 1401831637289652819383297)
      ·
        refine ⟨1051373727967239614537473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1401831637289652819383297 1051373727967239614537473)
        ·
          refine ⟨788530295975429710903105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1051373727967239614537473 788530295975429710903105)
          ·
            refine ⟨591397721981572283177329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788530295975429710903105 591397721981572283177329)
            ·
              refine ⟨443548291486179212382997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591397721981572283177329 443548291486179212382997)
              ·
                refine ⟨20791326163414650580453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 443548291486179212382997 20791326163414650580453)
                ·
                  rfl

theorem cell21_273314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_273314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273314 prefixEnd_273314 := by exact prefixLift 273314
  have htrace : WordTrace (prefixWord ++ tailWord_273314) baseStart_273314 baseEnd_273314 := by
    simpa [prefixWord, tailWord_273314, baseEnd_273314] using wordTrace_append hprefix tailTrace_273314
  have hstable : (prefixWord ++ tailWord_273314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273314).length < 2 ^ (prefixWord ++ tailWord_273314).sum := by decide
  have hdescent : baseEnd_273314 < baseStart_273314 := by decide
  rcases family_descends (prefixWord ++ tailWord_273314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273359 : List Nat := [1, 1, 2, 1, 1, 7, 2, 2, 4]
def baseStart_273359 : Nat := 118140960795 + 273359 * 2 ^ 59
def prefixEnd_273359 : Nat := 4983230072969 + 3 ^ 40 * 273359 * 2
def baseEnd_273359 : Nat := 62384248103333873491267

theorem tailTrace_273359 : CollatzResearch.WordTrace tailWord_273359 prefixEnd_273359 62384248103333873491267 := by
  unfold tailWord_273359
  simp only [CollatzResearch.WordTrace]
  refine ⟨9970221816674503845447131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6646814544449669230298087 9970221816674503845447131)
  ·
    refine ⟨14955332725011755768170697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9970221816674503845447131 14955332725011755768170697)
    ·
      refine ⟨11216499543758816826128023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14955332725011755768170697 11216499543758816826128023)
      ·
        refine ⟨16824749315638225239192035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11216499543758816826128023 16824749315638225239192035)
        ·
          refine ⟨25237123973457337858788053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16824749315638225239192035 25237123973457337858788053)
          ·
            refine ⟨591495093127906356065345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 25237123973457337858788053 591495093127906356065345)
            ·
              refine ⟨443621319845929767049009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591495093127906356065345 443621319845929767049009)
              ·
                refine ⟨332715989884447325286757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443621319845929767049009 332715989884447325286757)
                ·
                  refine ⟨62384248103333873491267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332715989884447325286757 62384248103333873491267)
                  ·
                    rfl

theorem cell21_273359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 2, 4].length) (baseStart_273359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273359 prefixEnd_273359 := by exact prefixLift 273359
  have htrace : WordTrace (prefixWord ++ tailWord_273359) baseStart_273359 baseEnd_273359 := by
    simpa [prefixWord, tailWord_273359, baseEnd_273359] using wordTrace_append hprefix tailTrace_273359
  have hstable : (prefixWord ++ tailWord_273359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273359).length < 2 ^ (prefixWord ++ tailWord_273359).sum := by decide
  have hdescent : baseEnd_273359 < baseStart_273359 := by decide
  rcases family_descends (prefixWord ++ tailWord_273359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273362 : List Nat := [3, 2, 2, 3, 1, 2, 1, 4, 3]
def baseStart_273362 : Nat := 118140960795 + 273362 * 2 ^ 59
def prefixEnd_273362 : Nat := 4983230072969 + 3 ^ 40 * 273362 * 2
def baseEnd_273362 : Nat := 62384932744206534941261

theorem tailTrace_273362 : CollatzResearch.WordTrace tailWord_273362 prefixEnd_273362 62384932744206534941261 := by
  unfold tailWord_273362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2492582808915908839451585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6646887490442423571870893 2492582808915908839451585)
  ·
    refine ⟨1869437106686931629588689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2492582808915908839451585 1869437106686931629588689)
    ·
      refine ⟨1402077830015198722191517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1869437106686931629588689 1402077830015198722191517)
      ·
        refine ⟨525779186255699520821819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1402077830015198722191517 525779186255699520821819)
        ·
          refine ⟨788668779383549281232729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525779186255699520821819 788668779383549281232729)
          ·
            refine ⟨591501584537661960924547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788668779383549281232729 591501584537661960924547)
            ·
              refine ⟨887252376806492941386821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591501584537661960924547 887252376806492941386821)
              ·
                refine ⟨166359820651217426510029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 887252376806492941386821 166359820651217426510029)
                ·
                  refine ⟨62384932744206534941261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166359820651217426510029 62384932744206534941261)
                  ·
                    rfl

theorem cell21_273362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_273362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273362 prefixEnd_273362 := by exact prefixLift 273362
  have htrace : WordTrace (prefixWord ++ tailWord_273362) baseStart_273362 baseEnd_273362 := by
    simpa [prefixWord, tailWord_273362, baseEnd_273362] using wordTrace_append hprefix tailTrace_273362
  have hstable : (prefixWord ++ tailWord_273362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273362).length < 2 ^ (prefixWord ++ tailWord_273362).sum := by decide
  have hdescent : baseEnd_273362 < baseStart_273362 := by decide
  rcases family_descends (prefixWord ++ tailWord_273362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273410 : List Nat := [3, 4, 1, 3, 1, 2, 1, 2, 4]
def baseStart_273410 : Nat := 118140960795 + 273410 * 2 ^ 59
def prefixEnd_273410 : Nat := 4983230072969 + 3 ^ 40 * 273410 * 2
def baseEnd_273410 : Nat := 62395886998169118141163

theorem tailTrace_273410 : CollatzResearch.WordTrace tailWord_273410 prefixEnd_273410 62395886998169118141163 := by
  unfold tailWord_273410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2493020484872434888888421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6648054626326493037035789 2493020484872434888888421)
  ·
    refine ⟨467441340913581541666579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2493020484872434888888421 467441340913581541666579)
    ·
      refine ⟨701162011370372312499869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 467441340913581541666579 701162011370372312499869)
      ·
        refine ⟨262935754263889617187451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 701162011370372312499869 262935754263889617187451)
        ·
          refine ⟨394403631395834425781177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262935754263889617187451 394403631395834425781177)
          ·
            refine ⟨295802723546875819335883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394403631395834425781177 295802723546875819335883)
            ·
              refine ⟨443704085320313729003825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295802723546875819335883 443704085320313729003825)
              ·
                refine ⟨332778063990235296752869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443704085320313729003825 332778063990235296752869)
                ·
                  refine ⟨62395886998169118141163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 332778063990235296752869 62395886998169118141163)
                  ·
                    rfl

theorem cell21_273410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_273410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273410 prefixEnd_273410 := by exact prefixLift 273410
  have htrace : WordTrace (prefixWord ++ tailWord_273410) baseStart_273410 baseEnd_273410 := by
    simpa [prefixWord, tailWord_273410, baseEnd_273410] using wordTrace_append hprefix tailTrace_273410
  have hstable : (prefixWord ++ tailWord_273410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273410).length < 2 ^ (prefixWord ++ tailWord_273410).sum := by decide
  have hdescent : baseEnd_273410 < baseStart_273410 := by decide
  rcases family_descends (prefixWord ++ tailWord_273410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273525 : List Nat := [1, 3, 4, 3, 10]
def baseStart_273525 : Nat := 118140960795 + 273525 * 2 ^ 59
def prefixEnd_273525 : Nat := 4983230072969 + 3 ^ 40 * 273525 * 2
def baseEnd_273525 : Nat := 770643599567339181781

theorem tailTrace_273525 : CollatzResearch.WordTrace tailWord_273525 prefixEnd_273525 770643599567339181781 := by
  unfold tailWord_273525
  simp only [CollatzResearch.WordTrace]
  refine ⟨9976276334073114195990029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6650850889382076130660019 9976276334073114195990029)
  ·
    refine ⟨3741103625277417823496261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9976276334073114195990029 3741103625277417823496261)
    ·
      refine ⟨701456929739515841905549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3741103625277417823496261 701456929739515841905549)
      ·
        refine ⟨263046348652318440714581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 701456929739515841905549 263046348652318440714581)
        ·
          refine ⟨770643599567339181781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 263046348652318440714581 770643599567339181781)
          ·
            rfl

theorem cell21_273525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 10].length) (baseStart_273525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273525 prefixEnd_273525 := by exact prefixLift 273525
  have htrace : WordTrace (prefixWord ++ tailWord_273525) baseStart_273525 baseEnd_273525 := by
    simpa [prefixWord, tailWord_273525, baseEnd_273525] using wordTrace_append hprefix tailTrace_273525
  have hstable : (prefixWord ++ tailWord_273525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273525).length < 2 ^ (prefixWord ++ tailWord_273525).sum := by decide
  have hdescent : baseEnd_273525 < baseStart_273525 := by decide
  rcases family_descends (prefixWord ++ tailWord_273525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273539 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 5]
def baseStart_273539 : Nat := 118140960795 + 273539 * 2 ^ 59
def prefixEnd_273539 : Nat := 4983230072969 + 3 ^ 40 * 273539 * 2
def baseEnd_273539 : Nat := 62425326555693560490899

theorem tailTrace_273539 : CollatzResearch.WordTrace tailWord_273539 prefixEnd_273539 62425326555693560490899 := by
  unfold tailWord_273539
  simp only [CollatzResearch.WordTrace]
  refine ⟨9976786956022394586999671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6651191304014929724666447 9976786956022394586999671)
  ·
    refine ⟨14965180434033591880499507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9976786956022394586999671 14965180434033591880499507)
    ·
      refine ⟨22447770651050387820749261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14965180434033591880499507 22447770651050387820749261)
      ·
        refine ⟨8417913994143895432780973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22447770651050387820749261 8417913994143895432780973)
        ·
          refine ⟨3156717747803960787292865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8417913994143895432780973 3156717747803960787292865)
          ·
            refine ⟨2367538310852970590469649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3156717747803960787292865 2367538310852970590469649)
            ·
              refine ⟨1775653733139727942852237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2367538310852970590469649 1775653733139727942852237)
              ·
                refine ⟨665870149927397978569589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1775653733139727942852237 665870149927397978569589)
                ·
                  refine ⟨62425326555693560490899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 665870149927397978569589 62425326555693560490899)
                  ·
                    rfl

theorem cell21_273539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_273539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273539 prefixEnd_273539 := by exact prefixLift 273539
  have htrace : WordTrace (prefixWord ++ tailWord_273539) baseStart_273539 baseEnd_273539 := by
    simpa [prefixWord, tailWord_273539, baseEnd_273539] using wordTrace_append hprefix tailTrace_273539
  have hstable : (prefixWord ++ tailWord_273539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273539).length < 2 ^ (prefixWord ++ tailWord_273539).sum := by decide
  have hdescent : baseEnd_273539 < baseStart_273539 := by decide
  rcases family_descends (prefixWord ++ tailWord_273539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273573 : List Nat := [1, 3, 1, 2, 1, 5, 2, 3, 3]
def baseStart_273573 : Nat := 118140960795 + 273573 * 2 ^ 59
def prefixEnd_273573 : Nat := 4983230072969 + 3 ^ 40 * 273573 * 2
def baseEnd_273573 : Nat := 62433085818917056924163

theorem tailTrace_273573 : CollatzResearch.WordTrace tailWord_273573 prefixEnd_273573 62433085818917056924163 := by
  unfold tailWord_273573
  simp only [CollatzResearch.WordTrace]
  refine ⟨9978027037899218393737373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6652018025266145595824915 9978027037899218393737373)
  ·
    refine ⟨3741760139212206897651515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9978027037899218393737373 3741760139212206897651515)
    ·
      refine ⟨5612640208818310346477273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3741760139212206897651515 5612640208818310346477273)
      ·
        refine ⟨4209480156613732759857955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5612640208818310346477273 4209480156613732759857955)
        ·
          refine ⟨6314220234920599139786933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4209480156613732759857955 6314220234920599139786933)
          ·
            refine ⟨591958147023806169355025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6314220234920599139786933 591958147023806169355025)
            ·
              refine ⟨443968610267854627016269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 591958147023806169355025 443968610267854627016269)
              ·
                refine ⟨166488228850445485131101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 443968610267854627016269 166488228850445485131101)
                ·
                  refine ⟨62433085818917056924163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166488228850445485131101 62433085818917056924163)
                  ·
                    rfl

theorem cell21_273573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 3, 3].length) (baseStart_273573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273573 prefixEnd_273573 := by exact prefixLift 273573
  have htrace : WordTrace (prefixWord ++ tailWord_273573) baseStart_273573 baseEnd_273573 := by
    simpa [prefixWord, tailWord_273573, baseEnd_273573] using wordTrace_append hprefix tailTrace_273573
  have hstable : (prefixWord ++ tailWord_273573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273573).length < 2 ^ (prefixWord ++ tailWord_273573).sum := by decide
  have hdescent : baseEnd_273573 < baseStart_273573 := by decide
  rcases family_descends (prefixWord ++ tailWord_273573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273646 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 6]
def baseStart_273646 : Nat := 118140960795 + 273646 * 2 ^ 59
def prefixEnd_273646 : Nat := 4983230072969 + 3 ^ 40 * 273646 * 2
def baseEnd_273646 : Nat := 62449745413485152207347

theorem tailTrace_273646 : CollatzResearch.WordTrace tailWord_273646 prefixEnd_273646 62449745413485152207347 := by
  unfold tailWord_273646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1247586195829343982643099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6653793044423167907429861 1247586195829343982643099)
  ·
    refine ⟨1871379293744015973964649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1247586195829343982643099 1871379293744015973964649)
    ·
      refine ⟨1403534470308011980473487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1871379293744015973964649 1403534470308011980473487)
      ·
        refine ⟨2105301705462017970710231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1403534470308011980473487 2105301705462017970710231)
        ·
          refine ⟨3157952558193026956065347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2105301705462017970710231 3157952558193026956065347)
          ·
            refine ⟨4736928837289540434098021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3157952558193026956065347 4736928837289540434098021)
            ·
              refine ⟨888174156991788831393379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4736928837289540434098021 888174156991788831393379)
              ·
                refine ⟨1332261235487683247090069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888174156991788831393379 1332261235487683247090069)
                ·
                  refine ⟨62449745413485152207347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1332261235487683247090069 62449745413485152207347)
                  ·
                    rfl

theorem cell21_273646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_273646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273646 prefixEnd_273646 := by exact prefixLift 273646
  have htrace : WordTrace (prefixWord ++ tailWord_273646) baseStart_273646 baseEnd_273646 := by
    simpa [prefixWord, tailWord_273646, baseEnd_273646] using wordTrace_append hprefix tailTrace_273646
  have hstable : (prefixWord ++ tailWord_273646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273646).length < 2 ^ (prefixWord ++ tailWord_273646).sum := by decide
  have hdescent : baseEnd_273646 < baseStart_273646 := by decide
  rcases family_descends (prefixWord ++ tailWord_273646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273652 : List Nat := [2, 6, 1, 2, 1, 1, 2, 6]
def baseStart_273652 : Nat := 118140960795 + 273652 * 2 ^ 59
def prefixEnd_273652 : Nat := 4983230072969 + 3 ^ 40 * 273652 * 2
def baseEnd_273652 : Nat := 20817038231743491702445

theorem tailTrace_273652 : CollatzResearch.WordTrace tailWord_273652 prefixEnd_273652 20817038231743491702445 := by
  unfold tailWord_273652
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990454202306507442931605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6653938936408676590575473 4990454202306507442931605)
  ·
    refine ⟨233927540733117536387419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4990454202306507442931605 233927540733117536387419)
    ·
      refine ⟨350891311099676304581129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233927540733117536387419 350891311099676304581129)
      ·
        refine ⟨263168483324757228435847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 350891311099676304581129 263168483324757228435847)
        ·
          refine ⟨394752724987135842653771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263168483324757228435847 394752724987135842653771)
          ·
            refine ⟨592129087480703763980657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394752724987135842653771 592129087480703763980657)
            ·
              refine ⟨444096815610527822985493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592129087480703763980657 444096815610527822985493)
              ·
                refine ⟨20817038231743491702445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 444096815610527822985493 20817038231743491702445)
                ·
                  rfl

theorem cell21_273652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 6].length) (baseStart_273652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273652 prefixEnd_273652 := by exact prefixLift 273652
  have htrace : WordTrace (prefixWord ++ tailWord_273652) baseStart_273652 baseEnd_273652 := by
    simpa [prefixWord, tailWord_273652, baseEnd_273652] using wordTrace_append hprefix tailTrace_273652
  have hstable : (prefixWord ++ tailWord_273652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273652).length < 2 ^ (prefixWord ++ tailWord_273652).sum := by decide
  have hdescent : baseEnd_273652 < baseStart_273652 := by decide
  rcases family_descends (prefixWord ++ tailWord_273652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273663 : List Nat := [1, 1, 2, 2, 1, 5, 4, 1, 4]
def baseStart_273663 : Nat := 118140960795 + 273663 * 2 ^ 59
def prefixEnd_273663 : Nat := 4983230072969 + 3 ^ 40 * 273663 * 2
def baseEnd_273663 : Nat := 62453625045096900423979

theorem tailTrace_273663 : CollatzResearch.WordTrace tailWord_273663 prefixEnd_273663 62453625045096900423979 := by
  unfold tailWord_273663
  simp only [CollatzResearch.WordTrace]
  refine ⟨9981309607573163764513643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6654206405048775843009095 9981309607573163764513643)
  ·
    refine ⟨14971964411359745646770465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9981309607573163764513643 14971964411359745646770465)
    ·
      refine ⟨11228973308519809235077849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14971964411359745646770465 11228973308519809235077849)
      ·
        refine ⟨8421729981389856926308387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11228973308519809235077849 8421729981389856926308387)
        ·
          refine ⟨12632594972084785389462581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8421729981389856926308387 12632594972084785389462581)
          ·
            refine ⟨1184305778632948630262117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12632594972084785389462581 1184305778632948630262117)
            ·
              refine ⟨222057333493677868174147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1184305778632948630262117 222057333493677868174147)
              ·
                refine ⟨333086000240516802261221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222057333493677868174147 333086000240516802261221)
                ·
                  refine ⟨62453625045096900423979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 333086000240516802261221 62453625045096900423979)
                  ·
                    rfl

theorem cell21_273663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 4, 1, 4].length) (baseStart_273663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273663 prefixEnd_273663 := by exact prefixLift 273663
  have htrace : WordTrace (prefixWord ++ tailWord_273663) baseStart_273663 baseEnd_273663 := by
    simpa [prefixWord, tailWord_273663, baseEnd_273663] using wordTrace_append hprefix tailTrace_273663
  have hstable : (prefixWord ++ tailWord_273663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273663).length < 2 ^ (prefixWord ++ tailWord_273663).sum := by decide
  have hdescent : baseEnd_273663 < baseStart_273663 := by decide
  rcases family_descends (prefixWord ++ tailWord_273663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273694 : List Nat := [4, 3, 2, 1, 2, 9]
def baseStart_273694 : Nat := 118140960795 + 273694 * 2 ^ 59
def prefixEnd_273694 : Nat := 4983230072969 + 3 ^ 40 * 273694 * 2
def baseEnd_273694 : Nat := 2313359246942508718787

theorem tailTrace_273694 : CollatzResearch.WordTrace tailWord_273694 prefixEnd_273694 2313359246942508718787 := by
  unfold tailWord_273694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1247805033807607007361517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6654960180307237372594757 1247805033807607007361517)
  ·
    refine ⟨467926887677852627760569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1247805033807607007361517 467926887677852627760569)
    ·
      refine ⟨350945165758389470820427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 467926887677852627760569 350945165758389470820427)
      ·
        refine ⟨526417748637584206230641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350945165758389470820427 526417748637584206230641)
        ·
          refine ⟨394813311478188154672981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526417748637584206230641 394813311478188154672981)
          ·
            refine ⟨2313359246942508718787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 394813311478188154672981 2313359246942508718787)
            ·
              rfl

theorem cell21_273694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 9].length) (baseStart_273694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273694 prefixEnd_273694 := by exact prefixLift 273694
  have htrace : WordTrace (prefixWord ++ tailWord_273694) baseStart_273694 baseEnd_273694 := by
    simpa [prefixWord, tailWord_273694, baseEnd_273694] using wordTrace_append hprefix tailTrace_273694
  have hstable : (prefixWord ++ tailWord_273694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273694).length < 2 ^ (prefixWord ++ tailWord_273694).sum := by decide
  have hdescent : baseEnd_273694 < baseStart_273694 := by decide
  rcases family_descends (prefixWord ++ tailWord_273694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273722 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_273722 : Nat := 118140960795 + 273722 * 2 ^ 59
def prefixEnd_273722 : Nat := 4983230072969 + 3 ^ 40 * 273722 * 2
def baseEnd_273722 : Nat := 62467089648925908940525

theorem tailTrace_273722 : CollatzResearch.WordTrace tailWord_273722 prefixEnd_273722 62467089648925908940525 := by
  unfold tailWord_273722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495865378589854210227855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6655641009572944560607613 2495865378589854210227855)
  ·
    refine ⟨3743798067884781315341783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2495865378589854210227855 3743798067884781315341783)
    ·
      refine ⟨5615697101827171973012675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3743798067884781315341783 5615697101827171973012675)
      ·
        refine ⟨8423545652740757959519013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5615697101827171973012675 8423545652740757959519013)
        ·
          refine ⟨1579414809888892117409815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8423545652740757959519013 1579414809888892117409815)
          ·
            refine ⟨2369122214833338176114723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1579414809888892117409815 2369122214833338176114723)
            ·
              refine ⟨3553683322250007264172085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2369122214833338176114723 3553683322250007264172085)
              ·
                refine ⟨333157811460938181016133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3553683322250007264172085 333157811460938181016133)
                ·
                  refine ⟨62467089648925908940525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 333157811460938181016133 62467089648925908940525)
                  ·
                    rfl

theorem cell21_273722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_273722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273722 prefixEnd_273722 := by exact prefixLift 273722
  have htrace : WordTrace (prefixWord ++ tailWord_273722) baseStart_273722 baseEnd_273722 := by
    simpa [prefixWord, tailWord_273722, baseEnd_273722] using wordTrace_append hprefix tailTrace_273722
  have hstable : (prefixWord ++ tailWord_273722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273722).length < 2 ^ (prefixWord ++ tailWord_273722).sum := by decide
  have hdescent : baseEnd_273722 < baseStart_273722 := by decide
  rcases family_descends (prefixWord ++ tailWord_273722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273725 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 5]
def baseStart_273725 : Nat := 118140960795 + 273725 * 2 ^ 59
def prefixEnd_273725 : Nat := 4983230072969 + 3 ^ 40 * 273725 * 2
def baseEnd_273725 : Nat := 62467774289798570390519

theorem tailTrace_273725 : CollatzResearch.WordTrace tailWord_273725 prefixEnd_273725 62467774289798570390519 := by
  unfold tailWord_273725
  simp only [CollatzResearch.WordTrace]
  refine ⟨9983570933348548353270629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6655713955565698902180419 9983570933348548353270629)
  ·
    refine ⟨1871919550002852816238243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9983570933348548353270629 1871919550002852816238243)
    ·
      refine ⟨2807879325004279224357365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1871919550002852816238243 2807879325004279224357365)
      ·
        refine ⟨263238686719151177283503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2807879325004279224357365 263238686719151177283503)
        ·
          refine ⟨394858030078726765925255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263238686719151177283503 394858030078726765925255)
          ·
            refine ⟨592287045118090148887883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394858030078726765925255 592287045118090148887883)
            ·
              refine ⟨888430567677135223331825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592287045118090148887883 888430567677135223331825)
              ·
                refine ⟨666322925757851417498869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 888430567677135223331825 666322925757851417498869)
                ·
                  refine ⟨62467774289798570390519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 666322925757851417498869 62467774289798570390519)
                  ·
                    rfl

theorem cell21_273725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_273725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273725 prefixEnd_273725 := by exact prefixLift 273725
  have htrace : WordTrace (prefixWord ++ tailWord_273725) baseStart_273725 baseEnd_273725 := by
    simpa [prefixWord, tailWord_273725, baseEnd_273725] using wordTrace_append hprefix tailTrace_273725
  have hstable : (prefixWord ++ tailWord_273725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273725).length < 2 ^ (prefixWord ++ tailWord_273725).sum := by decide
  have hdescent : baseEnd_273725 < baseStart_273725 := by decide
  rcases family_descends (prefixWord ++ tailWord_273725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273832 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 4]
def baseStart_273832 : Nat := 118140960795 + 273832 * 2 ^ 59
def prefixEnd_273832 : Nat := 4983230072969 + 3 ^ 40 * 273832 * 2
def baseEnd_273832 : Nat := 62492193147590162106967

theorem tailTrace_273832 : CollatzResearch.WordTrace tailWord_273832 prefixEnd_273832 62492193147590162106967 := by
  unfold tailWord_273832
  simp only [CollatzResearch.WordTrace]
  refine ⟨4993736771980452813707875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6658315695973937084943833 4993736771980452813707875)
  ·
    refine ⟨7490605157970679220561813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4993736771980452813707875 7490605157970679220561813)
    ·
      refine ⟨351122116779875588463835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7490605157970679220561813 351122116779875588463835)
      ·
        refine ⟨526683175169813382695753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351122116779875588463835 526683175169813382695753)
        ·
          refine ⟨395012381377360037021815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526683175169813382695753 395012381377360037021815)
          ·
            refine ⟨592518572066040055532723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395012381377360037021815 592518572066040055532723)
            ·
              refine ⟨888777858099060083299085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592518572066040055532723 888777858099060083299085)
              ·
                refine ⟨333291696787147531237157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 888777858099060083299085 333291696787147531237157)
                ·
                  refine ⟨62492193147590162106967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 333291696787147531237157 62492193147590162106967)
                  ·
                    rfl

theorem cell21_273832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_273832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273832 prefixEnd_273832 := by exact prefixLift 273832
  have htrace : WordTrace (prefixWord ++ tailWord_273832) baseStart_273832 baseEnd_273832 := by
    simpa [prefixWord, tailWord_273832, baseEnd_273832] using wordTrace_append hprefix tailTrace_273832
  have hstable : (prefixWord ++ tailWord_273832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273832).length < 2 ^ (prefixWord ++ tailWord_273832).sum := by decide
  have hdescent : baseEnd_273832 < baseStart_273832 := by decide
  rcases family_descends (prefixWord ++ tailWord_273832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273905 : List Nat := [1, 2, 2, 2, 3, 3, 3, 5]
def baseStart_273905 : Nat := 118140960795 + 273905 * 2 ^ 59
def prefixEnd_273905 : Nat := 4983230072969 + 3 ^ 40 * 273905 * 2
def baseEnd_273905 : Nat := 20836284247386085796717

theorem tailTrace_273905 : CollatzResearch.WordTrace tailWord_273905 prefixEnd_273905 20836284247386085796717 := by
  unfold tailWord_273905
  simp only [CollatzResearch.WordTrace]
  refine ⟨9990136072696439094823169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6660090715130959396548779 9990136072696439094823169)
  ·
    refine ⟨7492602054522329321117377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9990136072696439094823169 7492602054522329321117377)
    ·
      refine ⟨5619451540891746990838033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7492602054522329321117377 5619451540891746990838033)
      ·
        refine ⟨4214588655668810243128525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5619451540891746990838033 4214588655668810243128525)
        ·
          refine ⟨1580470745875803841173197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4214588655668810243128525 1580470745875803841173197)
          ·
            refine ⟨592676529703426440439949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1580470745875803841173197 592676529703426440439949)
            ·
              refine ⟨222253698638784915164981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 592676529703426440439949 222253698638784915164981)
              ·
                refine ⟨20836284247386085796717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222253698638784915164981 20836284247386085796717)
                ·
                  rfl

theorem cell21_273905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 5].length) (baseStart_273905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273905 prefixEnd_273905 := by exact prefixLift 273905
  have htrace : WordTrace (prefixWord ++ tailWord_273905) baseStart_273905 baseEnd_273905 := by
    simpa [prefixWord, tailWord_273905, baseEnd_273905] using wordTrace_append hprefix tailTrace_273905
  have hstable : (prefixWord ++ tailWord_273905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273905).length < 2 ^ (prefixWord ++ tailWord_273905).sum := by decide
  have hdescent : baseEnd_273905 < baseStart_273905 := by decide
  rcases family_descends (prefixWord ++ tailWord_273905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_273981 : List Nat := [1, 4, 1, 3, 3, 2, 7]
def baseStart_273981 : Nat := 118140960795 + 273981 * 2 ^ 59
def prefixEnd_273981 : Nat := 4983230072969 + 3 ^ 40 * 273981 * 2
def baseEnd_273981 : Nat := 6947355219733223791481

theorem tailTrace_273981 : CollatzResearch.WordTrace tailWord_273981 prefixEnd_273981 6947355219733223791481 := by
  unfold tailWord_273981
  simp only [CollatzResearch.WordTrace]
  refine ⟨9992908020421104074589797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6661938680280736049726531 9992908020421104074589797)
  ·
    refine ⟨1873670253828957013985587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9992908020421104074589797 1873670253828957013985587)
    ·
      refine ⟨2810505380743435520978381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873670253828957013985587 2810505380743435520978381)
      ·
        refine ⟨1053939517778788320366893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2810505380743435520978381 1053939517778788320366893)
        ·
          refine ⟨395227319167045620137585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1053939517778788320366893 395227319167045620137585)
          ·
            refine ⟨296420489375284215103189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 395227319167045620137585 296420489375284215103189)
            ·
              refine ⟨6947355219733223791481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 296420489375284215103189 6947355219733223791481)
              ·
                rfl

theorem cell21_273981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 7].length) (baseStart_273981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_273981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_273981 prefixEnd_273981 := by exact prefixLift 273981
  have htrace : WordTrace (prefixWord ++ tailWord_273981) baseStart_273981 baseEnd_273981 := by
    simpa [prefixWord, tailWord_273981, baseEnd_273981] using wordTrace_append hprefix tailTrace_273981
  have hstable : (prefixWord ++ tailWord_273981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_273981).length < 2 ^ (prefixWord ++ tailWord_273981).sum := by decide
  have hdescent : baseEnd_273981 < baseStart_273981 := by decide
  rcases family_descends (prefixWord ++ tailWord_273981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274071 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 5]
def baseStart_274071 : Nat := 118140960795 + 274071 * 2 ^ 59
def prefixEnd_274071 : Nat := 4983230072969 + 3 ^ 40 * 274071 * 2
def baseEnd_274071 : Nat := 62546736203778857623145

theorem tailTrace_274071 : CollatzResearch.WordTrace tailWord_274071 prefixEnd_274071 62546736203778857623145 := by
  unfold tailWord_274071
  simp only [CollatzResearch.WordTrace]
  refine ⟨9996190590095049445366067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6664127060063366296910711 9996190590095049445366067)
  ·
    refine ⟨14994285885142574168049101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9996190590095049445366067 14994285885142574168049101)
    ·
      refine ⟨5622857206928465313018413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14994285885142574168049101 5622857206928465313018413)
      ·
        refine ⟨2108571452598174492381905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5622857206928465313018413 2108571452598174492381905)
        ·
          refine ⟨1581428589448630869286429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2108571452598174492381905 1581428589448630869286429)
          ·
            refine ⟨593035721043236575982411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1581428589448630869286429 593035721043236575982411)
            ·
              refine ⟨889553581564854863973617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 593035721043236575982411 889553581564854863973617)
              ·
                refine ⟨667165186173641147980213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889553581564854863973617 667165186173641147980213)
                ·
                  refine ⟨62546736203778857623145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 667165186173641147980213 62546736203778857623145)
                  ·
                    rfl

theorem cell21_274071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 5].length) (baseStart_274071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274071 prefixEnd_274071 := by exact prefixLift 274071
  have htrace : WordTrace (prefixWord ++ tailWord_274071) baseStart_274071 baseEnd_274071 := by
    simpa [prefixWord, tailWord_274071, baseEnd_274071] using wordTrace_append hprefix tailTrace_274071
  have hstable : (prefixWord ++ tailWord_274071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274071).length < 2 ^ (prefixWord ++ tailWord_274071).sum := by decide
  have hdescent : baseEnd_274071 < baseStart_274071 := by decide
  rcases family_descends (prefixWord ++ tailWord_274071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274099 : List Nat := [1, 1, 1, 2, 3, 3, 10]
def baseStart_274099 : Nat := 118140960795 + 274099 * 2 ^ 59
def prefixEnd_274099 : Nat := 4983230072969 + 3 ^ 40 * 274099 * 2
def baseEnd_274099 : Nat := 6950347353917447906269

theorem tailTrace_274099 : CollatzResearch.WordTrace tailWord_274099 prefixEnd_274099 6950347353917447906269 := by
  unfold tailWord_274099
  simp only [CollatzResearch.WordTrace]
  refine ⟨9997211833993610227385351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6664807889329073484923567 9997211833993610227385351)
  ·
    refine ⟨14995817750990415341078027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9997211833993610227385351 14995817750990415341078027)
    ·
      refine ⟨22493726626485623011617041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14995817750990415341078027 22493726626485623011617041)
      ·
        refine ⟨16870294969864217258712781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22493726626485623011617041 16870294969864217258712781)
        ·
          refine ⟨6326360613699081472017293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16870294969864217258712781 6326360613699081472017293)
          ·
            refine ⟨2372385230137155552006485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6326360613699081472017293 2372385230137155552006485)
            ·
              refine ⟨6950347353917447906269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2372385230137155552006485 6950347353917447906269)
              ·
                rfl

theorem cell21_274099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 10].length) (baseStart_274099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274099 prefixEnd_274099 := by exact prefixLift 274099
  have htrace : WordTrace (prefixWord ++ tailWord_274099) baseStart_274099 baseEnd_274099 := by
    simpa [prefixWord, tailWord_274099, baseEnd_274099] using wordTrace_append hprefix tailTrace_274099
  have hstable : (prefixWord ++ tailWord_274099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274099).length < 2 ^ (prefixWord ++ tailWord_274099).sum := by decide
  have hdescent : baseEnd_274099 < baseStart_274099 := by decide
  rcases family_descends (prefixWord ++ tailWord_274099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274116 : List Nat := [2, 3, 3, 1, 1, 1, 2, 8]
def baseStart_274116 : Nat := 118140960795 + 274116 * 2 ^ 59
def prefixEnd_274116 : Nat := 4983230072969 + 3 ^ 40 * 274116 * 2
def baseEnd_274116 : Nat := 20852335272289593124351

theorem tailTrace_274116 : CollatzResearch.WordTrace tailWord_274116 prefixEnd_274116 20852335272289593124351 := by
  unfold tailWord_274116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4998915937466011065377101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6665221249954681420502801 4998915937466011065377101)
  ·
    refine ⟨1874593476549754149516413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4998915937466011065377101 1874593476549754149516413)
    ·
      refine ⟨702972553706157806068655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1874593476549754149516413 702972553706157806068655)
      ·
        refine ⟨1054458830559236709102983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702972553706157806068655 1054458830559236709102983)
        ·
          refine ⟨1581688245838855063654475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054458830559236709102983 1581688245838855063654475)
          ·
            refine ⟨2372532368758282595481713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581688245838855063654475 2372532368758282595481713)
            ·
              refine ⟨1779399276568711946611285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2372532368758282595481713 1779399276568711946611285)
              ·
                refine ⟨20852335272289593124351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1779399276568711946611285 20852335272289593124351)
                ·
                  rfl

theorem cell21_274116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 8].length) (baseStart_274116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274116 prefixEnd_274116 := by exact prefixLift 274116
  have htrace : WordTrace (prefixWord ++ tailWord_274116) baseStart_274116 baseEnd_274116 := by
    simpa [prefixWord, tailWord_274116, baseEnd_274116] using wordTrace_append hprefix tailTrace_274116
  have hstable : (prefixWord ++ tailWord_274116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274116).length < 2 ^ (prefixWord ++ tailWord_274116).sum := by decide
  have hdescent : baseEnd_274116 < baseStart_274116 := by decide
  rcases family_descends (prefixWord ++ tailWord_274116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274161 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 6]
def baseStart_274161 : Nat := 118140960795 + 274161 * 2 ^ 59
def prefixEnd_274161 : Nat := 4983230072969 + 3 ^ 40 * 274161 * 2
def baseEnd_274161 : Nat := 62567275429958701122961

theorem tailTrace_274161 : CollatzResearch.WordTrace tailWord_274161 prefixEnd_274161 62567275429958701122961 := by
  unfold tailWord_274161
  simp only [CollatzResearch.WordTrace]
  refine ⟨9999473159768994816142337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6666315439845996544094891 9999473159768994816142337)
  ·
    refine ⟨7499604869826746112106753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9999473159768994816142337 7499604869826746112106753)
    ·
      refine ⟨5624703652370059584080065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7499604869826746112106753 5624703652370059584080065)
      ·
        refine ⟨4218527739277544688060049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5624703652370059584080065 4218527739277544688060049)
        ·
          refine ⟨3163895804458158516045037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4218527739277544688060049 3163895804458158516045037)
          ·
            refine ⟨1186460926671809443516889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3163895804458158516045037 1186460926671809443516889)
            ·
              refine ⟨889845695003857082637667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186460926671809443516889 889845695003857082637667)
              ·
                refine ⟨1334768542505785623956501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889845695003857082637667 1334768542505785623956501)
                ·
                  refine ⟨62567275429958701122961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1334768542505785623956501 62567275429958701122961)
                  ·
                    rfl

theorem cell21_274161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_274161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274161 prefixEnd_274161 := by exact prefixLift 274161
  have htrace : WordTrace (prefixWord ++ tailWord_274161) baseStart_274161 baseEnd_274161 := by
    simpa [prefixWord, tailWord_274161, baseEnd_274161] using wordTrace_append hprefix tailTrace_274161
  have hstable : (prefixWord ++ tailWord_274161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274161).length < 2 ^ (prefixWord ++ tailWord_274161).sum := by decide
  have hdescent : baseEnd_274161 < baseStart_274161 := by decide
  rcases family_descends (prefixWord ++ tailWord_274161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274175 : List Nat := [1, 1, 2, 2, 1, 3, 3, 8]
def baseStart_274175 : Nat := 118140960795 + 274175 * 2 ^ 59
def prefixEnd_274175 : Nat := 4983230072969 + 3 ^ 40 * 274175 * 2
def baseEnd_274175 : Nat := 20856823473565929296533

theorem tailTrace_274175 : CollatzResearch.WordTrace tailWord_274175 prefixEnd_274175 20856823473565929296533 := by
  unfold tailWord_274175
  simp only [CollatzResearch.WordTrace]
  refine ⟨9999983781718275207151979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6666655854478850138101319 9999983781718275207151979)
  ·
    refine ⟨14999975672577412810727969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9999983781718275207151979 14999975672577412810727969)
    ·
      refine ⟨11249981754433059608045977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14999975672577412810727969 11249981754433059608045977)
      ·
        refine ⟨8437486315824794706034483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11249981754433059608045977 8437486315824794706034483)
        ·
          refine ⟨12656229473737192059051725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8437486315824794706034483 12656229473737192059051725)
          ·
            refine ⟨4746086052651447022144397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12656229473737192059051725 4746086052651447022144397)
            ·
              refine ⟨1779782269744292633304149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4746086052651447022144397 1779782269744292633304149)
              ·
                refine ⟨20856823473565929296533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1779782269744292633304149 20856823473565929296533)
                ·
                  rfl

theorem cell21_274175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 8].length) (baseStart_274175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274175 prefixEnd_274175 := by exact prefixLift 274175
  have htrace : WordTrace (prefixWord ++ tailWord_274175) baseStart_274175 baseEnd_274175 := by
    simpa [prefixWord, tailWord_274175, baseEnd_274175] using wordTrace_append hprefix tailTrace_274175
  have hstable : (prefixWord ++ tailWord_274175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274175).length < 2 ^ (prefixWord ++ tailWord_274175).sum := by decide
  have hdescent : baseEnd_274175 < baseStart_274175 := by decide
  rcases family_descends (prefixWord ++ tailWord_274175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274223 : List Nat := [1, 1, 2, 1, 2, 1, 2, 8, 3]
def baseStart_274223 : Nat := 118140960795 + 274223 * 2 ^ 59
def prefixEnd_274223 : Nat := 4983230072969 + 3 ^ 40 * 274223 * 2
def baseEnd_274223 : Nat := 62581424674660371089501

theorem tailTrace_274223 : CollatzResearch.WordTrace tailWord_274223 prefixEnd_274223 62581424674660371089501 := by
  unfold tailWord_274223
  simp only [CollatzResearch.WordTrace]
  refine ⟨10001734485544379404899323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6667822990362919603266215 10001734485544379404899323)
  ·
    refine ⟨15002601728316569107348985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10001734485544379404899323 15002601728316569107348985)
    ·
      refine ⟨11251951296237426830511739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15002601728316569107348985 11251951296237426830511739)
      ·
        refine ⟨16877926944356140245767609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11251951296237426830511739 16877926944356140245767609)
        ·
          refine ⟨12658445208267105184325707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16877926944356140245767609 12658445208267105184325707)
          ·
            refine ⟨18987667812400657776488561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12658445208267105184325707 18987667812400657776488561)
            ·
              refine ⟨14240750859300493332366421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18987667812400657776488561 14240750859300493332366421)
              ·
                refine ⟨166883799132427656238669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 14240750859300493332366421 166883799132427656238669)
                ·
                  refine ⟨62581424674660371089501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166883799132427656238669 62581424674660371089501)
                  ·
                    rfl

theorem cell21_274223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 3].length) (baseStart_274223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274223 prefixEnd_274223 := by exact prefixLift 274223
  have htrace : WordTrace (prefixWord ++ tailWord_274223) baseStart_274223 baseEnd_274223 := by
    simpa [prefixWord, tailWord_274223, baseEnd_274223] using wordTrace_append hprefix tailTrace_274223
  have hstable : (prefixWord ++ tailWord_274223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274223).length < 2 ^ (prefixWord ++ tailWord_274223).sum := by decide
  have hdescent : baseEnd_274223 < baseStart_274223 := by decide
  rcases family_descends (prefixWord ++ tailWord_274223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274302 : List Nat := [4, 2, 3, 1, 1, 1, 4, 5]
def baseStart_274302 : Nat := 118140960795 + 274302 * 2 ^ 59
def prefixEnd_274302 : Nat := 4983230072969 + 3 ^ 40 * 274302 * 2
def baseEnd_274302 : Nat := 20866484516991263090891

theorem tailTrace_274302 : CollatzResearch.WordTrace tailWord_274302 prefixEnd_274302 20866484516991263090891 := by
  unfold tailWord_274302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1250576981532271987128145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6669743901505450598016773 1250576981532271987128145)
  ·
    refine ⟨937932736149203990346109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1250576981532271987128145 937932736149203990346109)
    ·
      refine ⟨351724776055951496379791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 937932736149203990346109 351724776055951496379791)
      ·
        refine ⟨527587164083927244569687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351724776055951496379791 527587164083927244569687)
        ·
          refine ⟨791380746125890866854531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527587164083927244569687 791380746125890866854531)
          ·
            refine ⟨1187071119188836300281797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 791380746125890866854531 1187071119188836300281797)
            ·
              refine ⟨222575834847906806302837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1187071119188836300281797 222575834847906806302837)
              ·
                refine ⟨20866484516991263090891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222575834847906806302837 20866484516991263090891)
                ·
                  rfl

theorem cell21_274302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_274302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274302 prefixEnd_274302 := by exact prefixLift 274302
  have htrace : WordTrace (prefixWord ++ tailWord_274302) baseStart_274302 baseEnd_274302 := by
    simpa [prefixWord, tailWord_274302, baseEnd_274302] using wordTrace_append hprefix tailTrace_274302
  have hstable : (prefixWord ++ tailWord_274302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274302).length < 2 ^ (prefixWord ++ tailWord_274302).sum := by decide
  have hdescent : baseEnd_274302 < baseStart_274302 := by decide
  rcases family_descends (prefixWord ++ tailWord_274302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274327 : List Nat := [1, 1, 3, 3, 1, 3, 9]
def baseStart_274327 : Nat := 118140960795 + 274327 * 2 ^ 59
def prefixEnd_274327 : Nat := 4983230072969 + 3 ^ 40 * 274327 * 2
def baseEnd_274327 : Nat := 6956128765731033483995

theorem tailTrace_274327 : CollatzResearch.WordTrace tailWord_274327 prefixEnd_274327 6956128765731033483995 := by
  unfold tailWord_274327
  simp only [CollatzResearch.WordTrace]
  refine ⟨10005527677167605166685235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6670351784778403444456823 10005527677167605166685235)
  ·
    refine ⟨15008291515751407750027853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10005527677167605166685235 15008291515751407750027853)
    ·
      refine ⟨5628109318406777906260445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15008291515751407750027853 5628109318406777906260445)
      ·
        refine ⟨2110540994402541714847667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5628109318406777906260445 2110540994402541714847667)
        ·
          refine ⟨3165811491603812572271501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2110540994402541714847667 3165811491603812572271501)
          ·
            refine ⟨1187179309351429714601813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3165811491603812572271501 1187179309351429714601813)
            ·
              refine ⟨6956128765731033483995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1187179309351429714601813 6956128765731033483995)
              ·
                rfl

theorem cell21_274327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 9].length) (baseStart_274327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274327 prefixEnd_274327 := by exact prefixLift 274327
  have htrace : WordTrace (prefixWord ++ tailWord_274327) baseStart_274327 baseEnd_274327 := by
    simpa [prefixWord, tailWord_274327, baseEnd_274327] using wordTrace_append hprefix tailTrace_274327
  have hstable : (prefixWord ++ tailWord_274327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274327).length < 2 ^ (prefixWord ++ tailWord_274327).sum := by decide
  have hdescent : baseEnd_274327 < baseStart_274327 := by decide
  rcases family_descends (prefixWord ++ tailWord_274327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274333 : List Nat := [1, 4, 2, 1, 2, 3, 3, 2, 3]
def baseStart_274333 : Nat := 118140960795 + 274333 * 2 ^ 59
def prefixEnd_274333 : Nat := 4983230072969 + 3 ^ 40 * 274333 * 2
def baseEnd_274333 : Nat := 62606528173324624255943

theorem tailTrace_274333 : CollatzResearch.WordTrace tailWord_274333 prefixEnd_274333 62606528173324624255943 := by
  unfold tailWord_274333
  simp only [CollatzResearch.WordTrace]
  refine ⟨10005746515145868191403653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6670497676763912127602435 10005746515145868191403653)
  ·
    refine ⟨1876077471589850285888185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10005746515145868191403653 1876077471589850285888185)
    ·
      refine ⟨1407058103692387714416139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1876077471589850285888185 1407058103692387714416139)
      ·
        refine ⟨2110587155538581571624209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407058103692387714416139 2110587155538581571624209)
        ·
          refine ⟨1582940366653936178718157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2110587155538581571624209 1582940366653936178718157)
          ·
            refine ⟨593602637495226067019309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1582940366653936178718157 593602637495226067019309)
            ·
              refine ⟨222600989060709775132241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 593602637495226067019309 222600989060709775132241)
              ·
                refine ⟨166950741795532331349181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222600989060709775132241 166950741795532331349181)
                ·
                  refine ⟨62606528173324624255943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166950741795532331349181 62606528173324624255943)
                  ·
                    rfl

theorem cell21_274333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_274333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274333 prefixEnd_274333 := by exact prefixLift 274333
  have htrace : WordTrace (prefixWord ++ tailWord_274333) baseStart_274333 baseEnd_274333 := by
    simpa [prefixWord, tailWord_274333, baseEnd_274333] using wordTrace_append hprefix tailTrace_274333
  have hstable : (prefixWord ++ tailWord_274333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274333).length < 2 ^ (prefixWord ++ tailWord_274333).sum := by decide
  have hdescent : baseEnd_274333 < baseStart_274333 := by decide
  rcases family_descends (prefixWord ++ tailWord_274333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274375 : List Nat := [1, 1, 4, 1, 1, 2, 1, 7, 3]
def baseStart_274375 : Nat := 118140960795 + 274375 * 2 ^ 59
def prefixEnd_274375 : Nat := 4983230072969 + 3 ^ 40 * 274375 * 2
def baseEnd_274375 : Nat := 62616113145541884555857

theorem tailTrace_274375 : CollatzResearch.WordTrace tailWord_274375 prefixEnd_274375 62616113145541884555857 := by
  unfold tailWord_274375
  simp only [CollatzResearch.WordTrace]
  refine ⟨10007278380993709364432579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6671518920662472909621719 10007278380993709364432579)
  ·
    refine ⟨15010917571490564046648869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10007278380993709364432579 15010917571490564046648869)
    ·
      refine ⟨2814547044654480758746663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15010917571490564046648869 2814547044654480758746663)
      ·
        refine ⟨4221820566981721138119995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2814547044654480758746663 4221820566981721138119995)
        ·
          refine ⟨6332730850472581707179993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4221820566981721138119995 6332730850472581707179993)
          ·
            refine ⟨4749548137854436280384995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6332730850472581707179993 4749548137854436280384995)
            ·
              refine ⟨7124322206781654420577493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4749548137854436280384995 7124322206781654420577493)
              ·
                refine ⟨166976301721445025482285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7124322206781654420577493 166976301721445025482285)
                ·
                  refine ⟨62616113145541884555857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 166976301721445025482285 62616113145541884555857)
                  ·
                    rfl

theorem cell21_274375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 3].length) (baseStart_274375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274375 prefixEnd_274375 := by exact prefixLift 274375
  have htrace : WordTrace (prefixWord ++ tailWord_274375) baseStart_274375 baseEnd_274375 := by
    simpa [prefixWord, tailWord_274375, baseEnd_274375] using wordTrace_append hprefix tailTrace_274375
  have hstable : (prefixWord ++ tailWord_274375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274375).length < 2 ^ (prefixWord ++ tailWord_274375).sum := by decide
  have hdescent : baseEnd_274375 < baseStart_274375 := by decide
  rcases family_descends (prefixWord ++ tailWord_274375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274448 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 6]
def baseStart_274448 : Nat := 118140960795 + 274448 * 2 ^ 59
def prefixEnd_274448 : Nat := 4983230072969 + 3 ^ 40 * 274448 * 2
def baseEnd_274448 : Nat := 62632772740109979839041

theorem tailTrace_274448 : CollatzResearch.WordTrace tailWord_274448 prefixEnd_274448 62632772740109979839041 := by
  unfold tailWord_274448
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004970454864621415919999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6673293939819495221226665 5004970454864621415919999)
  ·
    refine ⟨7507455682296932123879999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5004970454864621415919999 7507455682296932123879999)
    ·
      refine ⟨11261183523445398185819999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7507455682296932123879999 11261183523445398185819999)
      ·
        refine ⟨16891775285168097278729999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11261183523445398185819999 16891775285168097278729999)
        ·
          refine ⟨25337662927752145918094999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16891775285168097278729999 25337662927752145918094999)
          ·
            refine ⟨38006494391628218877142499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25337662927752145918094999 38006494391628218877142499)
            ·
              refine ⟨57009741587442328315713749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38006494391628218877142499 57009741587442328315713749)
              ·
                refine ⟨1336165818455679569899541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57009741587442328315713749 1336165818455679569899541)
                ·
                  refine ⟨62632772740109979839041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1336165818455679569899541 62632772740109979839041)
                  ·
                    rfl

theorem cell21_274448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_274448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274448 prefixEnd_274448 := by exact prefixLift 274448
  have htrace : WordTrace (prefixWord ++ tailWord_274448) baseStart_274448 baseEnd_274448 := by
    simpa [prefixWord, tailWord_274448, baseEnd_274448] using wordTrace_append hprefix tailTrace_274448
  have hstable : (prefixWord ++ tailWord_274448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274448).length < 2 ^ (prefixWord ++ tailWord_274448).sum := by decide
  have hdescent : baseEnd_274448 < baseStart_274448 := by decide
  rcases family_descends (prefixWord ++ tailWord_274448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274451 : List Nat := [1, 1, 1, 2, 1, 4, 4, 4, 3]
def baseStart_274451 : Nat := 118140960795 + 274451 * 2 ^ 59
def prefixEnd_274451 : Nat := 4983230072969 + 3 ^ 40 * 274451 * 2
def baseEnd_274451 : Nat := 62633457380982641289035

theorem tailTrace_274451 : CollatzResearch.WordTrace tailWord_274451 prefixEnd_274451 62633457380982641289035 := by
  unfold tailWord_274451
  simp only [CollatzResearch.WordTrace]
  refine ⟨10010050328718374344199207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6673366885812249562799471 10010050328718374344199207)
  ·
    refine ⟨15015075493077561516298811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10010050328718374344199207 15015075493077561516298811)
    ·
      refine ⟨22522613239616342274448217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15015075493077561516298811 22522613239616342274448217)
      ·
        refine ⟨16891959929712256705836163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22522613239616342274448217 16891959929712256705836163)
        ·
          refine ⟨25337939894568385058754245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16891959929712256705836163 25337939894568385058754245)
          ·
            refine ⟨4750863730231572198516421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25337939894568385058754245 4750863730231572198516421)
            ·
              refine ⟨890786949418419787221829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4750863730231572198516421 890786949418419787221829)
              ·
                refine ⟨167022553015953710104093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 890786949418419787221829 167022553015953710104093)
                ·
                  refine ⟨62633457380982641289035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167022553015953710104093 62633457380982641289035)
                  ·
                    rfl

theorem cell21_274451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 4, 3].length) (baseStart_274451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274451 prefixEnd_274451 := by exact prefixLift 274451
  have htrace : WordTrace (prefixWord ++ tailWord_274451) baseStart_274451 baseEnd_274451 := by
    simpa [prefixWord, tailWord_274451, baseEnd_274451] using wordTrace_append hprefix tailTrace_274451
  have hstable : (prefixWord ++ tailWord_274451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274451).length < 2 ^ (prefixWord ++ tailWord_274451).sum := by decide
  have hdescent : baseEnd_274451 < baseStart_274451 := by decide
  rcases family_descends (prefixWord ++ tailWord_274451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274471 : List Nat := [1, 1, 7, 1, 3, 1, 2, 5]
def baseStart_274471 : Nat := 118140960795 + 274471 * 2 ^ 59
def prefixEnd_274471 : Nat := 4983230072969 + 3 ^ 40 * 274471 * 2
def baseEnd_274471 : Nat := 20879340551155683651887

theorem tailTrace_274471 : CollatzResearch.WordTrace tailWord_274471 prefixEnd_274471 20879340551155683651887 := by
  unfold tailWord_274471
  simp only [CollatzResearch.WordTrace]
  refine ⟨10010779788645917759927267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6673853192430611839951511 10010779788645917759927267)
  ·
    refine ⟨15016169682968876639890901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10010779788645917759927267 15016169682968876639890901)
    ·
      refine ⟨351941476944583046247443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 15016169682968876639890901 351941476944583046247443)
      ·
        refine ⟨527912215416874569371165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351941476944583046247443 527912215416874569371165)
        ·
          refine ⟨197967080781327963514187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 527912215416874569371165 197967080781327963514187)
          ·
            refine ⟨296950621171991945271281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197967080781327963514187 296950621171991945271281)
            ·
              refine ⟨222712965878993958953461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296950621171991945271281 222712965878993958953461)
              ·
                refine ⟨20879340551155683651887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222712965878993958953461 20879340551155683651887)
                ·
                  rfl

theorem cell21_274471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 2, 5].length) (baseStart_274471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274471 prefixEnd_274471 := by exact prefixLift 274471
  have htrace : WordTrace (prefixWord ++ tailWord_274471) baseStart_274471 baseEnd_274471 := by
    simpa [prefixWord, tailWord_274471, baseEnd_274471] using wordTrace_append hprefix tailTrace_274471
  have hstable : (prefixWord ++ tailWord_274471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274471).length < 2 ^ (prefixWord ++ tailWord_274471).sum := by decide
  have hdescent : baseEnd_274471 < baseStart_274471 := by decide
  rcases family_descends (prefixWord ++ tailWord_274471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274502 : List Nat := [6, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_274502 : Nat := 118140960795 + 274502 * 2 ^ 59
def prefixEnd_274502 : Nat := 4983230072969 + 3 ^ 40 * 274502 * 2
def baseEnd_274502 : Nat := 62645096275817885938931

theorem tailTrace_274502 : CollatzResearch.WordTrace tailWord_274502 prefixEnd_274502 62645096275817885938931 := by
  unfold tailWord_274502
  simp only [CollatzResearch.WordTrace]
  refine ⟨312872201610425314197055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6674606967689073369537173 312872201610425314197055)
  ·
    refine ⟨469308302415637971295583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 312872201610425314197055 469308302415637971295583)
    ·
      refine ⟨703962453623456956943375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 469308302415637971295583 703962453623456956943375)
      ·
        refine ⟨1055943680435185435415063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703962453623456956943375 1055943680435185435415063)
        ·
          refine ⟨1583915520652778153122595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1055943680435185435415063 1583915520652778153122595)
          ·
            refine ⟨2375873280979167229683893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583915520652778153122595 2375873280979167229683893)
            ·
              refine ⟨222738120091796927782865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2375873280979167229683893 222738120091796927782865)
              ·
                refine ⟨167053590068847695837149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222738120091796927782865 167053590068847695837149)
                ·
                  refine ⟨62645096275817885938931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167053590068847695837149 62645096275817885938931)
                  ·
                    rfl

theorem cell21_274502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_274502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274502 prefixEnd_274502 := by exact prefixLift 274502
  have htrace : WordTrace (prefixWord ++ tailWord_274502) baseStart_274502 baseEnd_274502 := by
    simpa [prefixWord, tailWord_274502, baseEnd_274502] using wordTrace_append hprefix tailTrace_274502
  have hstable : (prefixWord ++ tailWord_274502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274502).length < 2 ^ (prefixWord ++ tailWord_274502).sum := by decide
  have hdescent : baseEnd_274502 < baseStart_274502 := by decide
  rcases family_descends (prefixWord ++ tailWord_274502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274634 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_274634 : Nat := 118140960795 + 274634 * 2 ^ 59
def prefixEnd_274634 : Nat := 4983230072969 + 3 ^ 40 * 274634 * 2
def baseEnd_274634 : Nat := 62675220474214989738661

theorem tailTrace_274634 : CollatzResearch.WordTrace tailWord_274634 prefixEnd_274634 62675220474214989738661 := by
  unfold tailWord_274634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2504181221763849149527739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6677816591370264398740637 2504181221763849149527739)
  ·
    refine ⟨3756271832645773724291609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2504181221763849149527739 3756271832645773724291609)
    ·
      refine ⟨2817203874484330293218707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3756271832645773724291609 2817203874484330293218707)
      ·
        refine ⟨4225805811726495439828061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2817203874484330293218707 4225805811726495439828061)
        ·
          refine ⟨1584677179397435789935523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4225805811726495439828061 1584677179397435789935523)
          ·
            refine ⟨2377015769096153684903285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584677179397435789935523 2377015769096153684903285)
            ·
              refine ⟨222845228352764407959683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2377015769096153684903285 222845228352764407959683)
              ·
                refine ⟨334267842529146611939525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222845228352764407959683 334267842529146611939525)
                ·
                  refine ⟨62675220474214989738661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 334267842529146611939525 62675220474214989738661)
                  ·
                    rfl

theorem cell21_274634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_274634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274634 prefixEnd_274634 := by exact prefixLift 274634
  have htrace : WordTrace (prefixWord ++ tailWord_274634) baseStart_274634 baseEnd_274634 := by
    simpa [prefixWord, tailWord_274634, baseEnd_274634] using wordTrace_append hprefix tailTrace_274634
  have hstable : (prefixWord ++ tailWord_274634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274634).length < 2 ^ (prefixWord ++ tailWord_274634).sum := by decide
  have hdescent : baseEnd_274634 < baseStart_274634 := by decide
  rcases family_descends (prefixWord ++ tailWord_274634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274648 : List Nat := [2, 1, 2, 2, 4, 1, 4, 5]
def baseStart_274648 : Nat := 118140960795 + 274648 * 2 ^ 59
def prefixEnd_274648 : Nat := 4983230072969 + 3 ^ 40 * 274648 * 2
def baseEnd_274648 : Nat := 20892805154984692168433

theorem tailTrace_274648 : CollatzResearch.WordTrace tailWord_274648 prefixEnd_274648 20892805154984692168433 := by
  unfold tailWord_274648
  simp only [CollatzResearch.WordTrace]
  refine ⟨5008617754502338494560299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6678157006003117992747065 5008617754502338494560299)
  ·
    refine ⟨7512926631753507741840449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5008617754502338494560299 7512926631753507741840449)
    ·
      refine ⟨5634694973815130806380337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7512926631753507741840449 5634694973815130806380337)
      ·
        refine ⟨4226021230361348104785253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5634694973815130806380337 4226021230361348104785253)
        ·
          refine ⟨792378980692752769647235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4226021230361348104785253 792378980692752769647235)
          ·
            refine ⟨1188568471039129154470853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792378980692752769647235 1188568471039129154470853)
            ·
              refine ⟨222856588319836716463285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1188568471039129154470853 222856588319836716463285)
              ·
                refine ⟨20892805154984692168433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222856588319836716463285 20892805154984692168433)
                ·
                  rfl

theorem cell21_274648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 5].length) (baseStart_274648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274648 prefixEnd_274648 := by exact prefixLift 274648
  have htrace : WordTrace (prefixWord ++ tailWord_274648) baseStart_274648 baseEnd_274648 := by
    simpa [prefixWord, tailWord_274648, baseEnd_274648] using wordTrace_append hprefix tailTrace_274648
  have hstable : (prefixWord ++ tailWord_274648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274648).length < 2 ^ (prefixWord ++ tailWord_274648).sum := by decide
  have hdescent : baseEnd_274648 < baseStart_274648 := by decide
  rcases family_descends (prefixWord ++ tailWord_274648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274730 : List Nat := [3, 1, 4, 2, 2, 2, 2, 2, 3]
def baseStart_274730 : Nat := 118140960795 + 274730 * 2 ^ 59
def prefixEnd_274730 : Nat := 4983230072969 + 3 ^ 40 * 274730 * 2
def baseEnd_274730 : Nat := 62697128982140156138465

theorem tailTrace_274730 : CollatzResearch.WordTrace tailWord_274730 prefixEnd_274730 62697128982140156138465 := by
  unfold tailWord_274730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505056573676901248401411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6680150863138403329070429 2505056573676901248401411)
  ·
    refine ⟨3757584860515351872602117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2505056573676901248401411 3757584860515351872602117)
    ·
      refine ⟨704547161346628476112897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3757584860515351872602117 704547161346628476112897)
      ·
        refine ⟨528410371009971357084673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704547161346628476112897 528410371009971357084673)
        ·
          refine ⟨396307778257478517813505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528410371009971357084673 396307778257478517813505)
          ·
            refine ⟨297230833693108888360129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396307778257478517813505 297230833693108888360129)
            ·
              refine ⟨222923125269831666270097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297230833693108888360129 222923125269831666270097)
              ·
                refine ⟨167192343952373749702573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222923125269831666270097 167192343952373749702573)
                ·
                  refine ⟨62697128982140156138465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167192343952373749702573 62697128982140156138465)
                  ·
                    rfl

theorem cell21_274730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_274730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274730 prefixEnd_274730 := by exact prefixLift 274730
  have htrace : WordTrace (prefixWord ++ tailWord_274730) baseStart_274730 baseEnd_274730 := by
    simpa [prefixWord, tailWord_274730, baseEnd_274730] using wordTrace_append hprefix tailTrace_274730
  have hstable : (prefixWord ++ tailWord_274730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274730).length < 2 ^ (prefixWord ++ tailWord_274730).sum := by decide
  have hdescent : baseEnd_274730 < baseStart_274730 := by decide
  rcases family_descends (prefixWord ++ tailWord_274730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274772 : List Nat := [2, 4, 1, 1, 2, 3, 2, 3, 3]
def baseStart_274772 : Nat := 118140960795 + 274772 * 2 ^ 59
def prefixEnd_274772 : Nat := 4983230072969 + 3 ^ 40 * 274772 * 2
def baseEnd_274772 : Nat := 62706713954357416438379

theorem tailTrace_274772 : CollatzResearch.WordTrace tailWord_274772 prefixEnd_274772 62706713954357416438379 := by
  unfold tailWord_274772
  simp only [CollatzResearch.WordTrace]
  refine ⟨5010879080277723083317285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6681172107036964111089713 5010879080277723083317285)
  ·
    refine ⟨939539827552073078121991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5010879080277723083317285 939539827552073078121991)
    ·
      refine ⟨1409309741328109617182987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 939539827552073078121991 1409309741328109617182987)
      ·
        refine ⟨2113964611992164425774481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1409309741328109617182987 2113964611992164425774481)
        ·
          refine ⟨1585473458994123319330861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2113964611992164425774481 1585473458994123319330861)
          ·
            refine ⟨594552547122796244749073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1585473458994123319330861 594552547122796244749073)
            ·
              refine ⟨445914410342097183561805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 594552547122796244749073 445914410342097183561805)
              ·
                refine ⟨167217903878286443835677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 445914410342097183561805 167217903878286443835677)
                ·
                  refine ⟨62706713954357416438379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167217903878286443835677 62706713954357416438379)
                  ·
                    rfl

theorem cell21_274772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_274772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274772 prefixEnd_274772 := by exact prefixLift 274772
  have htrace : WordTrace (prefixWord ++ tailWord_274772) baseStart_274772 baseEnd_274772 := by
    simpa [prefixWord, tailWord_274772, baseEnd_274772] using wordTrace_append hprefix tailTrace_274772
  have hstable : (prefixWord ++ tailWord_274772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274772).length < 2 ^ (prefixWord ++ tailWord_274772).sum := by decide
  have hdescent : baseEnd_274772 < baseStart_274772 := by decide
  rcases family_descends (prefixWord ++ tailWord_274772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274786 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 4]
def baseStart_274786 : Nat := 118140960795 + 274786 * 2 ^ 59
def prefixEnd_274786 : Nat := 4983230072969 + 3 ^ 40 * 274786 * 2
def baseEnd_274786 : Nat := 62709908945096503205017

theorem tailTrace_274786 : CollatzResearch.WordTrace tailWord_274786 prefixEnd_274786 62709908945096503205017 := by
  unfold tailWord_274786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505567195626181639411053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6681512521669817705096141 2505567195626181639411053)
  ·
    refine ⟨939587698359818114779145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2505567195626181639411053 939587698359818114779145)
    ·
      refine ⟨704690773769863586084359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 939587698359818114779145 704690773769863586084359)
      ·
        refine ⟨1057036160654795379126539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 704690773769863586084359 1057036160654795379126539)
        ·
          refine ⟨1585554240982193068689809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057036160654795379126539 1585554240982193068689809)
          ·
            refine ⟨1189165680736644801517357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1585554240982193068689809 1189165680736644801517357)
            ·
              refine ⟨445937130276241800569009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1189165680736644801517357 445937130276241800569009)
              ·
                refine ⟨334452847707181350426757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 445937130276241800569009 334452847707181350426757)
                ·
                  refine ⟨62709908945096503205017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 334452847707181350426757 62709908945096503205017)
                  ·
                    rfl

theorem cell21_274786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_274786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274786 prefixEnd_274786 := by exact prefixLift 274786
  have htrace : WordTrace (prefixWord ++ tailWord_274786) baseStart_274786 baseEnd_274786 := by
    simpa [prefixWord, tailWord_274786, baseEnd_274786] using wordTrace_append hprefix tailTrace_274786
  have hstable : (prefixWord ++ tailWord_274786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274786).length < 2 ^ (prefixWord ++ tailWord_274786).sum := by decide
  have hdescent : baseEnd_274786 < baseStart_274786 := by decide
  rcases family_descends (prefixWord ++ tailWord_274786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274817 : List Nat := [1, 2, 4, 3, 1, 3, 2, 5]
def baseStart_274817 : Nat := 118140960795 + 274817 * 2 ^ 59
def prefixEnd_274817 : Nat := 4983230072969 + 3 ^ 40 * 274817 * 2
def baseEnd_274817 : Nat := 20905661189149112729429

theorem tailTrace_274817 : CollatzResearch.WordTrace tailWord_274817 prefixEnd_274817 20905661189149112729429 := by
  unfold tailWord_274817
  simp only [CollatzResearch.WordTrace]
  refine ⟨10023399445392418852022705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6682266296928279234681803 10023399445392418852022705)
  ·
    refine ⟨7517549584044314139017029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10023399445392418852022705 7517549584044314139017029)
    ·
      refine ⟨1409540547008308901065693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7517549584044314139017029 1409540547008308901065693)
      ·
        refine ⟨528577705128115837899635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1409540547008308901065693 528577705128115837899635)
        ·
          refine ⟨792866557692173756849453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528577705128115837899635 792866557692173756849453)
          ·
            refine ⟨297324959134565158818545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 792866557692173756849453 297324959134565158818545)
            ·
              refine ⟨222993719350923869113909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297324959134565158818545 222993719350923869113909)
              ·
                refine ⟨20905661189149112729429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 222993719350923869113909 20905661189149112729429)
                ·
                  rfl

theorem cell21_274817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 5].length) (baseStart_274817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274817 prefixEnd_274817 := by exact prefixLift 274817
  have htrace : WordTrace (prefixWord ++ tailWord_274817) baseStart_274817 baseEnd_274817 := by
    simpa [prefixWord, tailWord_274817, baseEnd_274817] using wordTrace_append hprefix tailTrace_274817
  have hstable : (prefixWord ++ tailWord_274817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274817).length < 2 ^ (prefixWord ++ tailWord_274817).sum := by decide
  have hdescent : baseEnd_274817 < baseStart_274817 := by decide
  rcases family_descends (prefixWord ++ tailWord_274817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274828 : List Nat := [2, 2, 1, 2, 1, 4, 1, 2, 6]
def baseStart_274828 : Nat := 118140960795 + 274828 * 2 ^ 59
def prefixEnd_274828 : Nat := 4983230072969 + 3 ^ 40 * 274828 * 2
def baseEnd_274828 : Nat := 62719493917313763504931

theorem tailTrace_274828 : CollatzResearch.WordTrace tailWord_274828 prefixEnd_274828 62719493917313763504931 := by
  unfold tailWord_274828
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011900324176283865336569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6682533765568378487115425 5011900324176283865336569)
  ·
    refine ⟨3758925243132212899002427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5011900324176283865336569 3758925243132212899002427)
    ·
      refine ⟨5638387864698319348503641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3758925243132212899002427 5638387864698319348503641)
      ·
        refine ⟨4228790898523739511377731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5638387864698319348503641 4228790898523739511377731)
        ·
          refine ⟨6343186347785609267066597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228790898523739511377731 6343186347785609267066597)
          ·
            refine ⟨1189347440209801737574987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6343186347785609267066597 1189347440209801737574987)
            ·
              refine ⟨1784021160314702606362481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1189347440209801737574987 1784021160314702606362481)
              ·
                refine ⟨1338015870236026954771861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784021160314702606362481 1338015870236026954771861)
                ·
                  refine ⟨62719493917313763504931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1338015870236026954771861 62719493917313763504931)
                  ·
                    rfl

theorem cell21_274828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_274828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274828 prefixEnd_274828 := by exact prefixLift 274828
  have htrace : WordTrace (prefixWord ++ tailWord_274828) baseStart_274828 baseEnd_274828 := by
    simpa [prefixWord, tailWord_274828, baseEnd_274828] using wordTrace_append hprefix tailTrace_274828
  have hstable : (prefixWord ++ tailWord_274828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274828).length < 2 ^ (prefixWord ++ tailWord_274828).sum := by decide
  have hdescent : baseEnd_274828 < baseStart_274828 := by decide
  rcases family_descends (prefixWord ++ tailWord_274828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_274848 : List Nat := [2, 1, 1, 4, 1, 4, 3, 2, 3]
def baseStart_274848 : Nat := 118140960795 + 274848 * 2 ^ 59
def prefixEnd_274848 : Nat := 4983230072969 + 3 ^ 40 * 274848 * 2
def baseEnd_274848 : Nat := 62724058189798173171557

theorem tailTrace_274848 : CollatzResearch.WordTrace tailWord_274848 prefixEnd_274848 62724058189798173171557 := by
  unfold tailWord_274848
  simp only [CollatzResearch.WordTrace]
  refine ⟨5012265054140055573200599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6683020072186740764267465 5012265054140055573200599)
  ·
    refine ⟨7518397581210083359800899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5012265054140055573200599 7518397581210083359800899)
    ·
      refine ⟨11277596371815125039701349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7518397581210083359800899 11277596371815125039701349)
      ·
        refine ⟨2114549319715335944944003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11277596371815125039701349 2114549319715335944944003)
        ·
          refine ⟨3171823979573003917416005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2114549319715335944944003 3171823979573003917416005)
          ·
            refine ⟨594716996169938234515501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3171823979573003917416005 594716996169938234515501)
            ·
              refine ⟨223018873563726837943313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 594716996169938234515501 223018873563726837943313)
              ·
                refine ⟨167264155172795128457485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223018873563726837943313 167264155172795128457485)
                ·
                  refine ⟨62724058189798173171557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167264155172795128457485 62724058189798173171557)
                  ·
                    rfl

theorem cell21_274848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 3].length) (baseStart_274848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_274848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_274848 prefixEnd_274848 := by exact prefixLift 274848
  have htrace : WordTrace (prefixWord ++ tailWord_274848) baseStart_274848 baseEnd_274848 := by
    simpa [prefixWord, tailWord_274848, baseEnd_274848] using wordTrace_append hprefix tailTrace_274848
  have hstable : (prefixWord ++ tailWord_274848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_274848).length < 2 ^ (prefixWord ++ tailWord_274848).sum := by decide
  have hdescent : baseEnd_274848 < baseStart_274848 := by decide
  rcases family_descends (prefixWord ++ tailWord_274848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275014 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_275014 : Nat := 118140960795 + 275014 * 2 ^ 59
def prefixEnd_275014 : Nat := 4983230072969 + 3 ^ 40 * 275014 * 2
def baseEnd_275014 : Nat := 62761941651418773404551

theorem tailTrace_275014 : CollatzResearch.WordTrace tailWord_275014 prefixEnd_275014 62761941651418773404551 := by
  unfold tailWord_275014
  simp only [CollatzResearch.WordTrace]
  refine ⟨313455769552460046779503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6687056417119147664629397 313455769552460046779503)
  ·
    refine ⟨470183654328690070169255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 313455769552460046779503 470183654328690070169255)
    ·
      refine ⟨705275481493035105253883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470183654328690070169255 705275481493035105253883)
      ·
        refine ⟨1057913222239552657880825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705275481493035105253883 1057913222239552657880825)
        ·
          refine ⟨793434916679664493410619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1057913222239552657880825 793434916679664493410619)
          ·
            refine ⟨1190152375019496740115929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793434916679664493410619 1190152375019496740115929)
            ·
              refine ⟨892614281264622555086947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1190152375019496740115929 892614281264622555086947)
              ·
                refine ⟨1338921421896933832630421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892614281264622555086947 1338921421896933832630421)
                ·
                  refine ⟨62761941651418773404551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1338921421896933832630421 62761941651418773404551)
                  ·
                    rfl

theorem cell21_275014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_275014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275014 prefixEnd_275014 := by exact prefixLift 275014
  have htrace : WordTrace (prefixWord ++ tailWord_275014) baseStart_275014 baseEnd_275014 := by
    simpa [prefixWord, tailWord_275014, baseEnd_275014] using wordTrace_append hprefix tailTrace_275014
  have hstable : (prefixWord ++ tailWord_275014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275014).length < 2 ^ (prefixWord ++ tailWord_275014).sum := by decide
  have hdescent : baseEnd_275014 < baseStart_275014 := by decide
  rcases family_descends (prefixWord ++ tailWord_275014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275070 : List Nat := [4, 2, 15]
def baseStart_275070 : Nat := 118140960795 + 275070 * 2 ^ 59
def prefixEnd_275070 : Nat := 4983230072969 + 3 ^ 40 * 275070 * 2
def baseEnd_275070 : Nat := 86110729237825954007

theorem tailTrace_275070 : CollatzResearch.WordTrace tailWord_275070 prefixEnd_275070 86110729237825954007 := by
  unfold tailWord_275070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1254078389184480382622833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6688418075650562040655109 1254078389184480382622833)
  ·
    refine ⟨940558791888360286967125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1254078389184480382622833 940558791888360286967125)
    ·
      refine ⟨86110729237825954007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 15 940558791888360286967125 86110729237825954007)
      ·
        rfl

theorem cell21_275070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 15].length) (baseStart_275070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275070 prefixEnd_275070 := by exact prefixLift 275070
  have htrace : WordTrace (prefixWord ++ tailWord_275070) baseStart_275070 baseEnd_275070 := by
    simpa [prefixWord, tailWord_275070, baseEnd_275070] using wordTrace_append hprefix tailTrace_275070
  have hstable : (prefixWord ++ tailWord_275070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275070).length < 2 ^ (prefixWord ++ tailWord_275070).sum := by decide
  have hdescent : baseEnd_275070 < baseStart_275070 := by decide
  rcases family_descends (prefixWord ++ tailWord_275070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275073 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 4]
def baseStart_275073 : Nat := 118140960795 + 275073 * 2 ^ 59
def prefixEnd_275073 : Nat := 4983230072969 + 3 ^ 40 * 275073 * 2
def baseEnd_275073 : Nat := 62775406255247781921097

theorem tailTrace_275073 : CollatzResearch.WordTrace tailWord_275073 prefixEnd_275073 62775406255247781921097 := by
  unfold tailWord_275073
  simp only [CollatzResearch.WordTrace]
  refine ⟨10032736532464974573341873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6688491021643316382227915 10032736532464974573341873)
  ·
    refine ⟨7524552399348730930006405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10032736532464974573341873 7524552399348730930006405)
    ·
      refine ⟨1410853574877887049376201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7524552399348730930006405 1410853574877887049376201)
      ·
        refine ⟨1058140181158415287032151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1410853574877887049376201 1058140181158415287032151)
        ·
          refine ⟨1587210271737622930548227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058140181158415287032151 1587210271737622930548227)
          ·
            refine ⟨2380815407606434395822341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587210271737622930548227 2380815407606434395822341)
            ·
              refine ⟨446402888926206449216689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2380815407606434395822341 446402888926206449216689)
              ·
                refine ⟨334802166694654836912517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446402888926206449216689 334802166694654836912517)
                ·
                  refine ⟨62775406255247781921097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 334802166694654836912517 62775406255247781921097)
                  ·
                    rfl

theorem cell21_275073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_275073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275073 prefixEnd_275073 := by exact prefixLift 275073
  have htrace : WordTrace (prefixWord ++ tailWord_275073) baseStart_275073 baseEnd_275073 := by
    simpa [prefixWord, tailWord_275073, baseEnd_275073] using wordTrace_append hprefix tailTrace_275073
  have hstable : (prefixWord ++ tailWord_275073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275073).length < 2 ^ (prefixWord ++ tailWord_275073).sum := by decide
  have hdescent : baseEnd_275073 < baseStart_275073 := by decide
  rcases family_descends (prefixWord ++ tailWord_275073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275076 : List Nat := [2, 3, 2, 1, 3, 1, 4, 2, 3]
def baseStart_275076 : Nat := 118140960795 + 275076 * 2 ^ 59
def prefixEnd_275076 : Nat := 4983230072969 + 3 ^ 40 * 275076 * 2
def baseEnd_275076 : Nat := 62776090896120443371091

theorem tailTrace_275076 : CollatzResearch.WordTrace tailWord_275076 prefixEnd_275076 62776090896120443371091 := by
  unfold tailWord_275076
  simp only [CollatzResearch.WordTrace]
  refine ⟨5016422975727053042850541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6688563967636070723800721 5016422975727053042850541)
  ·
    refine ⟨1881158615897644891068953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5016422975727053042850541 1881158615897644891068953)
    ·
      refine ⟨1410868961923233668301715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1881158615897644891068953 1410868961923233668301715)
      ·
        refine ⟨2116303442884850502452573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410868961923233668301715 2116303442884850502452573)
        ·
          refine ⟨793613791081818938419715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2116303442884850502452573 793613791081818938419715)
          ·
            refine ⟨1190420686622728407629573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 793613791081818938419715 1190420686622728407629573)
            ·
              refine ⟨223203878741761576430545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1190420686622728407629573 223203878741761576430545)
              ·
                refine ⟨167402909056321182322909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 223203878741761576430545 167402909056321182322909)
                ·
                  refine ⟨62776090896120443371091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167402909056321182322909 62776090896120443371091)
                  ·
                    rfl

theorem cell21_275076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_275076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275076 prefixEnd_275076 := by exact prefixLift 275076
  have htrace : WordTrace (prefixWord ++ tailWord_275076) baseStart_275076 baseEnd_275076 := by
    simpa [prefixWord, tailWord_275076, baseEnd_275076] using wordTrace_append hprefix tailTrace_275076
  have hstable : (prefixWord ++ tailWord_275076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275076).length < 2 ^ (prefixWord ++ tailWord_275076).sum := by decide
  have hdescent : baseEnd_275076 < baseStart_275076 := by decide
  rcases family_descends (prefixWord ++ tailWord_275076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275101 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 7]
def baseStart_275101 : Nat := 118140960795 + 275101 * 2 ^ 59
def prefixEnd_275101 : Nat := 4983230072969 + 3 ^ 40 * 275101 * 2
def baseEnd_275101 : Nat := 62781796236725955454373

theorem tailTrace_275101 : CollatzResearch.WordTrace tailWord_275101 prefixEnd_275101 62781796236725955454373 := by
  unfold tailWord_275101
  simp only [CollatzResearch.WordTrace]
  refine ⟨10033757776363535355361157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6689171850909023570240771 10033757776363535355361157)
  ·
    refine ⟨1881329583068162879130217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10033757776363535355361157 1881329583068162879130217)
    ·
      refine ⟨1410997187301122159347663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1881329583068162879130217 1410997187301122159347663)
      ·
        refine ⟨2116495780951683239021495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1410997187301122159347663 2116495780951683239021495)
        ·
          refine ⟨3174743671427524858532243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2116495780951683239021495 3174743671427524858532243)
          ·
            refine ⟨4762115507141287287798365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3174743671427524858532243 4762115507141287287798365)
            ·
              refine ⟨1785793315177982732924387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4762115507141287287798365 1785793315177982732924387)
              ·
                refine ⟨2678689972766974099386581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1785793315177982732924387 2678689972766974099386581)
                ·
                  refine ⟨62781796236725955454373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2678689972766974099386581 62781796236725955454373)
                  ·
                    rfl

theorem cell21_275101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_275101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275101 prefixEnd_275101 := by exact prefixLift 275101
  have htrace : WordTrace (prefixWord ++ tailWord_275101) baseStart_275101 baseEnd_275101 := by
    simpa [prefixWord, tailWord_275101, baseEnd_275101] using wordTrace_append hprefix tailTrace_275101
  have hstable : (prefixWord ++ tailWord_275101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275101).length < 2 ^ (prefixWord ++ tailWord_275101).sum := by decide
  have hdescent : baseEnd_275101 < baseStart_275101 := by decide
  rcases family_descends (prefixWord ++ tailWord_275101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275104 : List Nat := [2, 1, 1, 4, 4, 1, 3, 5]
def baseStart_275104 : Nat := 118140960795 + 275104 * 2 ^ 59
def prefixEnd_275104 : Nat := 4983230072969 + 3 ^ 40 * 275104 * 2
def baseEnd_275104 : Nat := 20927493625866205634789

theorem tailTrace_275104 : CollatzResearch.WordTrace tailWord_275104 prefixEnd_275104 20927493625866205634789 := by
  unfold tailWord_275104
  simp only [CollatzResearch.WordTrace]
  refine ⟨5016933597676333433860183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6689244796901777911813577 5016933597676333433860183)
  ·
    refine ⟨7525400396514500150790275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5016933597676333433860183 7525400396514500150790275)
    ·
      refine ⟨11288100594771750226185413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7525400396514500150790275 11288100594771750226185413)
      ·
        refine ⟨2116518861519703167409765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11288100594771750226185413 2116518861519703167409765)
        ·
          refine ⟨396847286534944343889331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2116518861519703167409765 396847286534944343889331)
          ·
            refine ⟨595270929802416515833997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396847286534944343889331 595270929802416515833997)
            ·
              refine ⟨223226598675906193437749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 595270929802416515833997 223226598675906193437749)
              ·
                refine ⟨20927493625866205634789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223226598675906193437749 20927493625866205634789)
                ·
                  rfl

theorem cell21_275104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 5].length) (baseStart_275104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275104 prefixEnd_275104 := by exact prefixLift 275104
  have htrace : WordTrace (prefixWord ++ tailWord_275104) baseStart_275104 baseEnd_275104 := by
    simpa [prefixWord, tailWord_275104, baseEnd_275104] using wordTrace_append hprefix tailTrace_275104
  have hstable : (prefixWord ++ tailWord_275104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275104).length < 2 ^ (prefixWord ++ tailWord_275104).sum := by decide
  have hdescent : baseEnd_275104 < baseStart_275104 := by decide
  rcases family_descends (prefixWord ++ tailWord_275104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275132 : List Nat := [2, 2, 2, 3, 1, 1, 3, 1, 6]
def baseStart_275132 : Nat := 118140960795 + 275132 * 2 ^ 59
def prefixEnd_275132 : Nat := 4983230072969 + 3 ^ 40 * 275132 * 2
def baseEnd_275132 : Nat := 62788870859076790437643

theorem tailTrace_275132 : CollatzResearch.WordTrace tailWord_275132 prefixEnd_275132 62788870859076790437643 := by
  unfold tailWord_275132
  simp only [CollatzResearch.WordTrace]
  refine ⟨5017444219625613824869825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6689925626167485099826433 5017444219625613824869825)
  ·
    refine ⟨3763083164719210368652369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5017444219625613824869825 3763083164719210368652369)
    ·
      refine ⟨2822312373539407776489277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3763083164719210368652369 2822312373539407776489277)
      ·
        refine ⟨1058367140077277916183479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2822312373539407776489277 1058367140077277916183479)
        ·
          refine ⟨1587550710115916874275219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1058367140077277916183479 1587550710115916874275219)
          ·
            refine ⟨2381326065173875311412829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1587550710115916874275219 2381326065173875311412829)
            ·
              refine ⟨892997274440203241779811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2381326065173875311412829 892997274440203241779811)
              ·
                refine ⟨1339495911660304862669717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892997274440203241779811 1339495911660304862669717)
                ·
                  refine ⟨62788870859076790437643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1339495911660304862669717 62788870859076790437643)
                  ·
                    rfl

theorem cell21_275132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_275132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275132 prefixEnd_275132 := by exact prefixLift 275132
  have htrace : WordTrace (prefixWord ++ tailWord_275132) baseStart_275132 baseEnd_275132 := by
    simpa [prefixWord, tailWord_275132, baseEnd_275132] using wordTrace_append hprefix tailTrace_275132
  have hstable : (prefixWord ++ tailWord_275132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275132).length < 2 ^ (prefixWord ++ tailWord_275132).sum := by decide
  have hdescent : baseEnd_275132 < baseStart_275132 := by decide
  rcases family_descends (prefixWord ++ tailWord_275132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275194 : List Nat := [3, 1, 1, 1, 1, 3, 2, 6, 3]
def baseStart_275194 : Nat := 118140960795 + 275194 * 2 ^ 59
def prefixEnd_275194 : Nat := 4983230072969 + 3 ^ 40 * 275194 * 2
def baseEnd_275194 : Nat := 62803020103778460404183

theorem tailTrace_275194 : CollatzResearch.WordTrace tailWord_275194 prefixEnd_275194 62803020103778460404183 := by
  unfold tailWord_275194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2509287441256653059624159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6691433176684408158997757 2509287441256653059624159)
  ·
    refine ⟨3763931161884979589436239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2509287441256653059624159 3763931161884979589436239)
    ·
      refine ⟨5645896742827469384154359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3763931161884979589436239 5645896742827469384154359)
      ·
        refine ⟨8468845114241204076231539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5645896742827469384154359 8468845114241204076231539)
        ·
          refine ⟨12703267671361806114347309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8468845114241204076231539 12703267671361806114347309)
          ·
            refine ⟨4763725376760677292880241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12703267671361806114347309 4763725376760677292880241)
            ·
              refine ⟨3572794032570507969660181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4763725376760677292880241 3572794032570507969660181)
              ·
                refine ⟨167474720276742561077821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3572794032570507969660181 167474720276742561077821)
                ·
                  refine ⟨62803020103778460404183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167474720276742561077821 62803020103778460404183)
                  ·
                    rfl

theorem cell21_275194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_275194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275194 prefixEnd_275194 := by exact prefixLift 275194
  have htrace : WordTrace (prefixWord ++ tailWord_275194) baseStart_275194 baseEnd_275194 := by
    simpa [prefixWord, tailWord_275194, baseEnd_275194] using wordTrace_append hprefix tailTrace_275194
  have hstable : (prefixWord ++ tailWord_275194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275194).length < 2 ^ (prefixWord ++ tailWord_275194).sum := by decide
  have hdescent : baseEnd_275194 < baseStart_275194 := by decide
  rcases family_descends (prefixWord ++ tailWord_275194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275245 : List Nat := [1, 5, 3, 2, 1, 1, 1, 4, 3]
def baseStart_275245 : Nat := 118140960795 + 275245 * 2 ^ 59
def prefixEnd_275245 : Nat := 4983230072969 + 3 ^ 40 * 275245 * 2
def baseEnd_275245 : Nat := 62814658998613705054079

theorem tailTrace_275245 : CollatzResearch.WordTrace tailWord_275245 prefixEnd_275245 62814658998613705054079 := by
  unfold tailWord_275245
  simp only [CollatzResearch.WordTrace]
  refine ⟨10039009887841847948603189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6692673258561231965735459 10039009887841847948603189)
  ·
    refine ⟨941157176985173245181549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10039009887841847948603189 941157176985173245181549)
    ·
      refine ⟨352933941369439966943081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 941157176985173245181549 352933941369439966943081)
      ·
        refine ⟨264700456027079975207311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 352933941369439966943081 264700456027079975207311)
        ·
          refine ⟨397050684040619962810967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264700456027079975207311 397050684040619962810967)
          ·
            refine ⟨595576026060929944216451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397050684040619962810967 595576026060929944216451)
            ·
              refine ⟨893364039091394916324677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595576026060929944216451 893364039091394916324677)
              ·
                refine ⟨167505757329636546810877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 893364039091394916324677 167505757329636546810877)
                ·
                  refine ⟨62814658998613705054079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167505757329636546810877 62814658998613705054079)
                  ·
                    rfl

theorem cell21_275245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_275245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275245 prefixEnd_275245 := by exact prefixLift 275245
  have htrace : WordTrace (prefixWord ++ tailWord_275245) baseStart_275245 baseEnd_275245 := by
    simpa [prefixWord, tailWord_275245, baseEnd_275245] using wordTrace_append hprefix tailTrace_275245
  have hstable : (prefixWord ++ tailWord_275245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275245).length < 2 ^ (prefixWord ++ tailWord_275245).sum := by decide
  have hdescent : baseEnd_275245 < baseStart_275245 := by decide
  rcases family_descends (prefixWord ++ tailWord_275245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275287 : List Nat := [1, 1, 3, 2, 4, 2, 2, 3, 3]
def baseStart_275287 : Nat := 118140960795 + 275287 * 2 ^ 59
def prefixEnd_275287 : Nat := 4983230072969 + 3 ^ 40 * 275287 * 2
def baseEnd_275287 : Nat := 62824243970830965353993

theorem tailTrace_275287 : CollatzResearch.WordTrace tailWord_275287 prefixEnd_275287 62824243970830965353993 := by
  unfold tailWord_275287
  simp only [CollatzResearch.WordTrace]
  refine ⟨10040541753689689121632115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6693694502459792747754743 10040541753689689121632115)
  ·
    refine ⟨15060812630534533682448173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10040541753689689121632115 15060812630534533682448173)
    ·
      refine ⟨5647804736450450130918065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15060812630534533682448173 5647804736450450130918065)
      ·
        refine ⟨4235853552337837598188549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5647804736450450130918065 4235853552337837598188549)
        ·
          refine ⟨794222541063344549660353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4235853552337837598188549 794222541063344549660353)
          ·
            refine ⟨595666905797508412245265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 794222541063344549660353 595666905797508412245265)
            ·
              refine ⟨446750179348131309183949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 595666905797508412245265 446750179348131309183949)
              ·
                refine ⟨167531317255549240943981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 446750179348131309183949 167531317255549240943981)
                ·
                  refine ⟨62824243970830965353993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 167531317255549240943981 62824243970830965353993)
                  ·
                    rfl

theorem cell21_275287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 3].length) (baseStart_275287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275287 prefixEnd_275287 := by exact prefixLift 275287
  have htrace : WordTrace (prefixWord ++ tailWord_275287) baseStart_275287 baseEnd_275287 := by
    simpa [prefixWord, tailWord_275287, baseEnd_275287] using wordTrace_append hprefix tailTrace_275287
  have hstable : (prefixWord ++ tailWord_275287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275287).length < 2 ^ (prefixWord ++ tailWord_275287).sum := by decide
  have hdescent : baseEnd_275287 < baseStart_275287 := by decide
  rcases family_descends (prefixWord ++ tailWord_275287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275377 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 4]
def baseStart_275377 : Nat := 118140960795 + 275377 * 2 ^ 59
def prefixEnd_275377 : Nat := 4983230072969 + 3 ^ 40 * 275377 * 2
def baseEnd_275377 : Nat := 62844783197010808853809

theorem tailTrace_275377 : CollatzResearch.WordTrace tailWord_275377 prefixEnd_275377 62844783197010808853809 := by
  unfold tailWord_275377
  simp only [CollatzResearch.WordTrace]
  refine ⟨10043824323363634492408385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6695882882242422994938923 10043824323363634492408385)
  ·
    refine ⟨7532868242522725869306289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10043824323363634492408385 7532868242522725869306289)
    ·
      refine ⟨5649651181892044401979717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7532868242522725869306289 5649651181892044401979717)
      ·
        refine ⟨1059309596604758325371197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5649651181892044401979717 1059309596604758325371197)
        ·
          refine ⟨397241098726784372014199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1059309596604758325371197 397241098726784372014199)
          ·
            refine ⟨595861648090176558021299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397241098726784372014199 595861648090176558021299)
            ·
              refine ⟨893792472135264837031949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595861648090176558021299 893792472135264837031949)
              ·
                refine ⟨335172177050724313886981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 893792472135264837031949 335172177050724313886981)
                ·
                  refine ⟨62844783197010808853809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335172177050724313886981 62844783197010808853809)
                  ·
                    rfl

theorem cell21_275377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 4].length) (baseStart_275377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275377 prefixEnd_275377 := by exact prefixLift 275377
  have htrace : WordTrace (prefixWord ++ tailWord_275377) baseStart_275377 baseEnd_275377 := by
    simpa [prefixWord, tailWord_275377, baseEnd_275377] using wordTrace_append hprefix tailTrace_275377
  have hstable : (prefixWord ++ tailWord_275377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275377).length < 2 ^ (prefixWord ++ tailWord_275377).sum := by decide
  have hdescent : baseEnd_275377 < baseStart_275377 := by decide
  rcases family_descends (prefixWord ++ tailWord_275377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275588 : List Nat := [2, 3, 2, 1, 2, 2, 1, 4, 4]
def baseStart_275588 : Nat := 118140960795 + 275588 * 2 ^ 59
def prefixEnd_275588 : Nat := 4983230072969 + 3 ^ 40 * 275588 * 2
def baseEnd_275588 : Nat := 62892936271721330836711

theorem tailTrace_275588 : CollatzResearch.WordTrace tailWord_275588 prefixEnd_275588 62892936271721330836711 := by
  unfold tailWord_275588
  simp only [CollatzResearch.WordTrace]
  refine ⟨5025760062799608764169709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6701013417066145018892945 5025760062799608764169709)
  ·
    refine ⟨1884660023549853286563641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5025760062799608764169709 1884660023549853286563641)
    ·
      refine ⟨1413495017662389964922731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1884660023549853286563641 1413495017662389964922731)
      ·
        refine ⟨2120242526493584947384097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413495017662389964922731 2120242526493584947384097)
        ·
          refine ⟨1590181894870188710538073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2120242526493584947384097 1590181894870188710538073)
          ·
            refine ⟨1192636421152641532903555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1590181894870188710538073 1192636421152641532903555)
            ·
              refine ⟨1788954631728962299355333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192636421152641532903555 1788954631728962299355333)
              ·
                refine ⟨335428993449180431129125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1788954631728962299355333 335428993449180431129125)
                ·
                  refine ⟨62892936271721330836711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335428993449180431129125 62892936271721330836711)
                  ·
                    rfl

theorem cell21_275588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_275588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275588 prefixEnd_275588 := by exact prefixLift 275588
  have htrace : WordTrace (prefixWord ++ tailWord_275588) baseStart_275588 baseEnd_275588 := by
    simpa [prefixWord, tailWord_275588, baseEnd_275588] using wordTrace_append hprefix tailTrace_275588
  have hstable : (prefixWord ++ tailWord_275588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275588).length < 2 ^ (prefixWord ++ tailWord_275588).sum := by decide
  have hdescent : baseEnd_275588 < baseStart_275588 := by decide
  rcases family_descends (prefixWord ++ tailWord_275588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275670 : List Nat := [5, 2, 1, 2, 3, 1, 2, 5]
def baseStart_275670 : Nat := 118140960795 + 275670 * 2 ^ 59
def prefixEnd_275670 : Nat := 4983230072969 + 3 ^ 40 * 275670 * 2
def baseEnd_275670 : Nat := 20970549929635803489959

theorem tailTrace_275670 : CollatzResearch.WordTrace tailWord_275670 prefixEnd_275670 20970549929635803489959 := by
  unfold tailWord_275670
  simp only [CollatzResearch.WordTrace]
  refine ⟨628406931956384095801529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6703007274201430355216309 628406931956384095801529)
  ·
    refine ⟨471305198967288071851147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 628406931956384095801529 471305198967288071851147)
    ·
      refine ⟨706957798450932107776721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 471305198967288071851147 706957798450932107776721)
      ·
        refine ⟨530218348838199080832541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 706957798450932107776721 530218348838199080832541)
        ·
          refine ⟨198831880814324655312203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 530218348838199080832541 198831880814324655312203)
          ·
            refine ⟨298247821221486982968305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198831880814324655312203 298247821221486982968305)
            ·
              refine ⟨223685865916115237226229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298247821221486982968305 223685865916115237226229)
              ·
                refine ⟨20970549929635803489959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223685865916115237226229 20970549929635803489959)
                ·
                  rfl

theorem cell21_275670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_275670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275670 prefixEnd_275670 := by exact prefixLift 275670
  have htrace : WordTrace (prefixWord ++ tailWord_275670) baseStart_275670 baseEnd_275670 := by
    simpa [prefixWord, tailWord_275670, baseEnd_275670] using wordTrace_append hprefix tailTrace_275670
  have hstable : (prefixWord ++ tailWord_275670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275670).length < 2 ^ (prefixWord ++ tailWord_275670).sum := by decide
  have hdescent : baseEnd_275670 < baseStart_275670 := by decide
  rcases family_descends (prefixWord ++ tailWord_275670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275695 : List Nat := [1, 1, 2, 1, 8, 1, 7]
def baseStart_275695 : Nat := 118140960795 + 275695 * 2 ^ 59
def prefixEnd_275695 : Nat := 4983230072969 + 3 ^ 40 * 275695 * 2
def baseEnd_275695 : Nat := 6990817236612546950351

theorem tailTrace_275695 : CollatzResearch.WordTrace tailWord_275695 prefixEnd_275695 6990817236612546950351 := by
  unfold tailWord_275695
  simp only [CollatzResearch.WordTrace]
  refine ⟨10055422736211574802484539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6703615157474383201656359 10055422736211574802484539)
  ·
    refine ⟨15083134104317362203726809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10055422736211574802484539 15083134104317362203726809)
    ·
      refine ⟨11312350578238021652795107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15083134104317362203726809 11312350578238021652795107)
      ·
        refine ⟨16968525867357032479192661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11312350578238021652795107 16968525867357032479192661)
        ·
          refine ⟨198849912508090224365539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 16968525867357032479192661 198849912508090224365539)
          ·
            refine ⟨298274868762135336548309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198849912508090224365539 298274868762135336548309)
            ·
              refine ⟨6990817236612546950351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 298274868762135336548309 6990817236612546950351)
              ·
                rfl

theorem cell21_275695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 7].length) (baseStart_275695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275695 prefixEnd_275695 := by exact prefixLift 275695
  have htrace : WordTrace (prefixWord ++ tailWord_275695) baseStart_275695 baseEnd_275695 := by
    simpa [prefixWord, tailWord_275695, baseEnd_275695] using wordTrace_append hprefix tailTrace_275695
  have hstable : (prefixWord ++ tailWord_275695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275695).length < 2 ^ (prefixWord ++ tailWord_275695).sum := by decide
  have hdescent : baseEnd_275695 < baseStart_275695 := by decide
  rcases family_descends (prefixWord ++ tailWord_275695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275754 : List Nat := [3, 1, 4, 2, 1, 10]
def baseStart_275754 : Nat := 118140960795 + 275754 * 2 ^ 59
def prefixEnd_275754 : Nat := 4983230072969 + 3 ^ 40 * 275754 * 2
def baseEnd_275754 : Nat := 2330771101234886335915

theorem tailTrace_275754 : CollatzResearch.WordTrace tailWord_275754 prefixEnd_275754 2330771101234886335915 := by
  unfold tailWord_275754
  simp only [CollatzResearch.WordTrace]
  refine ⟨2514393660749456969720579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6705049761998551919254877 2514393660749456969720579)
  ·
    refine ⟨3771590491124185454580869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2514393660749456969720579 3771590491124185454580869)
    ·
      refine ⟨707173217085784772733913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3771590491124185454580869 707173217085784772733913)
      ·
        refine ⟨530379912814338579550435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 707173217085784772733913 530379912814338579550435)
        ·
          refine ⟨795569869221507869325653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530379912814338579550435 795569869221507869325653)
          ·
            refine ⟨2330771101234886335915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 795569869221507869325653 2330771101234886335915)
            ·
              rfl

theorem cell21_275754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 10].length) (baseStart_275754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275754 prefixEnd_275754 := by exact prefixLift 275754
  have htrace : WordTrace (prefixWord ++ tailWord_275754) baseStart_275754 baseEnd_275754 := by
    simpa [prefixWord, tailWord_275754, baseEnd_275754] using wordTrace_append hprefix tailTrace_275754
  have hstable : (prefixWord ++ tailWord_275754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275754).length < 2 ^ (prefixWord ++ tailWord_275754).sum := by decide
  have hdescent : baseEnd_275754 < baseStart_275754 := by decide
  rcases family_descends (prefixWord ++ tailWord_275754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275757 : List Nat := [1, 5, 3, 1, 1, 1, 1, 4, 4]
def baseStart_275757 : Nat := 118140960795 + 275757 * 2 ^ 59
def prefixEnd_275757 : Nat := 4983230072969 + 3 ^ 40 * 275757 * 2
def baseEnd_275757 : Nat := 62931504374214592519699

theorem tailTrace_275757 : CollatzResearch.WordTrace tailWord_275757 prefixEnd_275757 62931504374214592519699 := by
  unfold tailWord_275757
  simp only [CollatzResearch.WordTrace]
  refine ⟨10057684061986959391241525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6705122707991306260827683 10057684061986959391241525)
  ·
    refine ⟨942907880811277442928893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10057684061986959391241525 942907880811277442928893)
    ·
      refine ⟨353590455304229041098335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 942907880811277442928893 353590455304229041098335)
      ·
        refine ⟨530385682956343561647503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353590455304229041098335 530385682956343561647503)
        ·
          refine ⟨795578524434515342471255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530385682956343561647503 795578524434515342471255)
          ·
            refine ⟨1193367786651773013706883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795578524434515342471255 1193367786651773013706883)
            ·
              refine ⟨1790051679977659520560325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193367786651773013706883 1790051679977659520560325)
              ·
                refine ⟨335634689995811160105061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1790051679977659520560325 335634689995811160105061)
                ·
                  refine ⟨62931504374214592519699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335634689995811160105061 62931504374214592519699)
                  ·
                    rfl

theorem cell21_275757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_275757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275757 prefixEnd_275757 := by exact prefixLift 275757
  have htrace : WordTrace (prefixWord ++ tailWord_275757) baseStart_275757 baseEnd_275757 := by
    simpa [prefixWord, tailWord_275757, baseEnd_275757] using wordTrace_append hprefix tailTrace_275757
  have hstable : (prefixWord ++ tailWord_275757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275757).length < 2 ^ (prefixWord ++ tailWord_275757).sum := by decide
  have hdescent : baseEnd_275757 < baseStart_275757 := by decide
  rcases family_descends (prefixWord ++ tailWord_275757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275768 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_275768 : Nat := 118140960795 + 275768 * 2 ^ 59
def prefixEnd_275768 : Nat := 4983230072969 + 3 ^ 40 * 275768 * 2
def baseEnd_275768 : Nat := 62934014724081017836343

theorem tailTrace_275768 : CollatzResearch.WordTrace tailWord_275768 prefixEnd_275768 62934014724081017836343 := by
  unfold tailWord_275768
  simp only [CollatzResearch.WordTrace]
  refine ⟨5029042632473554134945979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6705390176631405513261305 5029042632473554134945979)
  ·
    refine ⟨7543563948710331202418969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5029042632473554134945979 7543563948710331202418969)
    ·
      refine ⟨5657672961532748401814227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7543563948710331202418969 5657672961532748401814227)
      ·
        refine ⟨8486509442299122602721341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5657672961532748401814227 8486509442299122602721341)
        ·
          refine ⟨3182441040862170976020503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8486509442299122602721341 3182441040862170976020503)
          ·
            refine ⟨4773661561293256464030755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182441040862170976020503 4773661561293256464030755)
            ·
              refine ⟨7160492341939884696046133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4773661561293256464030755 7160492341939884696046133)
              ·
                refine ⟨671296157056864190254325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7160492341939884696046133 671296157056864190254325)
                ·
                  refine ⟨62934014724081017836343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 671296157056864190254325 62934014724081017836343)
                  ·
                    rfl

theorem cell21_275768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_275768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275768 prefixEnd_275768 := by exact prefixLift 275768
  have htrace : WordTrace (prefixWord ++ tailWord_275768) baseStart_275768 baseEnd_275768 := by
    simpa [prefixWord, tailWord_275768, baseEnd_275768] using wordTrace_append hprefix tailTrace_275768
  have hstable : (prefixWord ++ tailWord_275768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275768).length < 2 ^ (prefixWord ++ tailWord_275768).sum := by decide
  have hdescent : baseEnd_275768 < baseStart_275768 := by decide
  rcases family_descends (prefixWord ++ tailWord_275768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275813 : List Nat := [1, 3, 1, 3, 1, 2, 10]
def baseStart_275813 : Nat := 118140960795 + 275813 * 2 ^ 59
def prefixEnd_275813 : Nat := 4983230072969 + 3 ^ 40 * 275813 * 2
def baseEnd_275813 : Nat := 6993809370796771065139

theorem tailTrace_275813 : CollatzResearch.WordTrace tailWord_275813 prefixEnd_275813 6993809370796771065139 := by
  unfold tailWord_275813
  simp only [CollatzResearch.WordTrace]
  refine ⟨10059726549784080955280093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6706484366522720636853395 10059726549784080955280093)
  ·
    refine ⟨3772397456169030358230035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10059726549784080955280093 3772397456169030358230035)
    ·
      refine ⟨5658596184253545537345053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3772397456169030358230035 5658596184253545537345053)
      ·
        refine ⟨2121973569095079576504395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5658596184253545537345053 2121973569095079576504395)
        ·
          refine ⟨3182960353642619364756593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2121973569095079576504395 3182960353642619364756593)
          ·
            refine ⟨2387220265231964523567445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3182960353642619364756593 2387220265231964523567445)
            ·
              refine ⟨6993809370796771065139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2387220265231964523567445 6993809370796771065139)
              ·
                rfl

theorem cell21_275813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 10].length) (baseStart_275813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275813 prefixEnd_275813 := by exact prefixLift 275813
  have htrace : WordTrace (prefixWord ++ tailWord_275813) baseStart_275813 baseEnd_275813 := by
    simpa [prefixWord, tailWord_275813, baseEnd_275813] using wordTrace_append hprefix tailTrace_275813
  have hstable : (prefixWord ++ tailWord_275813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275813).length < 2 ^ (prefixWord ++ tailWord_275813).sum := by decide
  have hdescent : baseEnd_275813 < baseStart_275813 := by decide
  rcases family_descends (prefixWord ++ tailWord_275813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275816 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 6]
def baseStart_275816 : Nat := 118140960795 + 275816 * 2 ^ 59
def prefixEnd_275816 : Nat := 4983230072969 + 3 ^ 40 * 275816 * 2
def baseEnd_275816 : Nat := 62944968978043601036245

theorem tailTrace_275816 : CollatzResearch.WordTrace tailWord_275816 prefixEnd_275816 62944968978043601036245 := by
  unfold tailWord_275816
  simp only [CollatzResearch.WordTrace]
  refine ⟨5029917984386606233819651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6706557312515474978426201 5029917984386606233819651)
  ·
    refine ⟨7544876976579909350729477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5029917984386606233819651 7544876976579909350729477)
    ·
      refine ⟨1414664433108733003261777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7544876976579909350729477 1414664433108733003261777)
      ·
        refine ⟨1060998324831549752446333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1414664433108733003261777 1060998324831549752446333)
        ·
          refine ⟨397874371811831157167375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1060998324831549752446333 397874371811831157167375)
          ·
            refine ⟨596811557717746735751063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397874371811831157167375 596811557717746735751063)
            ·
              refine ⟨895217336576620103626595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 596811557717746735751063 895217336576620103626595)
              ·
                refine ⟨1342826004864930155439893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895217336576620103626595 1342826004864930155439893)
                ·
                  refine ⟨62944968978043601036245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1342826004864930155439893 62944968978043601036245)
                  ·
                    rfl

theorem cell21_275816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_275816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275816 prefixEnd_275816 := by exact prefixLift 275816
  have htrace : WordTrace (prefixWord ++ tailWord_275816) baseStart_275816 baseEnd_275816 := by
    simpa [prefixWord, tailWord_275816, baseEnd_275816] using wordTrace_append hprefix tailTrace_275816
  have hstable : (prefixWord ++ tailWord_275816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275816).length < 2 ^ (prefixWord ++ tailWord_275816).sum := by decide
  have hdescent : baseEnd_275816 < baseStart_275816 := by decide
  rcases family_descends (prefixWord ++ tailWord_275816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275847 : List Nat := [1, 1, 4, 2, 2, 4, 2, 5]
def baseStart_275847 : Nat := 118140960795 + 275847 * 2 ^ 59
def prefixEnd_275847 : Nat := 4983230072969 + 3 ^ 40 * 275847 * 2
def baseEnd_275847 : Nat := 20984014533464812006505

theorem tailTrace_275847 : CollatzResearch.WordTrace tailWord_275847 prefixEnd_275847 20984014533464812006505 := by
  unfold tailWord_275847
  simp only [CollatzResearch.WordTrace]
  refine ⟨10060966631660904762017795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6707311087773936508011863 10060966631660904762017795)
  ·
    refine ⟨15091449947491357143026693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10060966631660904762017795 15091449947491357143026693)
    ·
      refine ⟨2829646865154629464317505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15091449947491357143026693 2829646865154629464317505)
      ·
        refine ⟨2122235148865972098238129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2829646865154629464317505 2122235148865972098238129)
        ·
          refine ⟨1591676361649479073678597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2122235148865972098238129 1591676361649479073678597)
          ·
            refine ⟨298439317809277326314737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1591676361649479073678597 298439317809277326314737)
            ·
              refine ⟨223829488356957994736053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298439317809277326314737 223829488356957994736053)
              ·
                refine ⟨20984014533464812006505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 223829488356957994736053 20984014533464812006505)
                ·
                  rfl

theorem cell21_275847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 5].length) (baseStart_275847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275847 prefixEnd_275847 := by exact prefixLift 275847
  have htrace : WordTrace (prefixWord ++ tailWord_275847) baseStart_275847 baseEnd_275847 := by
    simpa [prefixWord, tailWord_275847, baseEnd_275847] using wordTrace_append hprefix tailTrace_275847
  have hstable : (prefixWord ++ tailWord_275847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275847).length < 2 ^ (prefixWord ++ tailWord_275847).sum := by decide
  have hdescent : baseEnd_275847 < baseStart_275847 := by decide
  rcases family_descends (prefixWord ++ tailWord_275847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275875 : List Nat := [1, 1, 1, 4, 1, 3, 2, 4, 4]
def baseStart_275875 : Nat := 118140960795 + 275875 * 2 ^ 59
def prefixEnd_275875 : Nat := 4983230072969 + 3 ^ 40 * 275875 * 2
def baseEnd_275875 : Nat := 62958433581872609552791

theorem tailTrace_275875 : CollatzResearch.WordTrace tailWord_275875 prefixEnd_275875 62958433581872609552791 := by
  unfold tailWord_275875
  simp only [CollatzResearch.WordTrace]
  refine ⟨10061987875559465544037079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6707991917039643696024719 10061987875559465544037079)
  ·
    refine ⟨15092981813339198316055619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10061987875559465544037079 15092981813339198316055619)
    ·
      refine ⟨22639472720008797474083429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15092981813339198316055619 22639472720008797474083429)
      ·
        refine ⟨4244901135001649526390643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22639472720008797474083429 4244901135001649526390643)
        ·
          refine ⟨6367351702502474289585965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244901135001649526390643 6367351702502474289585965)
          ·
            refine ⟨2387756888438427858594737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6367351702502474289585965 2387756888438427858594737)
            ·
              refine ⟨1790817666328820893946053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2387756888438427858594737 1790817666328820893946053)
              ·
                refine ⟨335778312436653917614885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1790817666328820893946053 335778312436653917614885)
                ·
                  refine ⟨62958433581872609552791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335778312436653917614885 62958433581872609552791)
                  ·
                    rfl

theorem cell21_275875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 4, 4].length) (baseStart_275875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275875 prefixEnd_275875 := by exact prefixLift 275875
  have htrace : WordTrace (prefixWord ++ tailWord_275875) baseStart_275875 baseEnd_275875 := by
    simpa [prefixWord, tailWord_275875, baseEnd_275875] using wordTrace_append hprefix tailTrace_275875
  have hstable : (prefixWord ++ tailWord_275875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275875).length < 2 ^ (prefixWord ++ tailWord_275875).sum := by decide
  have hdescent : baseEnd_275875 < baseStart_275875 := by decide
  rcases family_descends (prefixWord ++ tailWord_275875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275951 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 4]
def baseStart_275951 : Nat := 118140960795 + 275951 * 2 ^ 59
def prefixEnd_275951 : Nat := 4983230072969 + 3 ^ 40 * 275951 * 2
def baseEnd_275951 : Nat := 62975777817313366285969

theorem tailTrace_275951 : CollatzResearch.WordTrace tailWord_275951 prefixEnd_275951 62975777817313366285969 := by
  unfold tailWord_275951
  simp only [CollatzResearch.WordTrace]
  refine ⟨10064759823284130523803707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6709839882189420349202471 10064759823284130523803707)
  ·
    refine ⟨15097139734926195785705561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10064759823284130523803707 15097139734926195785705561)
    ·
      refine ⟨11322854801194646839279171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15097139734926195785705561 11322854801194646839279171)
      ·
        refine ⟨16984282201791970258918757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11322854801194646839279171 16984282201791970258918757)
        ·
          refine ⟨3184552912835994423547267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16984282201791970258918757 3184552912835994423547267)
          ·
            refine ⟨4776829369253991635320901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3184552912835994423547267 4776829369253991635320901)
            ·
              refine ⟨895655506735123431622669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4776829369253991635320901 895655506735123431622669)
              ·
                refine ⟨335870815025671286858501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 895655506735123431622669 335870815025671286858501)
                ·
                  refine ⟨62975777817313366285969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 335870815025671286858501 62975777817313366285969)
                  ·
                    rfl

theorem cell21_275951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 4].length) (baseStart_275951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275951 prefixEnd_275951 := by exact prefixLift 275951
  have htrace : WordTrace (prefixWord ++ tailWord_275951) baseStart_275951 baseEnd_275951 := by
    simpa [prefixWord, tailWord_275951, baseEnd_275951] using wordTrace_append hprefix tailTrace_275951
  have hstable : (prefixWord ++ tailWord_275951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275951).length < 2 ^ (prefixWord ++ tailWord_275951).sum := by decide
  have hdescent : baseEnd_275951 < baseStart_275951 := by decide
  rcases family_descends (prefixWord ++ tailWord_275951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_275982 : List Nat := [4, 1, 1, 2, 4, 1, 8]
def baseStart_275982 : Nat := 118140960795 + 275982 * 2 ^ 59
def prefixEnd_275982 : Nat := 4983230072969 + 3 ^ 40 * 275982 * 2
def baseEnd_275982 : Nat := 6998094715518244585471

theorem tailTrace_275982 : CollatzResearch.WordTrace tailWord_275982 prefixEnd_275982 6998094715518244585471 := by
  unfold tailWord_275982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1258236310771477852272775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6710593657447881878788133 1258236310771477852272775)
  ·
    refine ⟨1887354466157216778409163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1258236310771477852272775 1887354466157216778409163)
    ·
      refine ⟨2831031699235825167613745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1887354466157216778409163 2831031699235825167613745)
      ·
        refine ⟨2123273774426868875710309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2831031699235825167613745 2123273774426868875710309)
        ·
          refine ⟨398113832705037914195683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2123273774426868875710309 398113832705037914195683)
          ·
            refine ⟨597170749057556871293525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398113832705037914195683 597170749057556871293525)
            ·
              refine ⟨6998094715518244585471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 597170749057556871293525 6998094715518244585471)
              ·
                rfl

theorem cell21_275982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 8].length) (baseStart_275982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_275982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_275982 prefixEnd_275982 := by exact prefixLift 275982
  have htrace : WordTrace (prefixWord ++ tailWord_275982) baseStart_275982 baseEnd_275982 := by
    simpa [prefixWord, tailWord_275982, baseEnd_275982] using wordTrace_append hprefix tailTrace_275982
  have hstable : (prefixWord ++ tailWord_275982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_275982).length < 2 ^ (prefixWord ++ tailWord_275982).sum := by decide
  have hdescent : baseEnd_275982 < baseStart_275982 := by decide
  rcases family_descends (prefixWord ++ tailWord_275982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276089 : List Nat := [1, 2, 1, 3, 3, 1, 2, 5, 3]
def baseStart_276089 : Nat := 118140960795 + 276089 * 2 ^ 59
def prefixEnd_276089 : Nat := 4983230072969 + 3 ^ 40 * 276089 * 2
def baseEnd_276089 : Nat := 63007271297455792985687

theorem tailTrace_276089 : CollatzResearch.WordTrace tailWord_276089 prefixEnd_276089 63007271297455792985687 := by
  unfold tailWord_276089
  simp only [CollatzResearch.WordTrace]
  refine ⟨10069793096784180092327321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6713195397856120061551547 10069793096784180092327321)
  ·
    refine ⟨7552344822588135069245491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10069793096784180092327321 7552344822588135069245491)
    ·
      refine ⟨11328517233882202603868237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7552344822588135069245491 11328517233882202603868237)
      ·
        refine ⟨4248193962705825976450589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11328517233882202603868237 4248193962705825976450589)
        ·
          refine ⟨1593072736014684741168971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4248193962705825976450589 1593072736014684741168971)
          ·
            refine ⟨2389609104022027111753457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593072736014684741168971 2389609104022027111753457)
            ·
              refine ⟨1792206828016520333815093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2389609104022027111753457 1792206828016520333815093)
              ·
                refine ⟨168019390126548781295165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1792206828016520333815093 168019390126548781295165)
                ·
                  refine ⟨63007271297455792985687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168019390126548781295165 63007271297455792985687)
                  ·
                    rfl

theorem cell21_276089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5, 3].length) (baseStart_276089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276089 prefixEnd_276089 := by exact prefixLift 276089
  have htrace : WordTrace (prefixWord ++ tailWord_276089) baseStart_276089 baseEnd_276089 := by
    simpa [prefixWord, tailWord_276089, baseEnd_276089] using wordTrace_append hprefix tailTrace_276089
  have hstable : (prefixWord ++ tailWord_276089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276089).length < 2 ^ (prefixWord ++ tailWord_276089).sum := by decide
  have hdescent : baseEnd_276089 < baseStart_276089 := by decide
  rcases family_descends (prefixWord ++ tailWord_276089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276103 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 4]
def baseStart_276103 : Nat := 118140960795 + 276103 * 2 ^ 59
def prefixEnd_276103 : Nat := 4983230072969 + 3 ^ 40 * 276103 * 2
def baseEnd_276103 : Nat := 63010466288194879752325

theorem tailTrace_276103 : CollatzResearch.WordTrace tailWord_276103 prefixEnd_276103 63010466288194879752325 := by
  unfold tailWord_276103
  simp only [CollatzResearch.WordTrace]
  refine ⟨10070303718733460483336963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6713535812488973655557975 10070303718733460483336963)
  ·
    refine ⟨15105455578100190725005445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10070303718733460483336963 15105455578100190725005445)
    ·
      refine ⟨2832272920893785760938521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15105455578100190725005445 2832272920893785760938521)
      ·
        refine ⟨2124204690670339320703891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2832272920893785760938521 2124204690670339320703891)
        ·
          refine ⟨3186307036005508981055837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2124204690670339320703891 3186307036005508981055837)
          ·
            refine ⟨1194865138502065867895939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3186307036005508981055837 1194865138502065867895939)
            ·
              refine ⟨1792297707753098801843909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194865138502065867895939 1792297707753098801843909)
              ·
                refine ⟨336055820203706025345733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1792297707753098801843909 336055820203706025345733)
                ·
                  refine ⟨63010466288194879752325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 336055820203706025345733 63010466288194879752325)
                  ·
                    rfl

theorem cell21_276103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 4].length) (baseStart_276103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276103 prefixEnd_276103 := by exact prefixLift 276103
  have htrace : WordTrace (prefixWord ++ tailWord_276103) baseStart_276103 baseEnd_276103 := by
    simpa [prefixWord, tailWord_276103, baseEnd_276103] using wordTrace_append hprefix tailTrace_276103
  have hstable : (prefixWord ++ tailWord_276103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276103).length < 2 ^ (prefixWord ++ tailWord_276103).sum := by decide
  have hdescent : baseEnd_276103 < baseStart_276103 := by decide
  rcases family_descends (prefixWord ++ tailWord_276103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276106 : List Nat := [3, 1, 2, 3, 2, 2, 1, 4, 3]
def baseStart_276106 : Nat := 118140960795 + 276106 * 2 ^ 59
def prefixEnd_276106 : Nat := 4983230072969 + 3 ^ 40 * 276106 * 2
def baseEnd_276106 : Nat := 63011150929067541202319

theorem tailTrace_276106 : CollatzResearch.WordTrace tailWord_276106 prefixEnd_276106 63011150929067541202319 := by
  unfold tailWord_276106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517603284430647998924043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6713608758481727997130781 2517603284430647998924043)
  ·
    refine ⟨3776404926645971998386065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2517603284430647998924043 3776404926645971998386065)
    ·
      refine ⟨2832303694984478998789549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3776404926645971998386065 2832303694984478998789549)
      ·
        refine ⟨1062113885619179624546081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2832303694984478998789549 1062113885619179624546081)
        ·
          refine ⟨796585414214384718409561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1062113885619179624546081 796585414214384718409561)
          ·
            refine ⟨597439060660788538807171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 796585414214384718409561 597439060660788538807171)
            ·
              refine ⟨896158590991182808210757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597439060660788538807171 896158590991182808210757)
              ·
                refine ⟨168029735810846776539517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 896158590991182808210757 168029735810846776539517)
                ·
                  refine ⟨63011150929067541202319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168029735810846776539517 63011150929067541202319)
                  ·
                    rfl

theorem cell21_276106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_276106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276106 prefixEnd_276106 := by exact prefixLift 276106
  have htrace : WordTrace (prefixWord ++ tailWord_276106) baseStart_276106 baseEnd_276106 := by
    simpa [prefixWord, tailWord_276106, baseEnd_276106] using wordTrace_append hprefix tailTrace_276106
  have hstable : (prefixWord ++ tailWord_276106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276106).length < 2 ^ (prefixWord ++ tailWord_276106).sum := by decide
  have hdescent : baseEnd_276106 < baseStart_276106 := by decide
  rcases family_descends (prefixWord ++ tailWord_276106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276269 : List Nat := [1, 5, 3, 12]
def baseStart_276269 : Nat := 118140960795 + 276269 * 2 ^ 59
def prefixEnd_276269 : Nat := 4983230072969 + 3 ^ 40 * 276269 * 2
def baseEnd_276269 : Nat := 259458229423108971133

theorem tailTrace_276269 : CollatzResearch.WordTrace tailWord_276269 prefixEnd_276269 259458229423108971133 := by
  unfold tailWord_276269
  simp only [CollatzResearch.WordTrace]
  refine ⟨10076358236132070833879861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6717572157421380555919907 10076358236132070833879861)
  ·
    refine ⟨944658584637381640676237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10076358236132070833879861 944658584637381640676237)
    ·
      refine ⟨354246969239018115253589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 944658584637381640676237 354246969239018115253589)
      ·
        refine ⟨259458229423108971133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 354246969239018115253589 259458229423108971133)
        ·
          rfl

theorem cell21_276269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 12].length) (baseStart_276269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276269 prefixEnd_276269 := by exact prefixLift 276269
  have htrace : WordTrace (prefixWord ++ tailWord_276269) baseStart_276269 baseEnd_276269 := by
    simpa [prefixWord, tailWord_276269, baseEnd_276269] using wordTrace_append hprefix tailTrace_276269
  have hstable : (prefixWord ++ tailWord_276269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276269).length < 2 ^ (prefixWord ++ tailWord_276269).sum := by decide
  have hdescent : baseEnd_276269 < baseStart_276269 := by decide
  rcases family_descends (prefixWord ++ tailWord_276269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276275 : List Nat := [1, 1, 1, 2, 7, 2, 2, 2, 3]
def baseStart_276275 : Nat := 118140960795 + 276275 * 2 ^ 59
def prefixEnd_276275 : Nat := 4983230072969 + 3 ^ 40 * 276275 * 2
def baseEnd_276275 : Nat := 63049719031560802885307

theorem tailTrace_276275 : CollatzResearch.WordTrace tailWord_276275 prefixEnd_276275 63049719031560802885307 := by
  unfold tailWord_276275
  simp only [CollatzResearch.WordTrace]
  refine ⟨10076577074110333858598279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6717718049406889239065519 10076577074110333858598279)
  ·
    refine ⟨15114865611165500787897419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10076577074110333858598279 15114865611165500787897419)
    ·
      refine ⟨22672298416748251181846129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15114865611165500787897419 22672298416748251181846129)
      ·
        refine ⟨17004223812561188386384597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22672298416748251181846129 17004223812561188386384597)
        ·
          refine ⟨398536495606902852805889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17004223812561188386384597 398536495606902852805889)
          ·
            refine ⟨298902371705177139604417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398536495606902852805889 298902371705177139604417)
            ·
              refine ⟨224176778778882854703313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298902371705177139604417 224176778778882854703313)
              ·
                refine ⟨168132584084162141027485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224176778778882854703313 168132584084162141027485)
                ·
                  refine ⟨63049719031560802885307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168132584084162141027485 63049719031560802885307)
                  ·
                    rfl

theorem cell21_276275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 2, 3].length) (baseStart_276275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276275 prefixEnd_276275 := by exact prefixLift 276275
  have htrace : WordTrace (prefixWord ++ tailWord_276275) baseStart_276275 baseEnd_276275 := by
    simpa [prefixWord, tailWord_276275, baseEnd_276275] using wordTrace_append hprefix tailTrace_276275
  have hstable : (prefixWord ++ tailWord_276275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276275).length < 2 ^ (prefixWord ++ tailWord_276275).sum := by decide
  have hdescent : baseEnd_276275 < baseStart_276275 := by decide
  rcases family_descends (prefixWord ++ tailWord_276275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276286 : List Nat := [4, 2, 1, 2, 2, 1, 3, 6]
def baseStart_276286 : Nat := 118140960795 + 276286 * 2 ^ 59
def prefixEnd_276286 : Nat := 4983230072969 + 3 ^ 40 * 276286 * 2
def baseEnd_276286 : Nat := 21017409793809076067317

theorem tailTrace_276286 : CollatzResearch.WordTrace tailWord_276286 prefixEnd_276286 21017409793809076067317 := by
  unfold tailWord_276286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259622284633810342156089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6717985518046988491499141 1259622284633810342156089)
  ·
    refine ⟨944716713475357756617067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1259622284633810342156089 944716713475357756617067)
    ·
      refine ⟨1417075070213036634925601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 944716713475357756617067 1417075070213036634925601)
      ·
        refine ⟨1062806302659777476194201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1417075070213036634925601 1062806302659777476194201)
        ·
          refine ⟨797104726994833107145651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1062806302659777476194201 797104726994833107145651)
          ·
            refine ⟨1195657090492249660718477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797104726994833107145651 1195657090492249660718477)
            ·
              refine ⟨448371408934593622769429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1195657090492249660718477 448371408934593622769429)
              ·
                refine ⟨21017409793809076067317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 448371408934593622769429 21017409793809076067317)
                ·
                  rfl

theorem cell21_276286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_276286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276286 prefixEnd_276286 := by exact prefixLift 276286
  have htrace : WordTrace (prefixWord ++ tailWord_276286) baseStart_276286 baseEnd_276286 := by
    simpa [prefixWord, tailWord_276286, baseEnd_276286] using wordTrace_append hprefix tailTrace_276286
  have hstable : (prefixWord ++ tailWord_276286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276286).length < 2 ^ (prefixWord ++ tailWord_276286).sum := by decide
  have hdescent : baseEnd_276286 < baseStart_276286 := by decide
  rcases family_descends (prefixWord ++ tailWord_276286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276314 : List Nat := [3, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_276314 : Nat := 118140960795 + 276314 * 2 ^ 59
def prefixEnd_276314 : Nat := 4983230072969 + 3 ^ 40 * 276314 * 2
def baseEnd_276314 : Nat := 63058619362905401735227

theorem tailTrace_276314 : CollatzResearch.WordTrace tailWord_276314 prefixEnd_276314 63058619362905401735227 := by
  unfold tailWord_276314
  simp only [CollatzResearch.WordTrace]
  refine ⟨2519499880242260879816999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6718666347312695679511997 2519499880242260879816999)
  ·
    refine ⟨3779249820363391319725499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2519499880242260879816999 3779249820363391319725499)
    ·
      refine ⟨5668874730545086979588249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3779249820363391319725499 5668874730545086979588249)
      ·
        refine ⟨4251656047908815234691187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5668874730545086979588249 4251656047908815234691187)
        ·
          refine ⟨6377484071863222852036781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4251656047908815234691187 6377484071863222852036781)
          ·
            refine ⟨2391556526948708569513793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6377484071863222852036781 2391556526948708569513793)
            ·
              refine ⟨1793667395211531427135345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2391556526948708569513793 1793667395211531427135345)
              ·
                refine ⟨1345250546408648570351509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793667395211531427135345 1345250546408648570351509)
                ·
                  refine ⟨63058619362905401735227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1345250546408648570351509 63058619362905401735227)
                  ·
                    rfl

theorem cell21_276314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_276314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276314 prefixEnd_276314 := by exact prefixLift 276314
  have htrace : WordTrace (prefixWord ++ tailWord_276314) baseStart_276314 baseEnd_276314 := by
    simpa [prefixWord, tailWord_276314, baseEnd_276314] using wordTrace_append hprefix tailTrace_276314
  have hstable : (prefixWord ++ tailWord_276314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276314).length < 2 ^ (prefixWord ++ tailWord_276314).sum := by decide
  have hdescent : baseEnd_276314 < baseStart_276314 := by decide
  rcases family_descends (prefixWord ++ tailWord_276314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276334 : List Nat := [4, 1, 2, 3, 1, 1, 2, 4, 3]
def baseStart_276334 : Nat := 118140960795 + 276334 * 2 ^ 59
def prefixEnd_276334 : Nat := 4983230072969 + 3 ^ 40 * 276334 * 2
def baseEnd_276334 : Nat := 63063183635389811401853

theorem tailTrace_276334 : CollatzResearch.WordTrace tailWord_276334 prefixEnd_276334 63063183635389811401853 := by
  unfold tailWord_276334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259841122612073366874507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6719152653931057956664037 1259841122612073366874507)
  ·
    refine ⟨1889761683918110050311761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1259841122612073366874507 1889761683918110050311761)
    ·
      refine ⟨1417321262938582537733821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1889761683918110050311761 1417321262938582537733821)
      ·
        refine ⟨531495473601968451650183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1417321262938582537733821 531495473601968451650183)
        ·
          refine ⟨797243210402952677475275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531495473601968451650183 797243210402952677475275)
          ·
            refine ⟨1195864815604429016212913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797243210402952677475275 1195864815604429016212913)
            ·
              refine ⟨896898611703321762159685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1195864815604429016212913 896898611703321762159685)
              ·
                refine ⟨168168489694372830404941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 896898611703321762159685 168168489694372830404941)
                ·
                  refine ⟨63063183635389811401853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168168489694372830404941 63063183635389811401853)
                  ·
                    rfl

theorem cell21_276334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_276334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276334 prefixEnd_276334 := by exact prefixLift 276334
  have htrace : WordTrace (prefixWord ++ tailWord_276334) baseStart_276334 baseEnd_276334 := by
    simpa [prefixWord, tailWord_276334, baseEnd_276334] using wordTrace_append hprefix tailTrace_276334
  have hstable : (prefixWord ++ tailWord_276334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276334).length < 2 ^ (prefixWord ++ tailWord_276334).sum := by decide
  have hdescent : baseEnd_276334 < baseStart_276334 := by decide
  rcases family_descends (prefixWord ++ tailWord_276334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276362 : List Nat := [3, 1, 2, 4, 2, 1, 1, 7]
def baseStart_276362 : Nat := 118140960795 + 276362 * 2 ^ 59
def prefixEnd_276362 : Nat := 4983230072969 + 3 ^ 40 * 276362 * 2
def baseEnd_276362 : Nat := 21023191205622661645043

theorem tailTrace_276362 : CollatzResearch.WordTrace tailWord_276362 prefixEnd_276362 21023191205622661645043 := by
  unfold tailWord_276362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2519937556198786929253835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6719833483196765144676893 2519937556198786929253835)
  ·
    refine ⟨3779906334298180393880753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2519937556198786929253835 3779906334298180393880753)
    ·
      refine ⟨2834929750723635295410565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3779906334298180393880753 2834929750723635295410565)
      ·
        refine ⟨531549328260681617889481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2834929750723635295410565 531549328260681617889481)
        ·
          refine ⟨398661996195511213417111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 531549328260681617889481 398661996195511213417111)
          ·
            refine ⟨597992994293266820125667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398661996195511213417111 597992994293266820125667)
            ·
              refine ⟨896989491439900230188501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 597992994293266820125667 896989491439900230188501)
              ·
                refine ⟨21023191205622661645043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 896989491439900230188501 21023191205622661645043)
                ·
                  rfl

theorem cell21_276362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_276362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276362 prefixEnd_276362 := by exact prefixLift 276362
  have htrace : WordTrace (prefixWord ++ tailWord_276362) baseStart_276362 baseEnd_276362 := by
    simpa [prefixWord, tailWord_276362, baseEnd_276362] using wordTrace_append hprefix tailTrace_276362
  have hstable : (prefixWord ++ tailWord_276362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276362).length < 2 ^ (prefixWord ++ tailWord_276362).sum := by decide
  have hdescent : baseEnd_276362 < baseStart_276362 := by decide
  rcases family_descends (prefixWord ++ tailWord_276362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276438 : List Nat := [5, 2, 1, 1, 3, 9]
def baseStart_276438 : Nat := 118140960795 + 276438 * 2 ^ 59
def prefixEnd_276438 : Nat := 4983230072969 + 3 ^ 40 * 276438 * 2
def baseEnd_276438 : Nat := 2336552513048471913641

theorem tailTrace_276438 : CollatzResearch.WordTrace tailWord_276438 prefixEnd_276438 2336552513048471913641 := by
  unfold tailWord_276438
  simp only [CollatzResearch.WordTrace]
  refine ⟨630157635782488293548873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6721681448346541797854645 630157635782488293548873)
  ·
    refine ⟨472618226836866220161655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 630157635782488293548873 472618226836866220161655)
    ·
      refine ⟨708927340255299330242483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 472618226836866220161655 708927340255299330242483)
      ·
        refine ⟨1063391010382948995363725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708927340255299330242483 1063391010382948995363725)
        ·
          refine ⟨398771628893605873261397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1063391010382948995363725 398771628893605873261397)
          ·
            refine ⟨2336552513048471913641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 398771628893605873261397 2336552513048471913641)
            ·
              rfl

theorem cell21_276438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 9].length) (baseStart_276438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276438 prefixEnd_276438 := by exact prefixLift 276438
  have htrace : WordTrace (prefixWord ++ tailWord_276438) baseStart_276438 baseEnd_276438 := by
    simpa [prefixWord, tailWord_276438, baseEnd_276438] using wordTrace_append hprefix tailTrace_276438
  have hstable : (prefixWord ++ tailWord_276438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276438).length < 2 ^ (prefixWord ++ tailWord_276438).sum := by decide
  have hdescent : baseEnd_276438 < baseStart_276438 := by decide
  rcases family_descends (prefixWord ++ tailWord_276438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276444 : List Nat := [2, 2, 6, 1, 1, 1, 1, 4, 3]
def baseStart_276444 : Nat := 118140960795 + 276444 * 2 ^ 59
def prefixEnd_276444 : Nat := 4983230072969 + 3 ^ 40 * 276444 * 2
def baseEnd_276444 : Nat := 63088287134054064568295

theorem tailTrace_276444 : CollatzResearch.WordTrace tailWord_276444 prefixEnd_276444 63088287134054064568295 := by
  unfold tailWord_276444
  simp only [CollatzResearch.WordTrace]
  refine ⟨5041370505249037860750193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6721827340332050481000257 5041370505249037860750193)
  ·
    refine ⟨3781027878936778395562645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5041370505249037860750193 3781027878936778395562645)
    ·
      refine ⟨177235681825161487291999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3781027878936778395562645 177235681825161487291999)
      ·
        refine ⟨265853522737742230937999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177235681825161487291999 265853522737742230937999)
        ·
          refine ⟨398780284106613346406999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265853522737742230937999 398780284106613346406999)
          ·
            refine ⟨598170426159920019610499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398780284106613346406999 598170426159920019610499)
            ·
              refine ⟨897255639239880029415749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598170426159920019610499 897255639239880029415749)
              ·
                refine ⟨168235432357477505515453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 897255639239880029415749 168235432357477505515453)
                ·
                  refine ⟨63088287134054064568295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168235432357477505515453 63088287134054064568295)
                  ·
                    rfl

theorem cell21_276444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_276444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276444 prefixEnd_276444 := by exact prefixLift 276444
  have htrace : WordTrace (prefixWord ++ tailWord_276444) baseStart_276444 baseEnd_276444 := by
    simpa [prefixWord, tailWord_276444, baseEnd_276444] using wordTrace_append hprefix tailTrace_276444
  have hstable : (prefixWord ++ tailWord_276444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276444).length < 2 ^ (prefixWord ++ tailWord_276444).sum := by decide
  have hdescent : baseEnd_276444 < baseStart_276444 := by decide
  rcases family_descends (prefixWord ++ tailWord_276444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276455 : List Nat := [1, 1, 5, 2, 4, 1, 1, 6]
def baseStart_276455 : Nat := 118140960795 + 276455 * 2 ^ 59
def prefixEnd_276455 : Nat := 4983230072969 + 3 ^ 40 * 276455 * 2
def baseEnd_276455 : Nat := 21030265827973496628313

theorem tailTrace_276455 : CollatzResearch.WordTrace tailWord_276455 prefixEnd_276455 21030265827973496628313 := by
  unfold tailWord_276455
  simp only [CollatzResearch.WordTrace]
  refine ⟨10083142213458224600150819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6722094808972149733433879 10083142213458224600150819)
  ·
    refine ⟨15124713320187336900226229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10083142213458224600150819 15124713320187336900226229)
    ·
      refine ⟨1417941873767562834396209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15124713320187336900226229 1417941873767562834396209)
      ·
        refine ⟨1063456405325672125797157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1417941873767562834396209 1063456405325672125797157)
        ·
          refine ⟨199398075998563523586967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1063456405325672125797157 199398075998563523586967)
          ·
            refine ⟨299097113997845285380451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199398075998563523586967 299097113997845285380451)
            ·
              refine ⟨448645670996767928070677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299097113997845285380451 448645670996767928070677)
              ·
                refine ⟨21030265827973496628313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 448645670996767928070677 21030265827973496628313)
                ·
                  rfl

theorem cell21_276455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 6].length) (baseStart_276455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276455 prefixEnd_276455 := by exact prefixLift 276455
  have htrace : WordTrace (prefixWord ++ tailWord_276455) baseStart_276455 baseEnd_276455 := by
    simpa [prefixWord, tailWord_276455, baseEnd_276455] using wordTrace_append hprefix tailTrace_276455
  have hstable : (prefixWord ++ tailWord_276455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276455).length < 2 ^ (prefixWord ++ tailWord_276455).sum := by decide
  have hdescent : baseEnd_276455 < baseStart_276455 := by decide
  rcases family_descends (prefixWord ++ tailWord_276455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276556 : List Nat := [2, 2, 1, 3, 1, 1, 11]
def baseStart_276556 : Nat := 118140960795 + 276556 * 2 ^ 59
def prefixEnd_276556 : Nat := 4983230072969 + 3 ^ 40 * 276556 * 2
def baseEnd_276556 : Nat := 7012649673329639855711

theorem tailTrace_276556 : CollatzResearch.WordTrace tailWord_276556 prefixEnd_276556 7012649673329639855711 := by
  unfold tailWord_276556
  simp only [CollatzResearch.WordTrace]
  refine ⟨5043412993046159424788761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6724550657394879233051681 5043412993046159424788761)
  ·
    refine ⟨3782559744784619568591571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5043412993046159424788761 3782559744784619568591571)
    ·
      refine ⟨5673839617176929352887357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3782559744784619568591571 5673839617176929352887357)
      ·
        refine ⟨2127689856441348507332759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5673839617176929352887357 2127689856441348507332759)
        ·
          refine ⟨3191534784662022760999139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2127689856441348507332759 3191534784662022760999139)
          ·
            refine ⟨4787302176993034141498709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191534784662022760999139 4787302176993034141498709)
            ·
              refine ⟨7012649673329639855711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4787302176993034141498709 7012649673329639855711)
              ·
                rfl

theorem cell21_276556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 11].length) (baseStart_276556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276556 prefixEnd_276556 := by exact prefixLift 276556
  have htrace : WordTrace (prefixWord ++ tailWord_276556) baseStart_276556 baseEnd_276556 := by
    simpa [prefixWord, tailWord_276556, baseEnd_276556] using wordTrace_append hprefix tailTrace_276556
  have hstable : (prefixWord ++ tailWord_276556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276556).length < 2 ^ (prefixWord ++ tailWord_276556).sum := by decide
  have hdescent : baseEnd_276556 < baseStart_276556 := by decide
  rcases family_descends (prefixWord ++ tailWord_276556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276562 : List Nat := [3, 2, 2, 1, 5, 1, 1, 1, 5]
def baseStart_276562 : Nat := 118140960795 + 276562 * 2 ^ 59
def prefixEnd_276562 : Nat := 4983230072969 + 3 ^ 40 * 276562 * 2
def baseEnd_276562 : Nat := 63115216341712081601387

theorem tailTrace_276562 : CollatzResearch.WordTrace tailWord_276562 prefixEnd_276562 63115216341712081601387 := by
  unfold tailWord_276562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2521761206017645468573985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6724696549380387916197293 2521761206017645468573985)
  ·
    refine ⟨1891320904513234101430489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2521761206017645468573985 1891320904513234101430489)
    ·
      refine ⟨1418490678384925576072867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1891320904513234101430489 1418490678384925576072867)
      ·
        refine ⟨2127736017577388364109301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418490678384925576072867 2127736017577388364109301)
        ·
          refine ⟨199475251647880159135247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2127736017577388364109301 199475251647880159135247)
          ·
            refine ⟨299212877471820238702871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199475251647880159135247 299212877471820238702871)
            ·
              refine ⟨448819316207730358054307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299212877471820238702871 448819316207730358054307)
              ·
                refine ⟨673228974311595537081461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448819316207730358054307 673228974311595537081461)
                ·
                  refine ⟨63115216341712081601387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 673228974311595537081461 63115216341712081601387)
                  ·
                    rfl

theorem cell21_276562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_276562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276562 prefixEnd_276562 := by exact prefixLift 276562
  have htrace : WordTrace (prefixWord ++ tailWord_276562) baseStart_276562 baseEnd_276562 := by
    simpa [prefixWord, tailWord_276562, baseEnd_276562] using wordTrace_append hprefix tailTrace_276562
  have hstable : (prefixWord ++ tailWord_276562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276562).length < 2 ^ (prefixWord ++ tailWord_276562).sum := by decide
  have hdescent : baseEnd_276562 < baseStart_276562 := by decide
  rcases family_descends (prefixWord ++ tailWord_276562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276576 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 4]
def baseStart_276576 : Nat := 118140960795 + 276576 * 2 ^ 59
def prefixEnd_276576 : Nat := 4983230072969 + 3 ^ 40 * 276576 * 2
def baseEnd_276576 : Nat := 63118411332451168368025

theorem tailTrace_276576 : CollatzResearch.WordTrace tailWord_276576 prefixEnd_276576 63118411332451168368025 := by
  unfold tailWord_276576
  simp only [CollatzResearch.WordTrace]
  refine ⟨5043777723009931132652791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6725036964013241510203721 5043777723009931132652791)
  ·
    refine ⟨7565666584514896698979187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5043777723009931132652791 7565666584514896698979187)
    ·
      refine ⟨11348499876772345048468781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7565666584514896698979187 11348499876772345048468781)
      ·
        refine ⟨4255687453789629393175793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11348499876772345048468781 4255687453789629393175793)
        ·
          refine ⟨3191765590342222044881845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4255687453789629393175793 3191765590342222044881845)
          ·
            refine ⟨299228024094583316707673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3191765590342222044881845 299228024094583316707673)
            ·
              refine ⟨224421018070937487530755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299228024094583316707673 224421018070937487530755)
              ·
                refine ⟨336631527106406231296133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224421018070937487530755 336631527106406231296133)
                ·
                  refine ⟨63118411332451168368025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 336631527106406231296133 63118411332451168368025)
                  ·
                    rfl

theorem cell21_276576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_276576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276576 prefixEnd_276576 := by exact prefixLift 276576
  have htrace : WordTrace (prefixWord ++ tailWord_276576) baseStart_276576 baseEnd_276576 := by
    simpa [prefixWord, tailWord_276576, baseEnd_276576] using wordTrace_append hprefix tailTrace_276576
  have hstable : (prefixWord ++ tailWord_276576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276576).length < 2 ^ (prefixWord ++ tailWord_276576).sum := by decide
  have hdescent : baseEnd_276576 < baseStart_276576 := by decide
  rcases family_descends (prefixWord ++ tailWord_276576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276700 : List Nat := [2, 2, 5, 2, 1, 2, 2, 5]
def baseStart_276700 : Nat := 118140960795 + 276700 * 2 ^ 59
def prefixEnd_276700 : Nat := 4983230072969 + 3 ^ 40 * 276700 * 2
def baseEnd_276700 : Nat := 21048903273951502767035

theorem tailTrace_276700 : CollatzResearch.WordTrace tailWord_276700 prefixEnd_276700 21048903273951502767035 := by
  unfold tailWord_276700
  simp only [CollatzResearch.WordTrace]
  refine ⟨5046039048785315721409777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6728052065047087628546369 5046039048785315721409777)
  ·
    refine ⟨3784529286588986791057333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5046039048785315721409777 3784529286588986791057333)
    ·
      refine ⟨354799620617717511661625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3784529286588986791057333 354799620617717511661625)
      ·
        refine ⟨266099715463288133746219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354799620617717511661625 266099715463288133746219)
        ·
          refine ⟨399149573194932200619329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266099715463288133746219 399149573194932200619329)
          ·
            refine ⟨299362179896199150464497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399149573194932200619329 299362179896199150464497)
            ·
              refine ⟨224521634922149362848373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299362179896199150464497 224521634922149362848373)
              ·
                refine ⟨21048903273951502767035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 224521634922149362848373 21048903273951502767035)
                ·
                  rfl

theorem cell21_276700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 5].length) (baseStart_276700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276700 prefixEnd_276700 := by exact prefixLift 276700
  have htrace : WordTrace (prefixWord ++ tailWord_276700) baseStart_276700 baseEnd_276700 := by
    simpa [prefixWord, tailWord_276700, baseEnd_276700] using wordTrace_append hprefix tailTrace_276700
  have hstable : (prefixWord ++ tailWord_276700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276700).length < 2 ^ (prefixWord ++ tailWord_276700).sum := by decide
  have hdescent : baseEnd_276700 < baseStart_276700 := by decide
  rcases family_descends (prefixWord ++ tailWord_276700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276894 : List Nat := [4, 3, 1, 2, 1, 3, 7]
def baseStart_276894 : Nat := 118140960795 + 276894 * 2 ^ 59
def prefixEnd_276894 : Nat := 4983230072969 + 3 ^ 40 * 276894 * 2
def baseEnd_276894 : Nat := 7021220362772586896375

theorem tailTrace_276894 : CollatzResearch.WordTrace tailWord_276894 prefixEnd_276894 7021220362772586896375 := by
  unfold tailWord_276894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1262394232358475321922717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6732769239245201716921157 1262394232358475321922717)
  ·
    refine ⟨473397837134428245721019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1262394232358475321922717 473397837134428245721019)
    ·
      refine ⟨710096755701642368581529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 473397837134428245721019 710096755701642368581529)
      ·
        refine ⟨532572566776231776436147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 710096755701642368581529 532572566776231776436147)
        ·
          refine ⟨798858850164347664654221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532572566776231776436147 798858850164347664654221)
          ·
            refine ⟨299572068811630374245333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 798858850164347664654221 299572068811630374245333)
            ·
              refine ⟨7021220362772586896375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 299572068811630374245333 7021220362772586896375)
              ·
                rfl

theorem cell21_276894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 7].length) (baseStart_276894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276894 prefixEnd_276894 := by exact prefixLift 276894
  have htrace : WordTrace (prefixWord ++ tailWord_276894) baseStart_276894 baseEnd_276894 := by
    simpa [prefixWord, tailWord_276894, baseEnd_276894] using wordTrace_append hprefix tailTrace_276894
  have hstable : (prefixWord ++ tailWord_276894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276894).length < 2 ^ (prefixWord ++ tailWord_276894).sum := by decide
  have hdescent : baseEnd_276894 < baseStart_276894 := by decide
  rcases family_descends (prefixWord ++ tailWord_276894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276936 : List Nat := [2, 1, 3, 1, 3, 2, 2, 7]
def baseStart_276936 : Nat := 118140960795 + 276936 * 2 ^ 59
def prefixEnd_276936 : Nat := 4983230072969 + 3 ^ 40 * 276936 * 2
def baseEnd_276936 : Nat := 21066856079056847455763

theorem tailTrace_276936 : CollatzResearch.WordTrace tailWord_276936 prefixEnd_276936 21066856079056847455763 := by
  unfold tailWord_276936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5050342862357821874205331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6733790483143762498940441 5050342862357821874205331)
  ·
    refine ⟨7575514293536732811307997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5050342862357821874205331 7575514293536732811307997)
    ·
      refine ⟨2840817860076274804240499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7575514293536732811307997 2840817860076274804240499)
      ·
        refine ⟨4261226790114412206360749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2840817860076274804240499 4261226790114412206360749)
        ·
          refine ⟨1597960046292904577385281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4261226790114412206360749 1597960046292904577385281)
          ·
            refine ⟨1198470034719678433038961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1597960046292904577385281 1198470034719678433038961)
            ·
              refine ⟨898852526039758824779221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1198470034719678433038961 898852526039758824779221)
              ·
                refine ⟨21066856079056847455763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 898852526039758824779221 21066856079056847455763)
                ·
                  rfl

theorem cell21_276936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 7].length) (baseStart_276936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276936 prefixEnd_276936 := by exact prefixLift 276936
  have htrace : WordTrace (prefixWord ++ tailWord_276936) baseStart_276936 baseEnd_276936 := by
    simpa [prefixWord, tailWord_276936, baseEnd_276936] using wordTrace_append hprefix tailTrace_276936
  have hstable : (prefixWord ++ tailWord_276936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276936).length < 2 ^ (prefixWord ++ tailWord_276936).sum := by decide
  have hdescent : baseEnd_276936 < baseStart_276936 := by decide
  rcases family_descends (prefixWord ++ tailWord_276936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_276967 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 5]
def baseStart_276967 : Nat := 118140960795 + 276967 * 2 ^ 59
def prefixEnd_276967 : Nat := 4983230072969 + 3 ^ 40 * 276967 * 2
def baseEnd_276967 : Nat := 63207642859521377350559

theorem tailTrace_276967 : CollatzResearch.WordTrace tailWord_276967 prefixEnd_276967 63207642859521377350559 := by
  unfold tailWord_276967
  simp only [CollatzResearch.WordTrace]
  refine ⟨10101816387603336042789155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6734544258402224028526103 10101816387603336042789155)
  ·
    refine ⟨15152724581405004064183733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10101816387603336042789155 15152724581405004064183733)
    ·
      refine ⟨1420567929506719131017225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15152724581405004064183733 1420567929506719131017225)
      ·
        refine ⟨1065425947130039348262919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1420567929506719131017225 1065425947130039348262919)
        ·
          refine ⟨1598138920695059022394379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1065425947130039348262919 1598138920695059022394379)
          ·
            refine ⟨2397208381042588533591569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598138920695059022394379 2397208381042588533591569)
            ·
              refine ⟨1797906285781941400193677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2397208381042588533591569 1797906285781941400193677)
              ·
                refine ⟨674214857168228025072629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1797906285781941400193677 674214857168228025072629)
                ·
                  refine ⟨63207642859521377350559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 674214857168228025072629 63207642859521377350559)
                  ·
                    rfl

theorem cell21_276967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_276967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_276967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_276967 prefixEnd_276967 := by exact prefixLift 276967
  have htrace : WordTrace (prefixWord ++ tailWord_276967) baseStart_276967 baseEnd_276967 := by
    simpa [prefixWord, tailWord_276967, baseEnd_276967] using wordTrace_append hprefix tailTrace_276967
  have hstable : (prefixWord ++ tailWord_276967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_276967).length < 2 ^ (prefixWord ++ tailWord_276967).sum := by decide
  have hdescent : baseEnd_276967 < baseStart_276967 := by decide
  rcases family_descends (prefixWord ++ tailWord_276967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277015 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 6]
def baseStart_277015 : Nat := 118140960795 + 277015 * 2 ^ 59
def prefixEnd_277015 : Nat := 4983230072969 + 3 ^ 40 * 277015 * 2
def baseEnd_277015 : Nat := 63218597113483960550461

theorem tailTrace_277015 : CollatzResearch.WordTrace tailWord_277015 prefixEnd_277015 63218597113483960550461 := by
  unfold tailWord_277015
  simp only [CollatzResearch.WordTrace]
  refine ⟨10103567091429440240536499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6735711394286293493690999 10103567091429440240536499)
  ·
    refine ⟨15155350637144160360804749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10103567091429440240536499 15155350637144160360804749)
    ·
      refine ⟨5683256488929060135301781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15155350637144160360804749 5683256488929060135301781)
      ·
        refine ⟨266402647918549693842271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5683256488929060135301781 266402647918549693842271)
        ·
          refine ⟨399603971877824540763407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266402647918549693842271 399603971877824540763407)
          ·
            refine ⟨599405957816736811145111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399603971877824540763407 599405957816736811145111)
            ·
              refine ⟨899108936725105216717667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599405957816736811145111 899108936725105216717667)
              ·
                refine ⟨1348663405087657825076501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 899108936725105216717667 1348663405087657825076501)
                ·
                  refine ⟨63218597113483960550461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1348663405087657825076501 63218597113483960550461)
                  ·
                    rfl

theorem cell21_277015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 6].length) (baseStart_277015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277015 prefixEnd_277015 := by exact prefixLift 277015
  have htrace : WordTrace (prefixWord ++ tailWord_277015) baseStart_277015 baseEnd_277015 := by
    simpa [prefixWord, tailWord_277015, baseEnd_277015] using wordTrace_append hprefix tailTrace_277015
  have hstable : (prefixWord ++ tailWord_277015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277015).length < 2 ^ (prefixWord ++ tailWord_277015).sum := by decide
  have hdescent : baseEnd_277015 < baseStart_277015 := by decide
  rcases family_descends (prefixWord ++ tailWord_277015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277032 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 4]
def baseStart_277032 : Nat := 118140960795 + 277032 * 2 ^ 59
def prefixEnd_277032 : Nat := 4983230072969 + 3 ^ 40 * 277032 * 2
def baseEnd_277032 : Nat := 63222476745095708767093

theorem tailTrace_277032 : CollatzResearch.WordTrace tailWord_277032 prefixEnd_277032 63222476745095708767093 := by
  unfold tailWord_277032
  simp only [CollatzResearch.WordTrace]
  refine ⟨5052093566183926071952675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6736124754911901429270233 5052093566183926071952675)
  ·
    refine ⟨7578140349275889107929013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5052093566183926071952675 7578140349275889107929013)
    ·
      refine ⟨710450657744614603868345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7578140349275889107929013 710450657744614603868345)
      ·
        refine ⟨532837993308460952901259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 710450657744614603868345 532837993308460952901259)
        ·
          refine ⟨799256989962691429351889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532837993308460952901259 799256989962691429351889)
          ·
            refine ⟨599442742472018572013917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799256989962691429351889 599442742472018572013917)
            ·
              refine ⟨224791028427006964505219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 599442742472018572013917 224791028427006964505219)
              ·
                refine ⟨337186542640510446757829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224791028427006964505219 337186542640510446757829)
                ·
                  refine ⟨63222476745095708767093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337186542640510446757829 63222476745095708767093)
                  ·
                    rfl

theorem cell21_277032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_277032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277032 prefixEnd_277032 := by exact prefixLift 277032
  have htrace : WordTrace (prefixWord ++ tailWord_277032) baseStart_277032 baseEnd_277032 := by
    simpa [prefixWord, tailWord_277032, baseEnd_277032] using wordTrace_append hprefix tailTrace_277032
  have hstable : (prefixWord ++ tailWord_277032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277032).length < 2 ^ (prefixWord ++ tailWord_277032).sum := by decide
  have hdescent : baseEnd_277032 < baseStart_277032 := by decide
  rcases family_descends (prefixWord ++ tailWord_277032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277046 : List Nat := [5, 1, 2, 1, 2, 1, 4, 5]
def baseStart_277046 : Nat := 118140960795 + 277046 * 2 ^ 59
def prefixEnd_277046 : Nat := 4983230072969 + 3 ^ 40 * 277046 * 2
def baseEnd_277046 : Nat := 21075223911944931844577

theorem tailTrace_277046 : CollatzResearch.WordTrace tailWord_277046 prefixEnd_277046 21075223911944931844577 := by
  unfold tailWord_277046
  simp only [CollatzResearch.WordTrace]
  refine ⟨631543609644820783432187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6736465169544755023276661 631543609644820783432187)
  ·
    refine ⟨947315414467231175148281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 631543609644820783432187 947315414467231175148281)
    ·
      refine ⟨710486560850423381361211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 947315414467231175148281 710486560850423381361211)
      ·
        refine ⟨1065729841275635072041817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710486560850423381361211 1065729841275635072041817)
        ·
          refine ⟨799297380956726304031363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1065729841275635072041817 799297380956726304031363)
          ·
            refine ⟨1198946071435089456047045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799297380956726304031363 1198946071435089456047045)
            ·
              refine ⟨224802388394079273008821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1198946071435089456047045 224802388394079273008821)
              ·
                refine ⟨21075223911944931844577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 224802388394079273008821 21075223911944931844577)
                ·
                  rfl

theorem cell21_277046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_277046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277046 prefixEnd_277046 := by exact prefixLift 277046
  have htrace : WordTrace (prefixWord ++ tailWord_277046) baseStart_277046 baseEnd_277046 := by
    simpa [prefixWord, tailWord_277046, baseEnd_277046] using wordTrace_append hprefix tailTrace_277046
  have hstable : (prefixWord ++ tailWord_277046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277046).length < 2 ^ (prefixWord ++ tailWord_277046).sum := by decide
  have hdescent : baseEnd_277046 < baseStart_277046 := by decide
  rcases family_descends (prefixWord ++ tailWord_277046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277071 : List Nat := [1, 1, 2, 1, 1, 2, 13]
def baseStart_277071 : Nat := 118140960795 + 277071 * 2 ^ 59
def prefixEnd_277071 : Nat := 4983230072969 + 3 ^ 40 * 277071 * 2
def baseEnd_277071 : Nat := 7025708564048923068557

theorem tailTrace_277071 : CollatzResearch.WordTrace tailWord_277071 prefixEnd_277071 7025708564048923068557 := by
  unfold tailWord_277071
  simp only [CollatzResearch.WordTrace]
  refine ⟨10105609579226561804575067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6737073052817707869716711 10105609579226561804575067)
  ·
    refine ⟨15158414368839842706862601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10105609579226561804575067 15158414368839842706862601)
    ·
      refine ⟨11368810776629882030146951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15158414368839842706862601 11368810776629882030146951)
      ·
        refine ⟨17053216164944823045220427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11368810776629882030146951 17053216164944823045220427)
        ·
          refine ⟨25579824247417234567830641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17053216164944823045220427 25579824247417234567830641)
          ·
            refine ⟨19184868185562925925872981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25579824247417234567830641 19184868185562925925872981)
            ·
              refine ⟨7025708564048923068557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 19184868185562925925872981 7025708564048923068557)
              ·
                rfl

theorem cell21_277071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 13].length) (baseStart_277071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277071 prefixEnd_277071 := by exact prefixLift 277071
  have htrace : WordTrace (prefixWord ++ tailWord_277071) baseStart_277071 baseEnd_277071 := by
    simpa [prefixWord, tailWord_277071, baseEnd_277071] using wordTrace_append hprefix tailTrace_277071
  have hstable : (prefixWord ++ tailWord_277071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277071).length < 2 ^ (prefixWord ++ tailWord_277071).sum := by decide
  have hdescent : baseEnd_277071 < baseStart_277071 := by decide
  rcases family_descends (prefixWord ++ tailWord_277071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277074 : List Nat := [3, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_277074 : Nat := 118140960795 + 277074 * 2 ^ 59
def prefixEnd_277074 : Nat := 4983230072969 + 3 ^ 40 * 277074 * 2
def baseEnd_277074 : Nat := 63232061717312969067007

theorem tailTrace_277074 : CollatzResearch.WordTrace tailWord_277074 prefixEnd_277074 63232061717312969067007 := by
  unfold tailWord_277074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526429749553923329233569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6737145998810462211289517 2526429749553923329233569)
  ·
    refine ⟨1894822312165442496925177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2526429749553923329233569 1894822312165442496925177)
    ·
      refine ⟨1421116734124081872693883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1894822312165442496925177 1421116734124081872693883)
      ·
        refine ⟨2131675101186122809040825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1421116734124081872693883 2131675101186122809040825)
        ·
          refine ⟨1598756325889592106780619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2131675101186122809040825 1598756325889592106780619)
          ·
            refine ⟨2398134488834388160170929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1598756325889592106780619 2398134488834388160170929)
            ·
              refine ⟨1798600866625791120128197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2398134488834388160170929 1798600866625791120128197)
              ·
                refine ⟨337237662492335835024037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1798600866625791120128197 337237662492335835024037)
                ·
                  refine ⟨63232061717312969067007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 337237662492335835024037 63232061717312969067007)
                  ·
                    rfl

theorem cell21_277074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_277074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277074 prefixEnd_277074 := by exact prefixLift 277074
  have htrace : WordTrace (prefixWord ++ tailWord_277074) baseStart_277074 baseEnd_277074 := by
    simpa [prefixWord, tailWord_277074, baseEnd_277074] using wordTrace_append hprefix tailTrace_277074
  have hstable : (prefixWord ++ tailWord_277074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277074).length < 2 ^ (prefixWord ++ tailWord_277074).sum := by decide
  have hdescent : baseEnd_277074 < baseStart_277074 := by decide
  rcases family_descends (prefixWord ++ tailWord_277074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277122 : List Nat := [3, 4, 3, 1, 10]
def baseStart_277122 : Nat := 118140960795 + 277122 * 2 ^ 59
def prefixEnd_277122 : Nat := 4983230072969 + 3 ^ 40 * 277122 * 2
def baseEnd_277122 : Nat := 780777974954019163789

theorem tailTrace_277122 : CollatzResearch.WordTrace tailWord_277122 prefixEnd_277122 780777974954019163789 := by
  unfold tailWord_277122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2526867425510449378670405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6738313134694531676454413 2526867425510449378670405)
  ·
    refine ⟨473787642283209258500701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2526867425510449378670405 473787642283209258500701)
    ·
      refine ⟨177670365856203471937763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 473787642283209258500701 177670365856203471937763)
      ·
        refine ⟨266505548784305207906645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177670365856203471937763 266505548784305207906645)
        ·
          refine ⟨780777974954019163789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 266505548784305207906645 780777974954019163789)
          ·
            rfl

theorem cell21_277122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 10].length) (baseStart_277122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277122 prefixEnd_277122 := by exact prefixLift 277122
  have htrace : WordTrace (prefixWord ++ tailWord_277122) baseStart_277122 baseEnd_277122 := by
    simpa [prefixWord, tailWord_277122, baseEnd_277122] using wordTrace_append hprefix tailTrace_277122
  have hstable : (prefixWord ++ tailWord_277122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277122).length < 2 ^ (prefixWord ++ tailWord_277122).sum := by decide
  have hdescent : baseEnd_277122 < baseStart_277122 := by decide
  rcases family_descends (prefixWord ++ tailWord_277122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277178 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 7]
def baseStart_277178 : Nat := 118140960795 + 277178 * 2 ^ 59
def prefixEnd_277178 : Nat := 4983230072969 + 3 ^ 40 * 277178 * 2
def baseEnd_277178 : Nat := 63255795934231899333461

theorem tailTrace_277178 : CollatzResearch.WordTrace tailWord_277178 prefixEnd_277178 63255795934231899333461 := by
  unfold tailWord_277178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2527378047459729769680047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6739674793225946052480125 2527378047459729769680047)
  ·
    refine ⟨3791067071189594654520071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2527378047459729769680047 3791067071189594654520071)
    ·
      refine ⟨5686600606784391981780107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3791067071189594654520071 5686600606784391981780107)
      ·
        refine ⟨8529900910176587972670161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5686600606784391981780107 8529900910176587972670161)
        ·
          refine ⟨6397425682632440979502621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8529900910176587972670161 6397425682632440979502621)
          ·
            refine ⟨2399034630987165367313483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6397425682632440979502621 2399034630987165367313483)
            ·
              refine ⟨3598551946480748050970225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2399034630987165367313483 3598551946480748050970225)
              ·
                refine ⟨2698913959860561038227669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3598551946480748050970225 2698913959860561038227669)
                ·
                  refine ⟨63255795934231899333461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2698913959860561038227669 63255795934231899333461)
                  ·
                    rfl

theorem cell21_277178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_277178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277178 prefixEnd_277178 := by exact prefixLift 277178
  have htrace : WordTrace (prefixWord ++ tailWord_277178) baseStart_277178 baseEnd_277178 := by
    simpa [prefixWord, tailWord_277178, baseEnd_277178] using wordTrace_append hprefix tailTrace_277178
  have hstable : (prefixWord ++ tailWord_277178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277178).length < 2 ^ (prefixWord ++ tailWord_277178).sum := by decide
  have hdescent : baseEnd_277178 < baseStart_277178 := by decide
  rcases family_descends (prefixWord ++ tailWord_277178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277212 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 5]
def baseStart_277212 : Nat := 118140960795 + 277212 * 2 ^ 59
def prefixEnd_277212 : Nat := 4983230072969 + 3 ^ 40 * 277212 * 2
def baseEnd_277212 : Nat := 63263555197455395766725

theorem tailTrace_277212 : CollatzResearch.WordTrace tailWord_277212 prefixEnd_277212 63263555197455395766725 := by
  unfold tailWord_277212
  simp only [CollatzResearch.WordTrace]
  refine ⟨5055376135857871442728945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6740501514477161923638593 5055376135857871442728945)
  ·
    refine ⟨3791532101893403582046709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5055376135857871442728945 3791532101893403582046709)
    ·
      refine ⟨355456134552506585816879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3791532101893403582046709 355456134552506585816879)
      ·
        refine ⟨533184201828759878725319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355456134552506585816879 533184201828759878725319)
        ·
          refine ⟨799776302743139818087979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533184201828759878725319 799776302743139818087979)
          ·
            refine ⟨1199664454114709727131969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 799776302743139818087979 1199664454114709727131969)
            ·
              refine ⟨899748340586032295348977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1199664454114709727131969 899748340586032295348977)
              ·
                refine ⟨674811255439524221511733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899748340586032295348977 674811255439524221511733)
                ·
                  refine ⟨63263555197455395766725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 674811255439524221511733 63263555197455395766725)
                  ·
                    rfl

theorem cell21_277212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_277212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277212 prefixEnd_277212 := by exact prefixLift 277212
  have htrace : WordTrace (prefixWord ++ tailWord_277212) baseStart_277212 baseEnd_277212 := by
    simpa [prefixWord, tailWord_277212, baseEnd_277212] using wordTrace_append hprefix tailTrace_277212
  have hstable : (prefixWord ++ tailWord_277212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277212).length < 2 ^ (prefixWord ++ tailWord_277212).sum := by decide
  have hdescent : baseEnd_277212 < baseStart_277212 := by decide
  rcases family_descends (prefixWord ++ tailWord_277212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277246 : List Nat := [4, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_277246 : Nat := 118140960795 + 277246 * 2 ^ 59
def prefixEnd_277246 : Nat := 4983230072969 + 3 ^ 40 * 277246 * 2
def baseEnd_277246 : Nat := 63271314460678892199989

theorem tailTrace_277246 : CollatzResearch.WordTrace tailWord_277246 prefixEnd_277246 63271314460678892199989 := by
  unfold tailWord_277246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263999044199070836524449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6741328235728377794797061 1263999044199070836524449)
  ·
    refine ⟨947999283149303127393337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1263999044199070836524449 947999283149303127393337)
    ·
      refine ⟨710999462361977345545003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 947999283149303127393337 710999462361977345545003)
      ·
        refine ⟨1066499193542966018317505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710999462361977345545003 1066499193542966018317505)
        ·
          refine ⟨799874395157224513738129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1066499193542966018317505 799874395157224513738129)
          ·
            refine ⟨599905796367918385303597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799874395157224513738129 599905796367918385303597)
            ·
              refine ⟨224964673637969394488849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 599905796367918385303597 224964673637969394488849)
              ·
                refine ⟨168723505228477045866637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224964673637969394488849 168723505228477045866637)
                ·
                  refine ⟨63271314460678892199989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168723505228477045866637 63271314460678892199989)
                  ·
                    rfl

theorem cell21_277246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_277246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277246 prefixEnd_277246 := by exact prefixLift 277246
  have htrace : WordTrace (prefixWord ++ tailWord_277246) baseStart_277246 baseEnd_277246 := by
    simpa [prefixWord, tailWord_277246, baseEnd_277246] using wordTrace_append hprefix tailTrace_277246
  have hstable : (prefixWord ++ tailWord_277246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277246).length < 2 ^ (prefixWord ++ tailWord_277246).sum := by decide
  have hdescent : baseEnd_277246 < baseStart_277246 := by decide
  rcases family_descends (prefixWord ++ tailWord_277246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277288 : List Nat := [2, 1, 5, 1, 1, 1, 2, 5, 3]
def baseStart_277288 : Nat := 118140960795 + 277288 * 2 ^ 59
def prefixEnd_277288 : Nat := 4983230072969 + 3 ^ 40 * 277288 * 2
def baseEnd_277288 : Nat := 63280899432896152499903

theorem tailTrace_277288 : CollatzResearch.WordTrace tailWord_277288 prefixEnd_277288 63280899432896152499903 := by
  unfold tailWord_277288
  simp only [CollatzResearch.WordTrace]
  refine ⟨5056762109720203932612259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6742349479626938576816345 5056762109720203932612259)
  ·
    refine ⟨7585143164580305898918389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5056762109720203932612259 7585143164580305898918389)
    ·
      refine ⟨711107171679403678023599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7585143164580305898918389 711107171679403678023599)
      ·
        refine ⟨1066660757519105517035399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711107171679403678023599 1066660757519105517035399)
        ·
          refine ⟨1599991136278658275553099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1066660757519105517035399 1599991136278658275553099)
          ·
            refine ⟨2399986704417987413329649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1599991136278658275553099 2399986704417987413329649)
            ·
              refine ⟨1799990028313490559997237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2399986704417987413329649 1799990028313490559997237)
              ·
                refine ⟨168749065154389739999741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1799990028313490559997237 168749065154389739999741)
                ·
                  refine ⟨63280899432896152499903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168749065154389739999741 63280899432896152499903)
                  ·
                    rfl

theorem cell21_277288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 5, 3].length) (baseStart_277288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277288 prefixEnd_277288 := by exact prefixLift 277288
  have htrace : WordTrace (prefixWord ++ tailWord_277288) baseStart_277288 baseEnd_277288 := by
    simpa [prefixWord, tailWord_277288, baseEnd_277288] using wordTrace_append hprefix tailTrace_277288
  have hstable : (prefixWord ++ tailWord_277288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277288).length < 2 ^ (prefixWord ++ tailWord_277288).sum := by decide
  have hdescent : baseEnd_277288 < baseStart_277288 := by decide
  rcases family_descends (prefixWord ++ tailWord_277288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277299 : List Nat := [1, 1, 1, 2, 6, 10]
def baseStart_277299 : Nat := 118140960795 + 277299 * 2 ^ 59
def prefixEnd_277299 : Nat := 4983230072969 + 3 ^ 40 * 277299 * 2
def baseEnd_277299 : Nat := 2343829991954169548761

theorem tailTrace_277299 : CollatzResearch.WordTrace tailWord_277299 prefixEnd_277299 2343829991954169548761 := by
  unfold tailWord_277299
  simp only [CollatzResearch.WordTrace]
  refine ⟨10113925422400556743874951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6742616948267037829249967 10113925422400556743874951)
  ·
    refine ⟨15170888133600835115812427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10113925422400556743874951 15170888133600835115812427)
    ·
      refine ⟨22756332200401252673718641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15170888133600835115812427 22756332200401252673718641)
      ·
        refine ⟨17067249150300939505288981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22756332200401252673718641 17067249150300939505288981)
        ·
          refine ⟨800027303920356539310421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17067249150300939505288981 800027303920356539310421)
          ·
            refine ⟨2343829991954169548761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 800027303920356539310421 2343829991954169548761)
            ·
              rfl

theorem cell21_277299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 10].length) (baseStart_277299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277299 prefixEnd_277299 := by exact prefixLift 277299
  have htrace : WordTrace (prefixWord ++ tailWord_277299) baseStart_277299 baseEnd_277299 := by
    simpa [prefixWord, tailWord_277299, baseEnd_277299] using wordTrace_append hprefix tailTrace_277299
  have hstable : (prefixWord ++ tailWord_277299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277299).length < 2 ^ (prefixWord ++ tailWord_277299).sum := by decide
  have hdescent : baseEnd_277299 < baseStart_277299 := by decide
  rcases family_descends (prefixWord ++ tailWord_277299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277361 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 6]
def baseStart_277361 : Nat := 118140960795 + 277361 * 2 ^ 59
def prefixEnd_277361 : Nat := 4983230072969 + 3 ^ 40 * 277361 * 2
def baseEnd_277361 : Nat := 63297559027464247783087

theorem tailTrace_277361 : CollatzResearch.WordTrace tailWord_277361 prefixEnd_277361 63297559027464247783087 := by
  unfold tailWord_277361
  simp only [CollatzResearch.WordTrace]
  refine ⟨10116186748175941332631937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6744124498783960888421291 10116186748175941332631937)
  ·
    refine ⟨7587140061131955999473953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10116186748175941332631937 7587140061131955999473953)
    ·
      refine ⟨5690355045848966999605465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7587140061131955999473953 5690355045848966999605465)
      ·
        refine ⟨4267766284386725249704099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5690355045848966999605465 4267766284386725249704099)
        ·
          refine ⟨6401649426580087874556149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4267766284386725249704099 6401649426580087874556149)
          ·
            refine ⟨600154633741883238239639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6401649426580087874556149 600154633741883238239639)
            ·
              refine ⟨900231950612824857359459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600154633741883238239639 900231950612824857359459)
              ·
                refine ⟨1350347925919237286039189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 900231950612824857359459 1350347925919237286039189)
                ·
                  refine ⟨63297559027464247783087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1350347925919237286039189 63297559027464247783087)
                  ·
                    rfl

theorem cell21_277361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_277361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277361 prefixEnd_277361 := by exact prefixLift 277361
  have htrace : WordTrace (prefixWord ++ tailWord_277361) baseStart_277361 baseEnd_277361 := by
    simpa [prefixWord, tailWord_277361, baseEnd_277361] using wordTrace_append hprefix tailTrace_277361
  have hstable : (prefixWord ++ tailWord_277361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277361).length < 2 ^ (prefixWord ++ tailWord_277361).sum := by decide
  have hdescent : baseEnd_277361 < baseStart_277361 := by decide
  rcases family_descends (prefixWord ++ tailWord_277361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277451 : List Nat := [1, 1, 1, 1, 3, 5, 2, 7]
def baseStart_277451 : Nat := 118140960795 + 277451 * 2 ^ 59
def prefixEnd_277451 : Nat := 4983230072969 + 3 ^ 40 * 277451 * 2
def baseEnd_277451 : Nat := 21106032751214697094301

theorem tailTrace_277451 : CollatzResearch.WordTrace tailWord_277451 prefixEnd_277451 21106032751214697094301 := by
  unfold tailWord_277451
  simp only [CollatzResearch.WordTrace]
  refine ⟨10119469317849886703408207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6746312878566591135605471 10119469317849886703408207)
  ·
    refine ⟨15179203976774830055112311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10119469317849886703408207 15179203976774830055112311)
    ·
      refine ⟨22768805965162245082668467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15179203976774830055112311 22768805965162245082668467)
      ·
        refine ⟨34153208947743367624002701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22768805965162245082668467 34153208947743367624002701)
        ·
          refine ⟨12807453355403762859001013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34153208947743367624002701 12807453355403762859001013)
          ·
            refine ⟨1200698752069102768031345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12807453355403762859001013 1200698752069102768031345)
            ·
              refine ⟨900524064051827076023509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1200698752069102768031345 900524064051827076023509)
              ·
                refine ⟨21106032751214697094301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 900524064051827076023509 21106032751214697094301)
                ·
                  rfl

theorem cell21_277451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 7].length) (baseStart_277451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277451 prefixEnd_277451 := by exact prefixLift 277451
  have htrace : WordTrace (prefixWord ++ tailWord_277451) baseStart_277451 baseEnd_277451 := by
    simpa [prefixWord, tailWord_277451, baseEnd_277451] using wordTrace_append hprefix tailTrace_277451
  have hstable : (prefixWord ++ tailWord_277451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277451).length < 2 ^ (prefixWord ++ tailWord_277451).sum := by decide
  have hdescent : baseEnd_277451 < baseStart_277451 := by decide
  rcases family_descends (prefixWord ++ tailWord_277451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277468 : List Nat := [2, 2, 6, 11]
def baseStart_277468 : Nat := 118140960795 + 277468 * 2 ^ 59
def prefixEnd_277468 : Nat := 4983230072969 + 3 ^ 40 * 277468 * 2
def baseEnd_277468 : Nat := 260584271132740080245

theorem tailTrace_277468 : CollatzResearch.WordTrace tailWord_277468 prefixEnd_277468 260584271132740080245 := by
  unfold tailWord_277468
  simp only [CollatzResearch.WordTrace]
  refine ⟨5060044679394149303388529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6746726239192199071184705 5060044679394149303388529)
  ·
    refine ⟨3795033509545611977541397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5060044679394149303388529 3795033509545611977541397)
    ·
      refine ⟨177892195759950561447253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3795033509545611977541397 177892195759950561447253)
      ·
        refine ⟨260584271132740080245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 177892195759950561447253 260584271132740080245)
        ·
          rfl

theorem cell21_277468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 11].length) (baseStart_277468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277468 prefixEnd_277468 := by exact prefixLift 277468
  have htrace : WordTrace (prefixWord ++ tailWord_277468) baseStart_277468 baseEnd_277468 := by
    simpa [prefixWord, tailWord_277468, baseEnd_277468] using wordTrace_append hprefix tailTrace_277468
  have hstable : (prefixWord ++ tailWord_277468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277468).length < 2 ^ (prefixWord ++ tailWord_277468).sum := by decide
  have hdescent : baseEnd_277468 < baseStart_277468 := by decide
  rcases family_descends (prefixWord ++ tailWord_277468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_277474 : List Nat := [3, 3, 3, 1, 1, 1, 4, 2, 3]
def baseStart_277474 : Nat := 118140960795 + 277474 * 2 ^ 59
def prefixEnd_277474 : Nat := 4983230072969 + 3 ^ 40 * 277474 * 2
def baseEnd_277474 : Nat := 63323347167001162399523

theorem tailTrace_277474 : CollatzResearch.WordTrace tailWord_277474 prefixEnd_277474 63323347167001162399523 := by
  unfold tailWord_277474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2530077049191640407873869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6746872131177707754330317 2530077049191640407873869)
  ·
    refine ⟨948778893446865152952701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2530077049191640407873869 948778893446865152952701)
    ·
      refine ⟨355792085042574432357263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 948778893446865152952701 355792085042574432357263)
      ·
        refine ⟨533688127563861648535895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355792085042574432357263 533688127563861648535895)
        ·
          refine ⟨800532191345792472803843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533688127563861648535895 800532191345792472803843)
          ·
            refine ⟨1200798287018688709205765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 800532191345792472803843 1200798287018688709205765)
            ·
              refine ⟨225149678816004132976081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1200798287018688709205765 225149678816004132976081)
              ·
                refine ⟨168862259112003099732061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225149678816004132976081 168862259112003099732061)
                ·
                  refine ⟨63323347167001162399523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168862259112003099732061 63323347167001162399523)
                  ·
                    rfl

theorem cell21_277474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_277474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_277474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_277474 prefixEnd_277474 := by exact prefixLift 277474
  have htrace : WordTrace (prefixWord ++ tailWord_277474) baseStart_277474 baseEnd_277474 := by
    simpa [prefixWord, tailWord_277474, baseEnd_277474] using wordTrace_append hprefix tailTrace_277474
  have hstable : (prefixWord ++ tailWord_277474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_277474).length < 2 ^ (prefixWord ++ tailWord_277474).sum := by decide
  have hdescent : baseEnd_277474 < baseStart_277474 := by decide
  rcases family_descends (prefixWord ++ tailWord_277474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
