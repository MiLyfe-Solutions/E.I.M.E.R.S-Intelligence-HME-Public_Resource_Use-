import V185TrunkScan20Chunk008

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_55153 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 6]
def baseStart_55153 : Nat := 118140960795 + 55153 * 2 ^ 59
def prefixEnd_55153 : Nat := 4983230072969 + 3 ^ 40 * 55153 * 2
def baseEnd_55153 : Nat := 25173332033358175407877

theorem tailTrace_55153 : CollatzResearch.WordTrace tailWord_55153 prefixEnd_55153 25173332033358175407877 := by
  unfold tailWord_55153
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011595169197575227594113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1341063446131716818396075 2011595169197575227594113)
  ·
    refine ⟨1508696376898181420695585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2011595169197575227594113 1508696376898181420695585)
    ·
      refine ⟨1131522282673636065521689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1508696376898181420695585 1131522282673636065521689)
      ·
        refine ⟨848641712005227049141267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131522282673636065521689 848641712005227049141267)
        ·
          refine ⟨1272962568007840573711901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848641712005227049141267 1272962568007840573711901)
          ·
            refine ⟨477360963002940215141963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1272962568007840573711901 477360963002940215141963)
            ·
              refine ⟨716041444504410322712945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477360963002940215141963 716041444504410322712945)
              ·
                refine ⟨537031083378307742034709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716041444504410322712945 537031083378307742034709)
                ·
                  refine ⟨25173332033358175407877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 537031083378307742034709 25173332033358175407877)
                  ·
                    rfl

theorem cell20_55153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_55153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55153 prefixEnd_55153 := by exact prefixLift 55153
  have htrace : WordTrace (prefixWord ++ tailWord_55153) baseStart_55153 baseEnd_55153 := by
    simpa [prefixWord, tailWord_55153, baseEnd_55153] using wordTrace_append hprefix tailTrace_55153
  have hstable : (prefixWord ++ tailWord_55153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55153).length < 2 ^ (prefixWord ++ tailWord_55153).sum := by decide
  have hdescent : baseEnd_55153 < baseStart_55153 := by decide
  rcases family_descends (prefixWord ++ tailWord_55153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55166 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_55166 : Nat := 118140960795 + 55166 * 2 ^ 59
def prefixEnd_55166 : Nat := 4983230072969 + 3 ^ 40 * 55166 * 2
def baseEnd_55166 : Nat := 25179265587587907974491

theorem tailTrace_55166 : CollatzResearch.WordTrace tailWord_55166 prefixEnd_55166 25179265587587907974491 := by
  unfold tailWord_55166
  simp only [CollatzResearch.WordTrace]
  refine ⟨251508664768809805977169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1341379545433652298544901 251508664768809805977169)
  ·
    refine ⟨188631498576607354482877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251508664768809805977169 188631498576607354482877)
    ·
      refine ⟨70736811966227757931079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188631498576607354482877 70736811966227757931079)
      ·
        refine ⟨106105217949341636896619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70736811966227757931079 106105217949341636896619)
        ·
          refine ⟨159157826924012455344929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106105217949341636896619 159157826924012455344929)
          ·
            refine ⟨119368370193009341508697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159157826924012455344929 119368370193009341508697)
            ·
              refine ⟨89526277644757006131523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119368370193009341508697 89526277644757006131523)
              ·
                refine ⟨134289416467135509197285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89526277644757006131523 134289416467135509197285)
                ·
                  refine ⟨25179265587587907974491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134289416467135509197285 25179265587587907974491)
                  ·
                    rfl

theorem cell20_55166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_55166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55166 prefixEnd_55166 := by exact prefixLift 55166
  have htrace : WordTrace (prefixWord ++ tailWord_55166) baseStart_55166 baseEnd_55166 := by
    simpa [prefixWord, tailWord_55166, baseEnd_55166] using wordTrace_append hprefix tailTrace_55166
  have hstable : (prefixWord ++ tailWord_55166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55166).length < 2 ^ (prefixWord ++ tailWord_55166).sum := by decide
  have hdescent : baseEnd_55166 < baseStart_55166 := by decide
  rcases family_descends (prefixWord ++ tailWord_55166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55190 : List Nat := [5, 3, 1, 1, 2, 1, 1, 6]
def baseStart_55190 : Nat := 118140960795 + 55190 * 2 ^ 59
def prefixEnd_55190 : Nat := 4983230072969 + 3 ^ 40 * 55190 * 2
def baseEnd_55190 : Nat := 8396739947183497058131

theorem tailTrace_55190 : CollatzResearch.WordTrace tailWord_55190 prefixEnd_55190 8396739947183497058131 := by
  unfold tailWord_55190
  simp only [CollatzResearch.WordTrace]
  refine ⟨125809041878970659168189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1341963113375687031127349 125809041878970659168189)
  ·
    refine ⟨47178390704613997188071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125809041878970659168189 47178390704613997188071)
    ·
      refine ⟨70767586056920995782107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47178390704613997188071 70767586056920995782107)
      ·
        refine ⟨106151379085381493673161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70767586056920995782107 106151379085381493673161)
        ·
          refine ⟨79613534314036120254871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106151379085381493673161 79613534314036120254871)
          ·
            refine ⟨119420301471054180382307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79613534314036120254871 119420301471054180382307)
            ·
              refine ⟨179130452206581270573461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119420301471054180382307 179130452206581270573461)
              ·
                refine ⟨8396739947183497058131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179130452206581270573461 8396739947183497058131)
                ·
                  rfl

theorem cell20_55190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_55190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55190 prefixEnd_55190 := by exact prefixLift 55190
  have htrace : WordTrace (prefixWord ++ tailWord_55190) baseStart_55190 baseEnd_55190 := by
    simpa [prefixWord, tailWord_55190, baseEnd_55190] using wordTrace_append hprefix tailTrace_55190
  have hstable : (prefixWord ++ tailWord_55190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55190).length < 2 ^ (prefixWord ++ tailWord_55190).sum := by decide
  have hdescent : baseEnd_55190 < baseStart_55190 := by decide
  rcases family_descends (prefixWord ++ tailWord_55190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55194 : List Nat := [3, 1, 1, 4, 2, 1, 4, 4]
def baseStart_55194 : Nat := 118140960795 + 55194 * 2 ^ 59
def prefixEnd_55194 : Nat := 4983230072969 + 3 ^ 40 * 55194 * 2
def baseEnd_55194 : Nat := 8397348516848085013681

theorem tailTrace_55194 : CollatzResearch.WordTrace tailWord_55194 prefixEnd_55194 8397348516848085013681 := by
  unfold tailWord_55194
  simp only [CollatzResearch.WordTrace]
  refine ⟨503272640512259807459159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1342060374699359486557757 503272640512259807459159)
  ·
    refine ⟨754908960768389711188739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503272640512259807459159 754908960768389711188739)
    ·
      refine ⟨1132363441152584566783109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754908960768389711188739 1132363441152584566783109)
      ·
        refine ⟨212318145216109606271833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1132363441152584566783109 212318145216109606271833)
        ·
          refine ⟨159238608912082204703875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212318145216109606271833 159238608912082204703875)
          ·
            refine ⟨238857913368123307055813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159238608912082204703875 238857913368123307055813)
            ·
              refine ⟨44785858756523120072965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238857913368123307055813 44785858756523120072965)
              ·
                refine ⟨8397348516848085013681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44785858756523120072965 8397348516848085013681)
                ·
                  rfl

theorem cell20_55194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_55194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55194 prefixEnd_55194 := by exact prefixLift 55194
  have htrace : WordTrace (prefixWord ++ tailWord_55194) baseStart_55194 baseEnd_55194 := by
    simpa [prefixWord, tailWord_55194, baseEnd_55194] using wordTrace_append hprefix tailTrace_55194
  have hstable : (prefixWord ++ tailWord_55194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55194).length < 2 ^ (prefixWord ++ tailWord_55194).sum := by decide
  have hdescent : baseEnd_55194 < baseStart_55194 := by decide
  rcases family_descends (prefixWord ++ tailWord_55194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55204 : List Nat := [2, 3, 1, 2, 1, 5, 1, 3, 2]
def baseStart_55204 : Nat := 118140960795 + 55204 * 2 ^ 59
def prefixEnd_55204 : Nat := 4983230072969 + 3 ^ 40 * 55204 * 2
def baseEnd_55204 : Nat := 25196609823028664707669

theorem tailTrace_55204 : CollatzResearch.WordTrace tailWord_55204 prefixEnd_55204 25196609823028664707669 := by
  unfold tailWord_55204
  simp only [CollatzResearch.WordTrace]
  refine ⟨1006727646006405468850333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1342303528008540625133777 1006727646006405468850333)
  ·
    refine ⟨377522867252402050818875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1006727646006405468850333 377522867252402050818875)
    ·
      refine ⟨566284300878603076228313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377522867252402050818875 566284300878603076228313)
      ·
        refine ⟨424713225658952307171235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566284300878603076228313 424713225658952307171235)
        ·
          refine ⟨637069838488428460756853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424713225658952307171235 637069838488428460756853)
          ·
            refine ⟨59725297358290168195955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 637069838488428460756853 59725297358290168195955)
            ·
              refine ⟨89587946037435252293933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59725297358290168195955 89587946037435252293933)
              ·
                refine ⟨33595479764038219610225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89587946037435252293933 33595479764038219610225)
                ·
                  refine ⟨25196609823028664707669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33595479764038219610225 25196609823028664707669)
                  ·
                    rfl

theorem cell20_55204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_55204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55204 prefixEnd_55204 := by exact prefixLift 55204
  have htrace : WordTrace (prefixWord ++ tailWord_55204) baseStart_55204 baseEnd_55204 := by
    simpa [prefixWord, tailWord_55204, baseEnd_55204] using wordTrace_append hprefix tailTrace_55204
  have hstable : (prefixWord ++ tailWord_55204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55204).length < 2 ^ (prefixWord ++ tailWord_55204).sum := by decide
  have hdescent : baseEnd_55204 < baseStart_55204 := by decide
  rcases family_descends (prefixWord ++ tailWord_55204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55253 : List Nat := [1, 3, 2, 3, 2, 1, 2, 6]
def baseStart_55253 : Nat := 118140960795 + 55253 * 2 ^ 59
def prefixEnd_55253 : Nat := 4983230072969 + 3 ^ 40 * 55253 * 2
def baseEnd_55253 : Nat := 8406324919400757358045

theorem tailTrace_55253 : CollatzResearch.WordTrace tailWord_55253 prefixEnd_55253 8406324919400757358045 := by
  unfold tailWord_55253
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015242468835292306234413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1343494979223528204156275 2015242468835292306234413)
  ·
    refine ⟨755715925813234614837905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2015242468835292306234413 755715925813234614837905)
    ·
      refine ⟨566786944359925961128429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 755715925813234614837905 566786944359925961128429)
      ·
        refine ⟨212545104134972235423161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 566786944359925961128429 212545104134972235423161)
        ·
          refine ⟨159408828101229176567371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212545104134972235423161 159408828101229176567371)
          ·
            refine ⟨239113242151843764851057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159408828101229176567371 239113242151843764851057)
            ·
              refine ⟨179334931613882823638293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239113242151843764851057 179334931613882823638293)
              ·
                refine ⟨8406324919400757358045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179334931613882823638293 8406324919400757358045)
                ·
                  rfl

theorem cell20_55253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 6].length) (baseStart_55253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55253 prefixEnd_55253 := by exact prefixLift 55253
  have htrace : WordTrace (prefixWord ++ tailWord_55253) baseStart_55253 baseEnd_55253 := by
    simpa [prefixWord, tailWord_55253, baseEnd_55253] using wordTrace_append hprefix tailTrace_55253
  have hstable : (prefixWord ++ tailWord_55253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55253).length < 2 ^ (prefixWord ++ tailWord_55253).sum := by decide
  have hdescent : baseEnd_55253 < baseStart_55253 := by decide
  rcases family_descends (prefixWord ++ tailWord_55253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55294 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 3]
def baseStart_55294 : Nat := 118140960795 + 55294 * 2 ^ 59
def prefixEnd_55294 : Nat := 4983230072969 + 3 ^ 40 * 55294 * 2
def baseEnd_55294 : Nat := 25237688275388351707301

theorem tailTrace_55294 : CollatzResearch.WordTrace tailWord_55294 prefixEnd_55294 25237688275388351707301 := by
  unfold tailWord_55294
  simp only [CollatzResearch.WordTrace]
  refine ⟨252092232710844538559617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1344491907791170872317957 252092232710844538559617)
  ·
    refine ⟨189069174533133403919713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252092232710844538559617 189069174533133403919713)
    ·
      refine ⟨141801880899850052939785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189069174533133403919713 141801880899850052939785)
      ·
        refine ⟨106351410674887539704839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141801880899850052939785 106351410674887539704839)
        ·
          refine ⟨159527116012331309557259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106351410674887539704839 159527116012331309557259)
          ·
            refine ⟨239290674018496964335889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159527116012331309557259 239290674018496964335889)
            ·
              refine ⟨179468005513872723251917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239290674018496964335889 179468005513872723251917)
              ·
                refine ⟨67300502067702271219469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179468005513872723251917 67300502067702271219469)
                ·
                  refine ⟨25237688275388351707301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67300502067702271219469 25237688275388351707301)
                  ·
                    rfl

theorem cell20_55294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_55294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55294 prefixEnd_55294 := by exact prefixLift 55294
  have htrace : WordTrace (prefixWord ++ tailWord_55294) baseStart_55294 baseEnd_55294 := by
    simpa [prefixWord, tailWord_55294, baseEnd_55294] using wordTrace_append hprefix tailTrace_55294
  have hstable : (prefixWord ++ tailWord_55294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55294).length < 2 ^ (prefixWord ++ tailWord_55294).sum := by decide
  have hdescent : baseEnd_55294 < baseStart_55294 := by decide
  rcases family_descends (prefixWord ++ tailWord_55294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55329 : List Nat := [1, 2, 3, 2, 4, 1, 7]
def baseStart_55329 : Nat := 118140960795 + 55329 * 2 ^ 59
def prefixEnd_55329 : Nat := 4983230072969 + 3 ^ 40 * 55329 * 2
def baseEnd_55329 : Nat := 2805962581009309504499

theorem tailTrace_55329 : CollatzResearch.WordTrace tailWord_55329 prefixEnd_55329 2805962581009309504499 := by
  unfold tailWord_55329
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018014416559957286001041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1345342944373304857334027 2018014416559957286001041)
  ·
    refine ⟨1513510812419967964500781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2018014416559957286001041 1513510812419967964500781)
    ·
      refine ⟨567566554657487986687793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1513510812419967964500781 567566554657487986687793)
      ·
        refine ⟨425674915993115990015845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567566554657487986687793 425674915993115990015845)
        ·
          refine ⟨79814046748709248127971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 425674915993115990015845 79814046748709248127971)
          ·
            refine ⟨119721070123063872191957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79814046748709248127971 119721070123063872191957)
            ·
              refine ⟨2805962581009309504499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 119721070123063872191957 2805962581009309504499)
              ·
                rfl

theorem cell20_55329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 7].length) (baseStart_55329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55329 prefixEnd_55329 := by exact prefixLift 55329
  have htrace : WordTrace (prefixWord ++ tailWord_55329) baseStart_55329 baseEnd_55329 := by
    simpa [prefixWord, tailWord_55329, baseEnd_55329] using wordTrace_append hprefix tailTrace_55329
  have hstable : (prefixWord ++ tailWord_55329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55329).length < 2 ^ (prefixWord ++ tailWord_55329).sum := by decide
  have hdescent : baseEnd_55329 < baseStart_55329 := by decide
  rcases family_descends (prefixWord ++ tailWord_55329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55374 : List Nat := [4, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_55374 : Nat := 118140960795 + 55374 * 2 ^ 59
def prefixEnd_55374 : Nat := 4983230072969 + 3 ^ 40 * 55374 * 2
def baseEnd_55374 : Nat := 25274202455263629040307

theorem tailTrace_55374 : CollatzResearch.WordTrace tailWord_55374 prefixEnd_55374 25274202455263629040307 := by
  unfold tailWord_55374
  simp only [CollatzResearch.WordTrace]
  refine ⟨252456962674616246423647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1346437134264619980926117 252456962674616246423647)
  ·
    refine ⟨378685444011924369635471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252456962674616246423647 378685444011924369635471)
    ·
      refine ⟨568028166017886554453207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378685444011924369635471 568028166017886554453207)
      ·
        refine ⟨852042249026829831679811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568028166017886554453207 852042249026829831679811)
        ·
          refine ⟨1278063373540244747519717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852042249026829831679811 1278063373540244747519717)
          ·
            refine ⟨239636882538795890159947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1278063373540244747519717 239636882538795890159947)
            ·
              refine ⟨359455323808193835239921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239636882538795890159947 359455323808193835239921)
              ·
                refine ⟨269591492856145376429941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359455323808193835239921 269591492856145376429941)
                ·
                  refine ⟨25274202455263629040307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269591492856145376429941 25274202455263629040307)
                  ·
                    rfl

theorem cell20_55374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_55374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55374 prefixEnd_55374 := by exact prefixLift 55374
  have htrace : WordTrace (prefixWord ++ tailWord_55374) baseStart_55374 baseEnd_55374 := by
    simpa [prefixWord, tailWord_55374, baseEnd_55374] using wordTrace_append hprefix tailTrace_55374
  have hstable : (prefixWord ++ tailWord_55374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55374).length < 2 ^ (prefixWord ++ tailWord_55374).sum := by decide
  have hdescent : baseEnd_55374 < baseStart_55374 := by decide
  rcases family_descends (prefixWord ++ tailWord_55374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55390 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_55390 : Nat := 118140960795 + 55390 * 2 ^ 59
def prefixEnd_55390 : Nat := 4983230072969 + 3 ^ 40 * 55390 * 2
def baseEnd_55390 : Nat := 25281505291238684506909

theorem tailTrace_55390 : CollatzResearch.WordTrace tailWord_55390 prefixEnd_55390 25281505291238684506909 := by
  unfold tailWord_55390
  simp only [CollatzResearch.WordTrace]
  refine ⟨252529908667370587996453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1346826179559309802647749 252529908667370587996453)
  ·
    refine ⟨47349357875131985249335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252529908667370587996453 47349357875131985249335)
    ·
      refine ⟨71024036812697977874003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47349357875131985249335 71024036812697977874003)
      ·
        refine ⟨106536055219046966811005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71024036812697977874003 106536055219046966811005)
        ·
          refine ⟨39951020707142612554127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106536055219046966811005 39951020707142612554127)
          ·
            refine ⟨59926531060713918831191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39951020707142612554127 59926531060713918831191)
            ·
              refine ⟨89889796591070878246787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59926531060713918831191 89889796591070878246787)
              ·
                refine ⟨134834694886606317370181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89889796591070878246787 134834694886606317370181)
                ·
                  refine ⟨25281505291238684506909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134834694886606317370181 25281505291238684506909)
                  ·
                    rfl

theorem cell20_55390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_55390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55390 prefixEnd_55390 := by exact prefixLift 55390
  have htrace : WordTrace (prefixWord ++ tailWord_55390) baseStart_55390 baseEnd_55390 := by
    simpa [prefixWord, tailWord_55390, baseEnd_55390] using wordTrace_append hprefix tailTrace_55390
  have hstable : (prefixWord ++ tailWord_55390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55390).length < 2 ^ (prefixWord ++ tailWord_55390).sum := by decide
  have hdescent : baseEnd_55390 < baseStart_55390 := by decide
  rcases family_descends (prefixWord ++ tailWord_55390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55394 : List Nat := [3, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_55394 : Nat := 118140960795 + 55394 * 2 ^ 59
def prefixEnd_55394 : Nat := 4983230072969 + 3 ^ 40 * 55394 * 2
def baseEnd_55394 : Nat := 25283331000232448373559

theorem tailTrace_55394 : CollatzResearch.WordTrace tailWord_55394 prefixEnd_55394 25283331000232448373559 := by
  unfold tailWord_55394
  simp only [CollatzResearch.WordTrace]
  refine ⟨505096290331118346779309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1346923440882982258078157 505096290331118346779309)
  ·
    refine ⟨189411108874169380042241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 505096290331118346779309 189411108874169380042241)
    ·
      refine ⟨142058331655627035031681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189411108874169380042241 142058331655627035031681)
      ·
        refine ⟨106543748741720276273761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142058331655627035031681 106543748741720276273761)
        ·
          refine ⟨79907811556290207205321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106543748741720276273761 79907811556290207205321)
          ·
            refine ⟨59930858667217655403991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79907811556290207205321 59930858667217655403991)
            ·
              refine ⟨89896288000826483105987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59930858667217655403991 89896288000826483105987)
              ·
                refine ⟨134844432001239724658981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89896288000826483105987 134844432001239724658981)
                ·
                  refine ⟨25283331000232448373559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134844432001239724658981 25283331000232448373559)
                  ·
                    rfl

theorem cell20_55394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_55394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55394 prefixEnd_55394 := by exact prefixLift 55394
  have htrace : WordTrace (prefixWord ++ tailWord_55394) baseStart_55394 baseEnd_55394 := by
    simpa [prefixWord, tailWord_55394, baseEnd_55394] using wordTrace_append hprefix tailTrace_55394
  have hstable : (prefixWord ++ tailWord_55394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55394).length < 2 ^ (prefixWord ++ tailWord_55394).sum := by decide
  have hdescent : baseEnd_55394 < baseStart_55394 := by decide
  rcases family_descends (prefixWord ++ tailWord_55394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55405 : List Nat := [1, 5, 1, 1, 2, 1, 4, 5]
def baseStart_55405 : Nat := 118140960795 + 55405 * 2 ^ 59
def prefixEnd_55405 : Nat := 4983230072969 + 3 ^ 40 * 55405 * 2
def baseEnd_55405 : Nat := 8429450566655099668949

theorem tailTrace_55405 : CollatzResearch.WordTrace tailWord_55405 prefixEnd_55405 8429450566655099668949 := by
  unfold tailWord_55405
  simp only [CollatzResearch.WordTrace]
  refine ⟨2020786364284622265767669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1347190909523081510511779 2020786364284622265767669)
  ·
    refine ⟨189448721651683337415719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2020786364284622265767669 189448721651683337415719)
    ·
      refine ⟨284173082477525006123579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189448721651683337415719 284173082477525006123579)
      ·
        refine ⟨426259623716287509185369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284173082477525006123579 426259623716287509185369)
        ·
          refine ⟨319694717787215631889027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426259623716287509185369 319694717787215631889027)
          ·
            refine ⟨479542076680823447833541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319694717787215631889027 479542076680823447833541)
            ·
              refine ⟨89914139377654396468789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 479542076680823447833541 89914139377654396468789)
              ·
                refine ⟨8429450566655099668949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89914139377654396468789 8429450566655099668949)
                ·
                  rfl

theorem cell20_55405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 5].length) (baseStart_55405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55405 prefixEnd_55405 := by exact prefixLift 55405
  have htrace : WordTrace (prefixWord ++ tailWord_55405) baseStart_55405 baseEnd_55405 := by
    simpa [prefixWord, tailWord_55405, baseEnd_55405] using wordTrace_append hprefix tailTrace_55405
  have hstable : (prefixWord ++ tailWord_55405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55405).length < 2 ^ (prefixWord ++ tailWord_55405).sum := by decide
  have hdescent : baseEnd_55405 < baseStart_55405 := by decide
  rcases family_descends (prefixWord ++ tailWord_55405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55408 : List Nat := [2, 1, 1, 1, 5, 4, 2, 1, 3]
def baseStart_55408 : Nat := 118140960795 + 55408 * 2 ^ 59
def prefixEnd_55408 : Nat := 4983230072969 + 3 ^ 40 * 55408 * 2
def baseEnd_55408 : Nat := 25289720981710621906835

theorem tailTrace_55408 : CollatzResearch.WordTrace tailWord_55408 prefixEnd_55408 25289720981710621906835 := by
  unfold tailWord_55408
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010447891636876889063439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1347263855515835852084585 1010447891636876889063439)
  ·
    refine ⟨1515671837455315333595159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1010447891636876889063439 1515671837455315333595159)
    ·
      refine ⟨2273507756182973000392739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1515671837455315333595159 2273507756182973000392739)
      ·
        refine ⟨3410261634274459500589109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2273507756182973000392739 3410261634274459500589109)
        ·
          refine ⟨319712028213230578180229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3410261634274459500589109 319712028213230578180229)
          ·
            refine ⟨59946005289980733408793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319712028213230578180229 59946005289980733408793)
            ·
              refine ⟨44959503967485550056595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59946005289980733408793 44959503967485550056595)
              ·
                refine ⟨67439255951228325084893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44959503967485550056595 67439255951228325084893)
                ·
                  refine ⟨25289720981710621906835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67439255951228325084893 25289720981710621906835)
                  ·
                    rfl

theorem cell20_55408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_55408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55408 prefixEnd_55408 := by exact prefixLift 55408
  have htrace : WordTrace (prefixWord ++ tailWord_55408) baseStart_55408 baseEnd_55408 := by
    simpa [prefixWord, tailWord_55408, baseEnd_55408] using wordTrace_append hprefix tailTrace_55408
  have hstable : (prefixWord ++ tailWord_55408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55408).length < 2 ^ (prefixWord ++ tailWord_55408).sum := by decide
  have hdescent : baseEnd_55408 < baseStart_55408 := by decide
  rcases family_descends (prefixWord ++ tailWord_55408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55453 : List Nat := [1, 4, 2, 1, 1, 4, 1, 4, 2]
def baseStart_55453 : Nat := 118140960795 + 55453 * 2 ^ 59
def prefixEnd_55453 : Nat := 4983230072969 + 3 ^ 40 * 55453 * 2
def baseEnd_55453 : Nat := 25310260207890465406651

theorem tailTrace_55453 : CollatzResearch.WordTrace tailWord_55453 prefixEnd_55453 25310260207890465406651 := by
  unfold tailWord_55453
  simp only [CollatzResearch.WordTrace]
  refine ⟨2022537068110726463515013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1348358045407150975676675 2022537068110726463515013)
  ·
    refine ⟨379225700270761211909065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2022537068110726463515013 379225700270761211909065)
    ·
      refine ⟨284419275203070908931799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379225700270761211909065 284419275203070908931799)
      ·
        refine ⟨426628912804606363397699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284419275203070908931799 426628912804606363397699)
        ·
          refine ⟨639943369206909545096549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426628912804606363397699 639943369206909545096549)
          ·
            refine ⟨119989381726295539705603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 639943369206909545096549 119989381726295539705603)
            ·
              refine ⟨179984072589443309558405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119989381726295539705603 179984072589443309558405)
              ·
                refine ⟨33747013610520620542201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179984072589443309558405 33747013610520620542201)
                ·
                  refine ⟨25310260207890465406651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33747013610520620542201 25310260207890465406651)
                  ·
                    rfl

theorem cell20_55453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_55453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55453 prefixEnd_55453 := by exact prefixLift 55453
  have htrace : WordTrace (prefixWord ++ tailWord_55453) baseStart_55453 baseEnd_55453 := by
    simpa [prefixWord, tailWord_55453, baseEnd_55453] using wordTrace_append hprefix tailTrace_55453
  have hstable : (prefixWord ++ tailWord_55453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55453).length < 2 ^ (prefixWord ++ tailWord_55453).sum := by decide
  have hdescent : baseEnd_55453 < baseStart_55453 := by decide
  rcases family_descends (prefixWord ++ tailWord_55453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55460 : List Nat := [2, 3, 1, 2, 4, 2, 1, 5]
def baseStart_55460 : Nat := 118140960795 + 55460 * 2 ^ 59
def prefixEnd_55460 : Nat := 4983230072969 + 3 ^ 40 * 55460 * 2
def baseEnd_55460 : Nat := 8437818399543184057763

theorem tailTrace_55460 : CollatzResearch.WordTrace tailWord_55460 prefixEnd_55460 8437818399543184057763 := by
  unfold tailWord_55460
  simp only [CollatzResearch.WordTrace]
  refine ⟨1011396189542683329509917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1348528252723577772679889 1011396189542683329509917)
  ·
    refine ⟨379273571078506248566219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1011396189542683329509917 379273571078506248566219)
    ·
      refine ⟨568910356617759372849329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379273571078506248566219 568910356617759372849329)
      ·
        refine ⟨426682767463319529636997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568910356617759372849329 426682767463319529636997)
        ·
          refine ⟨80003018899372411806937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 426682767463319529636997 80003018899372411806937)
          ·
            refine ⟨60002264174529308855203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80003018899372411806937 60002264174529308855203)
            ·
              refine ⟨90003396261793963282805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60002264174529308855203 90003396261793963282805)
              ·
                refine ⟨8437818399543184057763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90003396261793963282805 8437818399543184057763)
                ·
                  rfl

theorem cell20_55460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_55460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55460 prefixEnd_55460 := by exact prefixLift 55460
  have htrace : WordTrace (prefixWord ++ tailWord_55460) baseStart_55460 baseEnd_55460 := by
    simpa [prefixWord, tailWord_55460, baseEnd_55460] using wordTrace_append hprefix tailTrace_55460
  have hstable : (prefixWord ++ tailWord_55460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55460).length < 2 ^ (prefixWord ++ tailWord_55460).sum := by decide
  have hdescent : baseEnd_55460 < baseStart_55460 := by decide
  rcases family_descends (prefixWord ++ tailWord_55460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55470 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_55470 : Nat := 118140960795 + 55470 * 2 ^ 59
def prefixEnd_55470 : Nat := 4983230072969 + 3 ^ 40 * 55470 * 2
def baseEnd_55470 : Nat := 25318019471113961839915

theorem tailTrace_55470 : CollatzResearch.WordTrace tailWord_55470 prefixEnd_55470 25318019471113961839915 := by
  unfold tailWord_55470
  simp only [CollatzResearch.WordTrace]
  refine ⟨252894638631142295860483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1348771406032758911255909 252894638631142295860483)
  ·
    refine ⟨379341957946713443790725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252894638631142295860483 379341957946713443790725)
    ·
      refine ⟨71126617115008770710761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379341957946713443790725 71126617115008770710761)
      ·
        refine ⟨53344962836256578033071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71126617115008770710761 53344962836256578033071)
        ·
          refine ⟨80017444254384867049607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53344962836256578033071 80017444254384867049607)
          ·
            refine ⟨120026166381577300574411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80017444254384867049607 120026166381577300574411)
            ·
              refine ⟨180039249572365950861617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120026166381577300574411 180039249572365950861617)
              ·
                refine ⟨135029437179274463146213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180039249572365950861617 135029437179274463146213)
                ·
                  refine ⟨25318019471113961839915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135029437179274463146213 25318019471113961839915)
                  ·
                    rfl

theorem cell20_55470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_55470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55470 prefixEnd_55470 := by exact prefixLift 55470
  have htrace : WordTrace (prefixWord ++ tailWord_55470) baseStart_55470 baseEnd_55470 := by
    simpa [prefixWord, tailWord_55470, baseEnd_55470] using wordTrace_append hprefix tailTrace_55470
  have hstable : (prefixWord ++ tailWord_55470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55470).length < 2 ^ (prefixWord ++ tailWord_55470).sum := by decide
  have hdescent : baseEnd_55470 < baseStart_55470 := by decide
  rcases family_descends (prefixWord ++ tailWord_55470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55471 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 7]
def baseStart_55471 : Nat := 118140960795 + 55471 * 2 ^ 59
def prefixEnd_55471 : Nat := 4983230072969 + 3 ^ 40 * 55471 * 2
def baseEnd_55471 : Nat := 25318475898362402806577

theorem tailTrace_55471 : CollatzResearch.WordTrace tailWord_55471 prefixEnd_55471 25318475898362402806577 := by
  unfold tailWord_55471
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023193582045515537670267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1348795721363677025113511 2023193582045515537670267)
  ·
    refine ⟨3034790373068273306505401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2023193582045515537670267 3034790373068273306505401)
    ·
      refine ⟨2276092779801204979879051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3034790373068273306505401 2276092779801204979879051)
      ·
        refine ⟨3414139169701807469818577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2276092779801204979879051 3414139169701807469818577)
        ·
          refine ⟨2560604377276355602363933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3414139169701807469818577 2560604377276355602363933)
          ·
            refine ⟨960226641478633350886475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2560604377276355602363933 960226641478633350886475)
            ·
              refine ⟨1440339962217950026329713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960226641478633350886475 1440339962217950026329713)
              ·
                refine ⟨1080254971663462519747285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1440339962217950026329713 1080254971663462519747285)
                ·
                  refine ⟨25318475898362402806577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1080254971663462519747285 25318475898362402806577)
                  ·
                    rfl

theorem cell20_55471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 7].length) (baseStart_55471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55471 prefixEnd_55471 := by exact prefixLift 55471
  have htrace : WordTrace (prefixWord ++ tailWord_55471) baseStart_55471 baseEnd_55471 := by
    simpa [prefixWord, tailWord_55471, baseEnd_55471] using wordTrace_append hprefix tailTrace_55471
  have hstable : (prefixWord ++ tailWord_55471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55471).length < 2 ^ (prefixWord ++ tailWord_55471).sum := by decide
  have hdescent : baseEnd_55471 < baseStart_55471 := by decide
  rcases family_descends (prefixWord ++ tailWord_55471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55477 : List Nat := [1, 3, 3, 4, 1, 1, 3, 4]
def baseStart_55477 : Nat := 118140960795 + 55477 * 2 ^ 59
def prefixEnd_55477 : Nat := 4983230072969 + 3 ^ 40 * 55477 * 2
def baseEnd_55477 : Nat := 8440404820617682868851

theorem tailTrace_55477 : CollatzResearch.WordTrace tailWord_55477 prefixEnd_55477 8440404820617682868851 := by
  unfold tailWord_55477
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023412420023778562388685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1348941613349185708259123 2023412420023778562388685)
  ·
    refine ⟨758779657508916960895757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2023412420023778562388685 758779657508916960895757)
    ·
      refine ⟨284542371565843860335909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 758779657508916960895757 284542371565843860335909)
      ·
        refine ⟨53351694668595723812983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284542371565843860335909 53351694668595723812983)
        ·
          refine ⟨80027542002893585719475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53351694668595723812983 80027542002893585719475)
          ·
            refine ⟨120041313004340378579213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80027542002893585719475 120041313004340378579213)
            ·
              refine ⟨45015492376627641967205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120041313004340378579213 45015492376627641967205)
              ·
                refine ⟨8440404820617682868851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45015492376627641967205 8440404820617682868851)
                ·
                  rfl

theorem cell20_55477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 4].length) (baseStart_55477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55477 prefixEnd_55477 := by exact prefixLift 55477
  have htrace : WordTrace (prefixWord ++ tailWord_55477) baseStart_55477 baseEnd_55477 := by
    simpa [prefixWord, tailWord_55477, baseEnd_55477] using wordTrace_append hprefix tailTrace_55477
  have hstable : (prefixWord ++ tailWord_55477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55477).length < 2 ^ (prefixWord ++ tailWord_55477).sum := by decide
  have hdescent : baseEnd_55477 < baseStart_55477 := by decide
  rcases family_descends (prefixWord ++ tailWord_55477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55481 : List Nat := [1, 2, 1, 4, 1, 2, 5, 4]
def baseStart_55481 : Nat := 118140960795 + 55481 * 2 ^ 59
def prefixEnd_55481 : Nat := 4983230072969 + 3 ^ 40 * 55481 * 2
def baseEnd_55481 : Nat := 8441013390282270824401

theorem tailTrace_55481 : CollatzResearch.WordTrace tailWord_55481 prefixEnd_55481 8441013390282270824401 := by
  unfold tailWord_55481
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023558312009287245534297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1349038874672858163689531 2023558312009287245534297)
  ·
    refine ⟨1517668734006965434150723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2023558312009287245534297 1517668734006965434150723)
    ·
      refine ⟨2276503101010448151226085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1517668734006965434150723 2276503101010448151226085)
      ·
        refine ⟨426844331439459028354891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2276503101010448151226085 426844331439459028354891)
        ·
          refine ⟨640266497159188542532337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426844331439459028354891 640266497159188542532337)
          ·
            refine ⟨480199872869391406899253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640266497159188542532337 480199872869391406899253)
            ·
              refine ⟨45018738081505444396805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 480199872869391406899253 45018738081505444396805)
              ·
                refine ⟨8441013390282270824401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45018738081505444396805 8441013390282270824401)
                ·
                  rfl

theorem cell20_55481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 4].length) (baseStart_55481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55481 prefixEnd_55481 := by exact prefixLift 55481
  have htrace : WordTrace (prefixWord ++ tailWord_55481) baseStart_55481 baseEnd_55481 := by
    simpa [prefixWord, tailWord_55481, baseEnd_55481] using wordTrace_append hprefix tailTrace_55481
  have hstable : (prefixWord ++ tailWord_55481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55481).length < 2 ^ (prefixWord ++ tailWord_55481).sum := by decide
  have hdescent : baseEnd_55481 < baseStart_55481 := by decide
  rcases family_descends (prefixWord ++ tailWord_55481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55512 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 4]
def baseStart_55512 : Nat := 118140960795 + 55512 * 2 ^ 59
def prefixEnd_55512 : Nat := 4983230072969 + 3 ^ 40 * 55512 * 2
def baseEnd_55512 : Nat := 25337189415548482439743

theorem tailTrace_55512 : CollatzResearch.WordTrace tailWord_55512 prefixEnd_55512 25337189415548482439743 := by
  unfold tailWord_55512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012344487448489769956395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1349792649931319693275193 1012344487448489769956395)
  ·
    refine ⟨1518516731172734654934593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1012344487448489769956395 1518516731172734654934593)
    ·
      refine ⟨1138887548379550991200945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1518516731172734654934593 1138887548379550991200945)
      ·
        refine ⟨854165661284663243400709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1138887548379550991200945 854165661284663243400709)
        ·
          refine ⟨160156061490874358137633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 854165661284663243400709 160156061490874358137633)
          ·
            refine ⟨120117046118155768603225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160156061490874358137633 120117046118155768603225)
            ·
              refine ⟨90087784588616826452419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120117046118155768603225 90087784588616826452419)
              ·
                refine ⟨135131676882925239678629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90087784588616826452419 135131676882925239678629)
                ·
                  refine ⟨25337189415548482439743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135131676882925239678629 25337189415548482439743)
                  ·
                    rfl

theorem cell20_55512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_55512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55512 prefixEnd_55512 := by exact prefixLift 55512
  have htrace : WordTrace (prefixWord ++ tailWord_55512) baseStart_55512 baseEnd_55512 := by
    simpa [prefixWord, tailWord_55512, baseEnd_55512] using wordTrace_append hprefix tailTrace_55512
  have hstable : (prefixWord ++ tailWord_55512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55512).length < 2 ^ (prefixWord ++ tailWord_55512).sum := by decide
  have hdescent : baseEnd_55512 < baseStart_55512 := by decide
  rcases family_descends (prefixWord ++ tailWord_55512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55564 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 3]
def baseStart_55564 : Nat := 118140960795 + 55564 * 2 ^ 59
def prefixEnd_55564 : Nat := 4983230072969 + 3 ^ 40 * 55564 * 2
def baseEnd_55564 : Nat := 25360923632467412706197

theorem tailTrace_55564 : CollatzResearch.WordTrace tailWord_55564 prefixEnd_55564 25360923632467412706197 := by
  unfold tailWord_55564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013292785354296210402873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1351057047139061613870497 1013292785354296210402873)
  ·
    refine ⟨759969589015722157802155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1013292785354296210402873 759969589015722157802155)
    ·
      refine ⟨1139954383523583236703233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759969589015722157802155 1139954383523583236703233)
      ·
        refine ⟨854965787642687427527425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1139954383523583236703233 854965787642687427527425)
        ·
          refine ⟨641224340732015570645569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854965787642687427527425 641224340732015570645569)
          ·
            refine ⟨480918255549011677984177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641224340732015570645569 480918255549011677984177)
            ·
              refine ⟨360688691661758758488133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480918255549011677984177 360688691661758758488133)
              ·
                refine ⟨67629129686579767216525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360688691661758758488133 67629129686579767216525)
                ·
                  refine ⟨25360923632467412706197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67629129686579767216525 25360923632467412706197)
                  ·
                    rfl

theorem cell20_55564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_55564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55564 prefixEnd_55564 := by exact prefixLift 55564
  have htrace : WordTrace (prefixWord ++ tailWord_55564) baseStart_55564 baseEnd_55564 := by
    simpa [prefixWord, tailWord_55564, baseEnd_55564] using wordTrace_append hprefix tailTrace_55564
  have hstable : (prefixWord ++ tailWord_55564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55564).length < 2 ^ (prefixWord ++ tailWord_55564).sum := by decide
  have hdescent : baseEnd_55564 < baseStart_55564 := by decide
  rcases family_descends (prefixWord ++ tailWord_55564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55633 : List Nat := [1, 2, 2, 1, 4, 4, 1, 5]
def baseStart_55633 : Nat := 118140960795 + 55633 * 2 ^ 59
def prefixEnd_55633 : Nat := 4983230072969 + 3 ^ 40 * 55633 * 2
def baseEnd_55633 : Nat := 8464139037536613135305

theorem tailTrace_55633 : CollatzResearch.WordTrace tailWord_55633 prefixEnd_55633 8464139037536613135305 := by
  unfold tailWord_55633
  simp only [CollatzResearch.WordTrace]
  refine ⟨2029102207458617205067553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1352734804972411470045035 2029102207458617205067553)
  ·
    refine ⟨1521826655593962903800665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2029102207458617205067553 1521826655593962903800665)
    ·
      refine ⟨1141369991695472177850499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1521826655593962903800665 1141369991695472177850499)
      ·
        refine ⟨1712054987543208266775749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1141369991695472177850499 1712054987543208266775749)
        ·
          refine ⟨321010310164351550020453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1712054987543208266775749 321010310164351550020453)
          ·
            refine ⟨60189433155815915628835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 321010310164351550020453 60189433155815915628835)
            ·
              refine ⟨90284149733723873443253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60189433155815915628835 90284149733723873443253)
              ·
                refine ⟨8464139037536613135305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90284149733723873443253 8464139037536613135305)
                ·
                  rfl

theorem cell20_55633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 5].length) (baseStart_55633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55633 prefixEnd_55633 := by exact prefixLift 55633
  have htrace : WordTrace (prefixWord ++ tailWord_55633) baseStart_55633 baseEnd_55633 := by
    simpa [prefixWord, tailWord_55633, baseEnd_55633] using wordTrace_append hprefix tailTrace_55633
  have hstable : (prefixWord ++ tailWord_55633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55633).length < 2 ^ (prefixWord ++ tailWord_55633).sum := by decide
  have hdescent : baseEnd_55633 < baseStart_55633 := by decide
  rcases family_descends (prefixWord ++ tailWord_55633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55650 : List Nat := [3, 3, 2, 1, 1, 3, 3, 4]
def baseStart_55650 : Nat := 118140960795 + 55650 * 2 ^ 59
def prefixEnd_55650 : Nat := 4983230072969 + 3 ^ 40 * 55650 * 2
def baseEnd_55650 : Nat := 8466725458611111946393

theorem tailTrace_55650 : CollatzResearch.WordTrace tailWord_55650 prefixEnd_55650 8466725458611111946393 := by
  unfold tailWord_55650
  simp only [CollatzResearch.WordTrace]
  refine ⟨507430562099257277109101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1353148165598019405624269 507430562099257277109101)
  ·
    refine ⟨190286460787221478915913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 507430562099257277109101 190286460787221478915913)
    ·
      refine ⟨142714845590416109186935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190286460787221478915913 142714845590416109186935)
      ·
        refine ⟨214072268385624163780403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142714845590416109186935 214072268385624163780403)
        ·
          refine ⟨321108402578436245670605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214072268385624163780403 321108402578436245670605)
          ·
            refine ⟨120415650966913592126477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 321108402578436245670605 120415650966913592126477)
            ·
              refine ⟨45155869112592597047429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120415650966913592126477 45155869112592597047429)
              ·
                refine ⟨8466725458611111946393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45155869112592597047429 8466725458611111946393)
                ·
                  rfl

theorem cell20_55650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_55650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55650 prefixEnd_55650 := by exact prefixLift 55650
  have htrace : WordTrace (prefixWord ++ tailWord_55650) baseStart_55650 baseEnd_55650 := by
    simpa [prefixWord, tailWord_55650, baseEnd_55650] using wordTrace_append hprefix tailTrace_55650
  have hstable : (prefixWord ++ tailWord_55650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55650).length < 2 ^ (prefixWord ++ tailWord_55650).sum := by decide
  have hdescent : baseEnd_55650 < baseStart_55650 := by decide
  rcases family_descends (prefixWord ++ tailWord_55650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55664 : List Nat := [2, 1, 1, 1, 4, 3, 1, 5, 2]
def baseStart_55664 : Nat := 118140960795 + 55664 * 2 ^ 59
def prefixEnd_55664 : Nat := 4983230072969 + 3 ^ 40 * 55664 * 2
def baseEnd_55664 : Nat := 25406566357311509372455

theorem tailTrace_55664 : CollatzResearch.WordTrace tailWord_55664 prefixEnd_55664 25406566357311509372455 := by
  unfold tailWord_55664
  simp only [CollatzResearch.WordTrace]
  refine ⟨1015116435173154749723023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1353488580230872999630697 1015116435173154749723023)
  ·
    refine ⟨1522674652759732124584535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1015116435173154749723023 1522674652759732124584535)
    ·
      refine ⟨2284011979139598186876803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1522674652759732124584535 2284011979139598186876803)
      ·
        refine ⟨3426017968709397280315205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2284011979139598186876803 3426017968709397280315205)
        ·
          refine ⟨642378369133011990059101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3426017968709397280315205 642378369133011990059101)
          ·
            refine ⟨240891888424879496272163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 642378369133011990059101 240891888424879496272163)
            ·
              refine ⟨361337832637319244408245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240891888424879496272163 361337832637319244408245)
              ·
                refine ⟨33875421809748679163273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 361337832637319244408245 33875421809748679163273)
                ·
                  refine ⟨25406566357311509372455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33875421809748679163273 25406566357311509372455)
                  ·
                    rfl

theorem cell20_55664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 2].length) (baseStart_55664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55664 prefixEnd_55664 := by exact prefixLift 55664
  have htrace : WordTrace (prefixWord ++ tailWord_55664) baseStart_55664 baseEnd_55664 := by
    simpa [prefixWord, tailWord_55664, baseEnd_55664] using wordTrace_append hprefix tailTrace_55664
  have hstable : (prefixWord ++ tailWord_55664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55664).length < 2 ^ (prefixWord ++ tailWord_55664).sum := by decide
  have hdescent : baseEnd_55664 < baseStart_55664 := by decide
  rcases family_descends (prefixWord ++ tailWord_55664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55670 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_55670 : Nat := 118140960795 + 55670 * 2 ^ 59
def prefixEnd_55670 : Nat := 4983230072969 + 3 ^ 40 * 55670 * 2
def baseEnd_55670 : Nat := 25409304920802155172431

theorem tailTrace_55670 : CollatzResearch.WordTrace tailWord_55670 prefixEnd_55670 25409304920802155172431 := by
  unfold tailWord_55670
  simp only [CollatzResearch.WordTrace]
  refine ⟨126903231770285782760279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1353634472216381682776309 126903231770285782760279)
  ·
    refine ⟨190354847655428674140419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126903231770285782760279 190354847655428674140419)
    ·
      refine ⟨285532271483143011210629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190354847655428674140419 285532271483143011210629)
      ·
        refine ⟨53537300903089314601993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285532271483143011210629 53537300903089314601993)
        ·
          refine ⟨40152975677316985951495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53537300903089314601993 40152975677316985951495)
          ·
            refine ⟨60229463515975478927243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40152975677316985951495 60229463515975478927243)
            ·
              refine ⟨90344195273963218390865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60229463515975478927243 90344195273963218390865)
              ·
                refine ⟨67758146455472413793149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90344195273963218390865 67758146455472413793149)
                ·
                  refine ⟨25409304920802155172431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67758146455472413793149 25409304920802155172431)
                  ·
                    rfl

theorem cell20_55670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_55670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55670 prefixEnd_55670 := by exact prefixLift 55670
  have htrace : WordTrace (prefixWord ++ tailWord_55670) baseStart_55670 baseEnd_55670 := by
    simpa [prefixWord, tailWord_55670, baseEnd_55670] using wordTrace_append hprefix tailTrace_55670
  have hstable : (prefixWord ++ tailWord_55670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55670).length < 2 ^ (prefixWord ++ tailWord_55670).sum := by decide
  have hdescent : baseEnd_55670 < baseStart_55670 := by decide
  rcases family_descends (prefixWord ++ tailWord_55670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55681 : List Nat := [1, 2, 4, 3, 1, 1, 2, 4, 2]
def baseStart_55681 : Nat := 118140960795 + 55681 * 2 ^ 59
def prefixEnd_55681 : Nat := 4983230072969 + 3 ^ 40 * 55681 * 2
def baseEnd_55681 : Nat := 25414325620535005805719

theorem tailTrace_55681 : CollatzResearch.WordTrace tailWord_55681 prefixEnd_55681 25414325620535005805719 := by
  unfold tailWord_55681
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030852911284721402814897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1353901940856480935209931 2030852911284721402814897)
  ·
    refine ⟨1523139683463541052111173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2030852911284721402814897 1523139683463541052111173)
    ·
      refine ⟨285588690649413947270845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1523139683463541052111173 285588690649413947270845)
      ·
        refine ⟨107095758993530230226567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285588690649413947270845 107095758993530230226567)
        ·
          refine ⟨160643638490295345339851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107095758993530230226567 160643638490295345339851)
          ·
            refine ⟨240965457735443018009777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160643638490295345339851 240965457735443018009777)
            ·
              refine ⟨180724093301582263507333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240965457735443018009777 180724093301582263507333)
              ·
                refine ⟨33885767494046674407625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180724093301582263507333 33885767494046674407625)
                ·
                  refine ⟨25414325620535005805719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33885767494046674407625 25414325620535005805719)
                  ·
                    rfl

theorem cell20_55681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 4, 2].length) (baseStart_55681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55681 prefixEnd_55681 := by exact prefixLift 55681
  have htrace : WordTrace (prefixWord ++ tailWord_55681) baseStart_55681 baseEnd_55681 := by
    simpa [prefixWord, tailWord_55681, baseEnd_55681] using wordTrace_append hprefix tailTrace_55681
  have hstable : (prefixWord ++ tailWord_55681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55681).length < 2 ^ (prefixWord ++ tailWord_55681).sum := by decide
  have hdescent : baseEnd_55681 < baseStart_55681 := by decide
  rcases family_descends (prefixWord ++ tailWord_55681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55709 : List Nat := [1, 4, 2, 1, 4, 1, 1, 6]
def baseStart_55709 : Nat := 118140960795 + 55709 * 2 ^ 59
def prefixEnd_55709 : Nat := 4983230072969 + 3 ^ 40 * 55709 * 2
def baseEnd_55709 : Nat := 8475701861163784290757

theorem tailTrace_55709 : CollatzResearch.WordTrace tailWord_55709 prefixEnd_55709 8475701861163784290757 := by
  unfold tailWord_55709
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031874155183282184834181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1354582770122188123222787 2031874155183282184834181)
  ·
    refine ⟨380976404096865409656409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2031874155183282184834181 380976404096865409656409)
    ·
      refine ⟨285732303072649057242307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380976404096865409656409 285732303072649057242307)
      ·
        refine ⟨428598454608973585863461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285732303072649057242307 428598454608973585863461)
        ·
          refine ⟨80362210239182547349399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 428598454608973585863461 80362210239182547349399)
          ·
            refine ⟨120543315358773821024099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80362210239182547349399 120543315358773821024099)
            ·
              refine ⟨180814973038160731536149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120543315358773821024099 180814973038160731536149)
              ·
                refine ⟨8475701861163784290757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180814973038160731536149 8475701861163784290757)
                ·
                  rfl

theorem cell20_55709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 6].length) (baseStart_55709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55709 prefixEnd_55709 := by exact prefixLift 55709
  have htrace : WordTrace (prefixWord ++ tailWord_55709) baseStart_55709 baseEnd_55709 := by
    simpa [prefixWord, tailWord_55709, baseEnd_55709] using wordTrace_append hprefix tailTrace_55709
  have hstable : (prefixWord ++ tailWord_55709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55709).length < 2 ^ (prefixWord ++ tailWord_55709).sum := by decide
  have hdescent : baseEnd_55709 < baseStart_55709 := by decide
  rcases family_descends (prefixWord ++ tailWord_55709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55719 : List Nat := [1, 1, 6, 1, 1, 2, 3, 3, 2]
def baseStart_55719 : Nat := 118140960795 + 55719 * 2 ^ 59
def prefixEnd_55719 : Nat := 4983230072969 + 3 ^ 40 * 55719 * 2
def baseEnd_55719 : Nat := 25431669855975762538897

theorem tailTrace_55719 : CollatzResearch.WordTrace tailWord_55719 prefixEnd_55719 25431669855975762538897 := by
  unfold tailWord_55719
  simp only [CollatzResearch.WordTrace]
  refine ⟨2032238885147053892698211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1354825923431369261798807 2032238885147053892698211)
  ·
    refine ⟨3048358327720580839047317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2032238885147053892698211 3048358327720580839047317)
    ·
      refine ⟨142891796611902226830343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3048358327720580839047317 142891796611902226830343)
      ·
        refine ⟨214337694917853340245515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142891796611902226830343 214337694917853340245515)
        ·
          refine ⟨321506542376780010368273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214337694917853340245515 321506542376780010368273)
          ·
            refine ⟨241129906782585007776205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 321506542376780010368273 241129906782585007776205)
            ·
              refine ⟨90423715043469377916077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241129906782585007776205 90423715043469377916077)
              ·
                refine ⟨33908893141301016718529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90423715043469377916077 33908893141301016718529)
                ·
                  refine ⟨25431669855975762538897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33908893141301016718529 25431669855975762538897)
                  ·
                    rfl

theorem cell20_55719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 3, 2].length) (baseStart_55719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55719 prefixEnd_55719 := by exact prefixLift 55719
  have htrace : WordTrace (prefixWord ++ tailWord_55719) baseStart_55719 baseEnd_55719 := by
    simpa [prefixWord, tailWord_55719, baseEnd_55719] using wordTrace_append hprefix tailTrace_55719
  have hstable : (prefixWord ++ tailWord_55719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55719).length < 2 ^ (prefixWord ++ tailWord_55719).sum := by decide
  have hdescent : baseEnd_55719 < baseStart_55719 := by decide
  rcases family_descends (prefixWord ++ tailWord_55719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55722 : List Nat := [3, 1, 6, 1, 2, 1, 6]
def baseStart_55722 : Nat := 118140960795 + 55722 * 2 ^ 59
def prefixEnd_55722 : Nat := 4983230072969 + 3 ^ 40 * 55722 * 2
def baseEnd_55722 : Nat := 2825893237524565048765

theorem tailTrace_55722 : CollatzResearch.WordTrace tailWord_55722 prefixEnd_55722 2825893237524565048765 := by
  unfold tailWord_55722
  simp only [CollatzResearch.WordTrace]
  refine ⟨508087076034046351264355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1354898869424123603371613 508087076034046351264355)
  ·
    refine ⟨762130614051069526896533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 508087076034046351264355 762130614051069526896533)
    ·
      refine ⟨35724872533643884073275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 762130614051069526896533 35724872533643884073275)
      ·
        refine ⟨53587308800465826109913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35724872533643884073275 53587308800465826109913)
        ·
          refine ⟨40190481600349369582435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53587308800465826109913 40190481600349369582435)
          ·
            refine ⟨60285722400524054373653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40190481600349369582435 60285722400524054373653)
            ·
              refine ⟨2825893237524565048765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60285722400524054373653 2825893237524565048765)
              ·
                rfl

theorem cell20_55722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 6].length) (baseStart_55722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55722 prefixEnd_55722 := by exact prefixLift 55722
  have htrace : WordTrace (prefixWord ++ tailWord_55722) baseStart_55722 baseEnd_55722 := by
    simpa [prefixWord, tailWord_55722, baseEnd_55722] using wordTrace_append hprefix tailTrace_55722
  have hstable : (prefixWord ++ tailWord_55722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55722).length < 2 ^ (prefixWord ++ tailWord_55722).sum := by decide
  have hdescent : baseEnd_55722 < baseStart_55722 := by decide
  rcases family_descends (prefixWord ++ tailWord_55722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55732 : List Nat := [2, 5, 2, 2, 1, 1, 3, 2, 2]
def baseStart_55732 : Nat := 118140960795 + 55732 * 2 ^ 59
def prefixEnd_55732 : Nat := 4983230072969 + 3 ^ 40 * 55732 * 2
def baseEnd_55732 : Nat := 25437603410205495105511

theorem tailTrace_55732 : CollatzResearch.WordTrace tailWord_55732 prefixEnd_55732 25437603410205495105511 := by
  unfold tailWord_55732
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016356517049978556460725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1355142022733304741947633 1016356517049978556460725)
  ·
    refine ⟨95283423473435489668193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1016356517049978556460725 95283423473435489668193)
    ·
      refine ⟨71462567605076617251145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95283423473435489668193 71462567605076617251145)
      ·
        refine ⟨53596925703807462938359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71462567605076617251145 53596925703807462938359)
        ·
          refine ⟨80395388555711194407539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53596925703807462938359 80395388555711194407539)
          ·
            refine ⟨120593082833566791611309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80395388555711194407539 120593082833566791611309)
            ·
              refine ⟨45222406062587546854241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120593082833566791611309 45222406062587546854241)
              ·
                refine ⟨33916804546940660140681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45222406062587546854241 33916804546940660140681)
                ·
                  refine ⟨25437603410205495105511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33916804546940660140681 25437603410205495105511)
                  ·
                    rfl

theorem cell20_55732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_55732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55732 prefixEnd_55732 := by exact prefixLift 55732
  have htrace : WordTrace (prefixWord ++ tailWord_55732) baseStart_55732 baseEnd_55732 := by
    simpa [prefixWord, tailWord_55732, baseEnd_55732] using wordTrace_append hprefix tailTrace_55732
  have hstable : (prefixWord ++ tailWord_55732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55732).length < 2 ^ (prefixWord ++ tailWord_55732).sum := by decide
  have hdescent : baseEnd_55732 < baseStart_55732 := by decide
  rcases family_descends (prefixWord ++ tailWord_55732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55740 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_55740 : Nat := 118140960795 + 55740 * 2 ^ 59
def prefixEnd_55740 : Nat := 4983230072969 + 3 ^ 40 * 55740 * 2
def baseEnd_55740 : Nat := 25441254828193022838811

theorem tailTrace_55740 : CollatzResearch.WordTrace tailWord_55740 prefixEnd_55740 25441254828193022838811 := by
  unfold tailWord_55740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016502409035487239606337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1355336545380649652808449 1016502409035487239606337)
  ·
    refine ⟨762376806776615429704753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1016502409035487239606337 762376806776615429704753)
    ·
      refine ⟨571782605082461572278565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 762376806776615429704753 571782605082461572278565)
      ·
        refine ⟨107209238452961544802231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 571782605082461572278565 107209238452961544802231)
        ·
          refine ⟨160813857679442317203347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107209238452961544802231 160813857679442317203347)
          ·
            refine ⟨241220786519163475805021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160813857679442317203347 241220786519163475805021)
            ·
              refine ⟨90457794944686303426883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241220786519163475805021 90457794944686303426883)
              ·
                refine ⟨135686692417029455140325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90457794944686303426883 135686692417029455140325)
                ·
                  refine ⟨25441254828193022838811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135686692417029455140325 25441254828193022838811)
                  ·
                    rfl

theorem cell20_55740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_55740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55740 prefixEnd_55740 := by exact prefixLift 55740
  have htrace : WordTrace (prefixWord ++ tailWord_55740) baseStart_55740 baseEnd_55740 := by
    simpa [prefixWord, tailWord_55740, baseEnd_55740] using wordTrace_append hprefix tailTrace_55740
  have hstable : (prefixWord ++ tailWord_55740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55740).length < 2 ^ (prefixWord ++ tailWord_55740).sum := by decide
  have hdescent : baseEnd_55740 < baseStart_55740 := by decide
  rcases family_descends (prefixWord ++ tailWord_55740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55754 : List Nat := [3, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_55754 : Nat := 118140960795 + 55754 * 2 ^ 59
def prefixEnd_55754 : Nat := 4983230072969 + 3 ^ 40 * 55754 * 2
def baseEnd_55754 : Nat := 25447644809671196372087

theorem tailTrace_55754 : CollatzResearch.WordTrace tailWord_55754 prefixEnd_55754 25447644809671196372087 := by
  unfold tailWord_55754
  simp only [CollatzResearch.WordTrace]
  refine ⟨508378860005063717555579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1355676960013503246814877 508378860005063717555579)
  ·
    refine ⟨762568290007595576333369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 508378860005063717555579 762568290007595576333369)
    ·
      refine ⟨571926217505696682250027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 762568290007595576333369 571926217505696682250027)
      ·
        refine ⟨857889326258545023375041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571926217505696682250027 857889326258545023375041)
        ·
          refine ⟨643416994693908767531281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 857889326258545023375041 643416994693908767531281)
          ·
            refine ⟨482562746020431575648461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643416994693908767531281 482562746020431575648461)
            ·
              refine ⟨180961029757661840868173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482562746020431575648461 180961029757661840868173)
              ·
                refine ⟨67860386159123190325565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180961029757661840868173 67860386159123190325565)
                ·
                  refine ⟨25447644809671196372087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67860386159123190325565 25447644809671196372087)
                  ·
                    rfl

theorem cell20_55754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_55754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55754 prefixEnd_55754 := by exact prefixLift 55754
  have htrace : WordTrace (prefixWord ++ tailWord_55754) baseStart_55754 baseEnd_55754 := by
    simpa [prefixWord, tailWord_55754, baseEnd_55754] using wordTrace_append hprefix tailTrace_55754
  have hstable : (prefixWord ++ tailWord_55754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55754).length < 2 ^ (prefixWord ++ tailWord_55754).sum := by decide
  have hdescent : baseEnd_55754 < baseStart_55754 := by decide
  rcases family_descends (prefixWord ++ tailWord_55754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55792 : List Nat := [2, 1, 1, 1, 3, 3, 4, 2, 3]
def baseStart_55792 : Nat := 118140960795 + 55792 * 2 ^ 59
def prefixEnd_55792 : Nat := 4983230072969 + 3 ^ 40 * 55792 * 2
def baseEnd_55792 : Nat := 25464989045111953105265

theorem tailTrace_55792 : CollatzResearch.WordTrace tailWord_55792 prefixEnd_55792 25464989045111953105265 := by
  unfold tailWord_55792
  simp only [CollatzResearch.WordTrace]
  refine ⟨1017450706941293680052815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1356600942588391573403753 1017450706941293680052815)
  ·
    refine ⟨1526176060411940520079223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1017450706941293680052815 1526176060411940520079223)
    ·
      refine ⟨2289264090617910780118835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1526176060411940520079223 2289264090617910780118835)
      ·
        refine ⟨3433896135926866170178253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2289264090617910780118835 3433896135926866170178253)
        ·
          refine ⟨1287711050972574813816845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3433896135926866170178253 1287711050972574813816845)
          ·
            refine ⟨482891644114715555181317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1287711050972574813816845 482891644114715555181317)
            ·
              refine ⟨90542183271509166596497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 482891644114715555181317 90542183271509166596497)
              ·
                refine ⟨67906637453631874947373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90542183271509166596497 67906637453631874947373)
                ·
                  refine ⟨25464989045111953105265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67906637453631874947373 25464989045111953105265)
                  ·
                    rfl

theorem cell20_55792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_55792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55792 prefixEnd_55792 := by exact prefixLift 55792
  have htrace : WordTrace (prefixWord ++ tailWord_55792) baseStart_55792 baseEnd_55792 := by
    simpa [prefixWord, tailWord_55792, baseEnd_55792] using wordTrace_append hprefix tailTrace_55792
  have hstable : (prefixWord ++ tailWord_55792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55792).length < 2 ^ (prefixWord ++ tailWord_55792).sum := by decide
  have hdescent : baseEnd_55792 < baseStart_55792 := by decide
  rcases family_descends (prefixWord ++ tailWord_55792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55878 : List Nat := [6, 1, 1, 1, 2, 2, 1, 6]
def baseStart_55878 : Nat := 118140960795 + 55878 * 2 ^ 59
def prefixEnd_55878 : Nat := 4983230072969 + 3 ^ 40 * 55878 * 2
def baseEnd_55878 : Nat := 8501413929492625412749

theorem tailTrace_55878 : CollatzResearch.WordTrace tailWord_55878 prefixEnd_55878 8501413929492625412749 := by
  unfold tailWord_55878
  simp only [CollatzResearch.WordTrace]
  refine ⟨63688690361594501491759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1358692061047349365157525 63688690361594501491759)
  ·
    refine ⟨95533035542391752237639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63688690361594501491759 95533035542391752237639)
    ·
      refine ⟨143299553313587628356459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95533035542391752237639 143299553313587628356459)
      ·
        refine ⟨214949329970381442534689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143299553313587628356459 214949329970381442534689)
        ·
          refine ⟨161211997477786081901017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214949329970381442534689 161211997477786081901017)
          ·
            refine ⟨120908998108339561425763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161211997477786081901017 120908998108339561425763)
            ·
              refine ⟨181363497162509342138645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120908998108339561425763 181363497162509342138645)
              ·
                refine ⟨8501413929492625412749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181363497162509342138645 8501413929492625412749)
                ·
                  rfl

theorem cell20_55878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_55878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55878 prefixEnd_55878 := by exact prefixLift 55878
  have htrace : WordTrace (prefixWord ++ tailWord_55878) baseStart_55878 baseEnd_55878 := by
    simpa [prefixWord, tailWord_55878, baseEnd_55878] using wordTrace_append hprefix tailTrace_55878
  have hstable : (prefixWord ++ tailWord_55878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55878).length < 2 ^ (prefixWord ++ tailWord_55878).sum := by decide
  have hdescent : baseEnd_55878 < baseStart_55878 := by decide
  rcases family_descends (prefixWord ++ tailWord_55878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55882 : List Nat := [3, 1, 2, 1, 1, 5, 1, 6]
def baseStart_55882 : Nat := 118140960795 + 55882 * 2 ^ 59
def prefixEnd_55882 : Nat := 4983230072969 + 3 ^ 40 * 55882 * 2
def baseEnd_55882 : Nat := 8502022499157213368299

theorem tailTrace_55882 : CollatzResearch.WordTrace tailWord_55882 prefixEnd_55882 8502022499157213368299 := by
  unfold tailWord_55882
  simp only [CollatzResearch.WordTrace]
  refine ⟨509545995889133182720475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1358789322371021820587933 509545995889133182720475)
  ·
    refine ⟨764318993833699774080713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 509545995889133182720475 764318993833699774080713)
    ·
      refine ⟨573239245375274830560535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 764318993833699774080713 573239245375274830560535)
      ·
        refine ⟨859858868062912245840803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573239245375274830560535 859858868062912245840803)
        ·
          refine ⟨1289788302094368368761205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859858868062912245840803 1289788302094368368761205)
          ·
            refine ⟨120917653321347034571363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1289788302094368368761205 120917653321347034571363)
            ·
              refine ⟨181376479982020551857045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120917653321347034571363 181376479982020551857045)
              ·
                refine ⟨8502022499157213368299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 181376479982020551857045 8502022499157213368299)
                ·
                  rfl

theorem cell20_55882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_55882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55882 prefixEnd_55882 := by exact prefixLift 55882
  have htrace : WordTrace (prefixWord ++ tailWord_55882) baseStart_55882 baseEnd_55882 := by
    simpa [prefixWord, tailWord_55882, baseEnd_55882] using wordTrace_append hprefix tailTrace_55882
  have hstable : (prefixWord ++ tailWord_55882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55882).length < 2 ^ (prefixWord ++ tailWord_55882).sum := by decide
  have hdescent : baseEnd_55882 < baseStart_55882 := by decide
  rcases family_descends (prefixWord ++ tailWord_55882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55889 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 5]
def baseStart_55889 : Nat := 118140960795 + 55889 * 2 ^ 59
def prefixEnd_55889 : Nat := 4983230072969 + 3 ^ 40 * 55889 * 2
def baseEnd_55889 : Nat := 25509262488210726871535

theorem tailTrace_55889 : CollatzResearch.WordTrace tailWord_55889 prefixEnd_55889 25509262488210726871535 := by
  unfold tailWord_55889
  simp only [CollatzResearch.WordTrace]
  refine ⟨2038439294531172926386721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1358959529687448617591147 2038439294531172926386721)
  ·
    refine ⟨1528829470898379694790041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2038439294531172926386721 1528829470898379694790041)
    ·
      refine ⟨1146622103173784771092531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1528829470898379694790041 1146622103173784771092531)
      ·
        refine ⟨1719933154760677156638797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146622103173784771092531 1719933154760677156638797)
        ·
          refine ⟨644974933035253933739549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1719933154760677156638797 644974933035253933739549)
          ·
            refine ⟨241865599888220225152331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 644974933035253933739549 241865599888220225152331)
            ·
              refine ⟨362798399832330337728497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241865599888220225152331 362798399832330337728497)
              ·
                refine ⟨272098799874247753296373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362798399832330337728497 272098799874247753296373)
                ·
                  refine ⟨25509262488210726871535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272098799874247753296373 25509262488210726871535)
                  ·
                    rfl

theorem cell20_55889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_55889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55889 prefixEnd_55889 := by exact prefixLift 55889
  have htrace : WordTrace (prefixWord ++ tailWord_55889) baseStart_55889 baseEnd_55889 := by
    simpa [prefixWord, tailWord_55889, baseEnd_55889] using wordTrace_append hprefix tailTrace_55889
  have hstable : (prefixWord ++ tailWord_55889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55889).length < 2 ^ (prefixWord ++ tailWord_55889).sum := by decide
  have hdescent : baseEnd_55889 < baseStart_55889 := by decide
  rcases family_descends (prefixWord ++ tailWord_55889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55896 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 6]
def baseStart_55896 : Nat := 118140960795 + 55896 * 2 ^ 59
def prefixEnd_55896 : Nat := 4983230072969 + 3 ^ 40 * 55896 * 2
def baseEnd_55896 : Nat := 25512457478949813638173

theorem tailTrace_55896 : CollatzResearch.WordTrace tailWord_55896 prefixEnd_55896 25512457478949813638173 := by
  unfold tailWord_55896
  simp only [CollatzResearch.WordTrace]
  refine ⟨1019347302752906560945771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1359129737003875414594361 1019347302752906560945771)
  ·
    refine ⟨1529020954129359841418657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1019347302752906560945771 1529020954129359841418657)
    ·
      refine ⟨1146765715597019881063993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1529020954129359841418657 1146765715597019881063993)
      ·
        refine ⟨860074286697764910797995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1146765715597019881063993 860074286697764910797995)
        ·
          refine ⟨1290111430046647366196993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860074286697764910797995 1290111430046647366196993)
          ·
            refine ⟨967583572534985524647745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1290111430046647366196993 967583572534985524647745)
            ·
              refine ⟨725687679401239143485809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967583572534985524647745 725687679401239143485809)
              ·
                refine ⟨544265759550929357614357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725687679401239143485809 544265759550929357614357)
                ·
                  refine ⟨25512457478949813638173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 544265759550929357614357 25512457478949813638173)
                  ·
                    rfl

theorem cell20_55896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_55896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55896 prefixEnd_55896 := by exact prefixLift 55896
  have htrace : WordTrace (prefixWord ++ tailWord_55896) baseStart_55896 baseEnd_55896 := by
    simpa [prefixWord, tailWord_55896, baseEnd_55896] using wordTrace_append hprefix tailTrace_55896
  have hstable : (prefixWord ++ tailWord_55896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55896).length < 2 ^ (prefixWord ++ tailWord_55896).sum := by decide
  have hdescent : baseEnd_55896 < baseStart_55896 := by decide
  rcases family_descends (prefixWord ++ tailWord_55896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55909 : List Nat := [1, 3, 1, 3, 5, 1, 1, 1, 4]
def baseStart_55909 : Nat := 118140960795 + 55909 * 2 ^ 59
def prefixEnd_55909 : Nat := 4983230072969 + 3 ^ 40 * 55909 * 2
def baseEnd_55909 : Nat := 25518391033179546204787

theorem tailTrace_55909 : CollatzResearch.WordTrace tailWord_55909 prefixEnd_55909 25518391033179546204787 := by
  unfold tailWord_55909
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039168754458716342114781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1359445836305810894743187 2039168754458716342114781)
  ·
    refine ⟨764688282922018628293043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2039168754458716342114781 764688282922018628293043)
    ·
      refine ⟨1147032424383027942439565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764688282922018628293043 1147032424383027942439565)
      ·
        refine ⟨430137159143635478414837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1147032424383027942439565 430137159143635478414837)
        ·
          refine ⟨40325358669715826101391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 430137159143635478414837 40325358669715826101391)
          ·
            refine ⟨60488038004573739152087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40325358669715826101391 60488038004573739152087)
            ·
              refine ⟨90732057006860608728131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60488038004573739152087 90732057006860608728131)
              ·
                refine ⟨136098085510290913092197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90732057006860608728131 136098085510290913092197)
                ·
                  refine ⟨25518391033179546204787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136098085510290913092197 25518391033179546204787)
                  ·
                    rfl

theorem cell20_55909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 4].length) (baseStart_55909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55909 prefixEnd_55909 := by exact prefixLift 55909
  have htrace : WordTrace (prefixWord ++ tailWord_55909) baseStart_55909 baseEnd_55909 := by
    simpa [prefixWord, tailWord_55909, baseEnd_55909] using wordTrace_append hprefix tailTrace_55909
  have hstable : (prefixWord ++ tailWord_55909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55909).length < 2 ^ (prefixWord ++ tailWord_55909).sum := by decide
  have hdescent : baseEnd_55909 < baseStart_55909 := by decide
  rcases family_descends (prefixWord ++ tailWord_55909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55964 : List Nat := [2, 2, 3, 2, 2, 3, 2, 2, 2]
def baseStart_55964 : Nat := 118140960795 + 55964 * 2 ^ 59
def prefixEnd_55964 : Nat := 4983230072969 + 3 ^ 40 * 55964 * 2
def baseEnd_55964 : Nat := 25543494531843799371229

theorem tailTrace_55964 : CollatzResearch.WordTrace tailWord_55964 prefixEnd_55964 25543494531843799371229 := by
  unfold tailWord_55964
  simp only [CollatzResearch.WordTrace]
  refine ⟨1020587384629730367683473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1360783179506307156911297 1020587384629730367683473)
  ·
    refine ⟨765440538472297775762605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1020587384629730367683473 765440538472297775762605)
    ·
      refine ⟨287040201927111665910977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 765440538472297775762605 287040201927111665910977)
      ·
        refine ⟨215280151445333749433233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 287040201927111665910977 215280151445333749433233)
        ·
          refine ⟨161460113584000312074925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 215280151445333749433233 161460113584000312074925)
          ·
            refine ⟨60547542594000117028097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 161460113584000312074925 60547542594000117028097)
            ·
              refine ⟨45410656945500087771073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60547542594000117028097 45410656945500087771073)
              ·
                refine ⟨34057992709125065828305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45410656945500087771073 34057992709125065828305)
                ·
                  refine ⟨25543494531843799371229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34057992709125065828305 25543494531843799371229)
                  ·
                    rfl

theorem cell20_55964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_55964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55964 prefixEnd_55964 := by exact prefixLift 55964
  have htrace : WordTrace (prefixWord ++ tailWord_55964) baseStart_55964 baseEnd_55964 := by
    simpa [prefixWord, tailWord_55964, baseEnd_55964] using wordTrace_append hprefix tailTrace_55964
  have hstable : (prefixWord ++ tailWord_55964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55964).length < 2 ^ (prefixWord ++ tailWord_55964).sum := by decide
  have hdescent : baseEnd_55964 < baseStart_55964 := by decide
  rcases family_descends (prefixWord ++ tailWord_55964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55965 : List Nat := [1, 4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_55965 : Nat := 118140960795 + 55965 * 2 ^ 59
def prefixEnd_55965 : Nat := 4983230072969 + 3 ^ 40 * 55965 * 2
def baseEnd_55965 : Nat := 25543950959092240337891

theorem tailTrace_55965 : CollatzResearch.WordTrace tailWord_55965 prefixEnd_55965 25543950959092240337891 := by
  unfold tailWord_55965
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041211242255837906153349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1360807494837225270768899 2041211242255837906153349)
  ·
    refine ⟨382727107922969607403753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2041211242255837906153349 382727107922969607403753)
    ·
      refine ⟨287045330942227205552815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 382727107922969607403753 287045330942227205552815)
      ·
        refine ⟨430567996413340808329223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287045330942227205552815 430567996413340808329223)
        ·
          refine ⟨645851994620011212493835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430567996413340808329223 645851994620011212493835)
          ·
            refine ⟨968777991930016818740753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645851994620011212493835 968777991930016818740753)
            ·
              refine ⟨726583493947512614055565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968777991930016818740753 726583493947512614055565)
              ·
                refine ⟨272468810230317230270837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 726583493947512614055565 272468810230317230270837)
                ·
                  refine ⟨25543950959092240337891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272468810230317230270837 25543950959092240337891)
                  ·
                    rfl

theorem cell20_55965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_55965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55965 prefixEnd_55965 := by exact prefixLift 55965
  have htrace : WordTrace (prefixWord ++ tailWord_55965) baseStart_55965 baseEnd_55965 := by
    simpa [prefixWord, tailWord_55965, baseEnd_55965] using wordTrace_append hprefix tailTrace_55965
  have hstable : (prefixWord ++ tailWord_55965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55965).length < 2 ^ (prefixWord ++ tailWord_55965).sum := by decide
  have hdescent : baseEnd_55965 < baseStart_55965 := by decide
  rcases family_descends (prefixWord ++ tailWord_55965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_55989 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 6]
def baseStart_55989 : Nat := 118140960795 + 55989 * 2 ^ 59
def prefixEnd_55989 : Nat := 4983230072969 + 3 ^ 40 * 55989 * 2
def baseEnd_55989 : Nat := 25554905213054823537793

theorem tailTrace_55989 : CollatzResearch.WordTrace tailWord_55989 prefixEnd_55989 25554905213054823537793 := by
  unfold tailWord_55989
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042086594168890005027021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1361391062779260003351347 2042086594168890005027021)
  ·
    refine ⟨765782472813333751885133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2042086594168890005027021 765782472813333751885133)
    ·
      refine ⟨287168427305000156956925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 765782472813333751885133 287168427305000156956925)
      ·
        refine ⟨107688160239375058858847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287168427305000156956925 107688160239375058858847)
        ·
          refine ⟨161532240359062588288271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107688160239375058858847 161532240359062588288271)
          ·
            refine ⟨242298360538593882432407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161532240359062588288271 242298360538593882432407)
            ·
              refine ⟨363447540807890823648611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242298360538593882432407 363447540807890823648611)
              ·
                refine ⟨545171311211836235472917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363447540807890823648611 545171311211836235472917)
                ·
                  refine ⟨25554905213054823537793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 545171311211836235472917 25554905213054823537793)
                  ·
                    rfl

theorem cell20_55989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_55989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_55989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_55989 prefixEnd_55989 := by exact prefixLift 55989
  have htrace : WordTrace (prefixWord ++ tailWord_55989) baseStart_55989 baseEnd_55989 := by
    simpa [prefixWord, tailWord_55989, baseEnd_55989] using wordTrace_append hprefix tailTrace_55989
  have hstable : (prefixWord ++ tailWord_55989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_55989).length < 2 ^ (prefixWord ++ tailWord_55989).sum := by decide
  have hdescent : baseEnd_55989 < baseStart_55989 := by decide
  rcases family_descends (prefixWord ++ tailWord_55989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56017 : List Nat := [1, 2, 2, 1, 2, 3, 9]
def baseStart_56017 : Nat := 118140960795 + 56017 * 2 ^ 59
def prefixEnd_56017 : Nat := 4983230072969 + 3 ^ 40 * 56017 * 2
def baseEnd_56017 : Nat := 2840853908445685622705

theorem tailTrace_56017 : CollatzResearch.WordTrace tailWord_56017 prefixEnd_56017 2840853908445685622705 := by
  unfold tailWord_56017
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043107838067450787046305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1362071892044967191364203 2043107838067450787046305)
  ·
    refine ⟨1532330878550588090284729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2043107838067450787046305 1532330878550588090284729)
    ·
      refine ⟨1149248158912941067713547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1532330878550588090284729 1149248158912941067713547)
      ·
        refine ⟨1723872238369411601570321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1149248158912941067713547 1723872238369411601570321)
        ·
          refine ⟨1292904178777058701177741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1723872238369411601570321 1292904178777058701177741)
          ·
            refine ⟨484839067041397012941653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1292904178777058701177741 484839067041397012941653)
            ·
              refine ⟨2840853908445685622705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 484839067041397012941653 2840853908445685622705)
              ·
                rfl

theorem cell20_56017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 9].length) (baseStart_56017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56017 prefixEnd_56017 := by exact prefixLift 56017
  have htrace : WordTrace (prefixWord ++ tailWord_56017) baseStart_56017 baseEnd_56017 := by
    simpa [prefixWord, tailWord_56017, baseEnd_56017] using wordTrace_append hprefix tailTrace_56017
  have hstable : (prefixWord ++ tailWord_56017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56017).length < 2 ^ (prefixWord ++ tailWord_56017).sum := by decide
  have hdescent : baseEnd_56017 < baseStart_56017 := by decide
  rcases family_descends (prefixWord ++ tailWord_56017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56037 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 3]
def baseStart_56037 : Nat := 118140960795 + 56037 * 2 ^ 59
def prefixEnd_56037 : Nat := 4983230072969 + 3 ^ 40 * 56037 * 2
def baseEnd_56037 : Nat := 25576813720979989937597

theorem tailTrace_56037 : CollatzResearch.WordTrace tailWord_56037 prefixEnd_56037 25576813720979989937597 := by
  unfold tailWord_56037
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043837297994994202774365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1362558198663329468516243 2043837297994994202774365)
  ·
    refine ⟨766438986748122826040387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2043837297994994202774365 766438986748122826040387)
    ·
      refine ⟨1149658480122184239060581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 766438986748122826040387 1149658480122184239060581)
      ·
        refine ⟨215560965022909544823859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1149658480122184239060581 215560965022909544823859)
        ·
          refine ⟨323341447534364317235789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215560965022909544823859 323341447534364317235789)
          ·
            refine ⟨121253042825386618963421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323341447534364317235789 121253042825386618963421)
            ·
              refine ⟨45469891059519982111283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121253042825386618963421 45469891059519982111283)
              ·
                refine ⟨68204836589279973166925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45469891059519982111283 68204836589279973166925)
                ·
                  refine ⟨25576813720979989937597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68204836589279973166925 25576813720979989937597)
                  ·
                    rfl

theorem cell20_56037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_56037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56037 prefixEnd_56037 := by exact prefixLift 56037
  have htrace : WordTrace (prefixWord ++ tailWord_56037) baseStart_56037 baseEnd_56037 := by
    simpa [prefixWord, tailWord_56037, baseEnd_56037] using wordTrace_append hprefix tailTrace_56037
  have hstable : (prefixWord ++ tailWord_56037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56037).length < 2 ^ (prefixWord ++ tailWord_56037).sum := by decide
  have hdescent : baseEnd_56037 < baseStart_56037 := by decide
  rcases family_descends (prefixWord ++ tailWord_56037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56041 : List Nat := [1, 2, 1, 1, 1, 2, 4, 5, 3]
def baseStart_56041 : Nat := 118140960795 + 56041 * 2 ^ 59
def prefixEnd_56041 : Nat := 4983230072969 + 3 ^ 40 * 56041 * 2
def baseEnd_56041 : Nat := 25578639429973753804247

theorem tailTrace_56041 : CollatzResearch.WordTrace tailWord_56041 prefixEnd_56041 25578639429973753804247 := by
  unfold tailWord_56041
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043983189980502885919977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1362655459987001923946651 2043983189980502885919977)
  ·
    refine ⟨1532987392485377164439983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2043983189980502885919977 1532987392485377164439983)
    ·
      refine ⟨2299481088728065746659975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1532987392485377164439983 2299481088728065746659975)
      ·
        refine ⟨3449221633092098619989963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299481088728065746659975 3449221633092098619989963)
        ·
          refine ⟨5173832449638147929984945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3449221633092098619989963 5173832449638147929984945)
          ·
            refine ⟨3880374337228610947488709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5173832449638147929984945 3880374337228610947488709)
            ·
              refine ⟨727570188230364552654133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3880374337228610947488709 727570188230364552654133)
              ·
                refine ⟨68209705146596676811325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 727570188230364552654133 68209705146596676811325)
                ·
                  refine ⟨25578639429973753804247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68209705146596676811325 25578639429973753804247)
                  ·
                    rfl

theorem cell20_56041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5, 3].length) (baseStart_56041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56041 prefixEnd_56041 := by exact prefixLift 56041
  have htrace : WordTrace (prefixWord ++ tailWord_56041) baseStart_56041 baseEnd_56041 := by
    simpa [prefixWord, tailWord_56041, baseEnd_56041] using wordTrace_append hprefix tailTrace_56041
  have hstable : (prefixWord ++ tailWord_56041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56041).length < 2 ^ (prefixWord ++ tailWord_56041).sum := by decide
  have hdescent : baseEnd_56041 < baseStart_56041 := by decide
  rcases family_descends (prefixWord ++ tailWord_56041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56048 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 4]
def baseStart_56048 : Nat := 118140960795 + 56048 * 2 ^ 59
def prefixEnd_56048 : Nat := 4983230072969 + 3 ^ 40 * 56048 * 2
def baseEnd_56048 : Nat := 25581834420712840570885

theorem tailTrace_56048 : CollatzResearch.WordTrace tailWord_56048 prefixEnd_56048 25581834420712840570885 := by
  unfold tailWord_56048
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022119250477571540712399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1362825667303428720949865 1022119250477571540712399)
  ·
    refine ⟨1533178875716357311068599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1022119250477571540712399 1533178875716357311068599)
    ·
      refine ⟨2299768313574535966602899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533178875716357311068599 2299768313574535966602899)
      ·
        refine ⟨3449652470361803949904349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299768313574535966602899 3449652470361803949904349)
        ·
          refine ⟨1293619676385676481214131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3449652470361803949904349 1293619676385676481214131)
          ·
            refine ⟨1940429514578514721821197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1293619676385676481214131 1940429514578514721821197)
            ·
              refine ⟨727661067966943020682949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1940429514578514721821197 727661067966943020682949)
              ·
                refine ⟨136436450243801816378053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 727661067966943020682949 136436450243801816378053)
                ·
                  refine ⟨25581834420712840570885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136436450243801816378053 25581834420712840570885)
                  ·
                    rfl

theorem cell20_56048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_56048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56048 prefixEnd_56048 := by exact prefixLift 56048
  have htrace : WordTrace (prefixWord ++ tailWord_56048) baseStart_56048 baseEnd_56048 := by
    simpa [prefixWord, tailWord_56048, baseEnd_56048] using wordTrace_append hprefix tailTrace_56048
  have hstable : (prefixWord ++ tailWord_56048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56048).length < 2 ^ (prefixWord ++ tailWord_56048).sum := by decide
  have hdescent : baseEnd_56048 < baseStart_56048 := by decide
  rcases family_descends (prefixWord ++ tailWord_56048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56072 : List Nat := [2, 1, 3, 2, 2, 4, 6]
def baseStart_56072 : Nat := 118140960795 + 56072 * 2 ^ 59
def prefixEnd_56072 : Nat := 4983230072969 + 3 ^ 40 * 56072 * 2
def baseEnd_56072 : Nat := 2843643186075047085643

theorem tailTrace_56072 : CollatzResearch.WordTrace tailWord_56072 prefixEnd_56072 2843643186075047085643 := by
  unfold tailWord_56072
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022556926434097590149235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1363409235245463453532313 1022556926434097590149235)
  ·
    refine ⟨1533835389651146385223853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1022556926434097590149235 1533835389651146385223853)
    ·
      refine ⟨575188271119179894458945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1533835389651146385223853 575188271119179894458945)
      ·
        refine ⟨431391203339384920844209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575188271119179894458945 431391203339384920844209)
        ·
          refine ⟨323543402504538690633157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431391203339384920844209 323543402504538690633157)
          ·
            refine ⟨60664387969601004493717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 323543402504538690633157 60664387969601004493717)
            ·
              refine ⟨2843643186075047085643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60664387969601004493717 2843643186075047085643)
              ·
                rfl

theorem cell20_56072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 6].length) (baseStart_56072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56072 prefixEnd_56072 := by exact prefixLift 56072
  have htrace : WordTrace (prefixWord ++ tailWord_56072) baseStart_56072 baseEnd_56072 := by
    simpa [prefixWord, tailWord_56072, baseEnd_56072] using wordTrace_append hprefix tailTrace_56072
  have hstable : (prefixWord ++ tailWord_56072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56072).length < 2 ^ (prefixWord ++ tailWord_56072).sum := by decide
  have hdescent : baseEnd_56072 < baseStart_56072 := by decide
  rcases family_descends (prefixWord ++ tailWord_56072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56079 : List Nat := [1, 1, 2, 1, 1, 1, 6, 4, 3]
def baseStart_56079 : Nat := 118140960795 + 56079 * 2 ^ 59
def prefixEnd_56079 : Nat := 4983230072969 + 3 ^ 40 * 56079 * 2
def baseEnd_56079 : Nat := 25595983665414510537425

theorem tailTrace_56079 : CollatzResearch.WordTrace tailWord_56079 prefixEnd_56079 25595983665414510537425 := by
  unfold tailWord_56079
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045369163842835375803291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1363579442561890250535527 2045369163842835375803291)
  ·
    refine ⟨3068053745764253063704937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2045369163842835375803291 3068053745764253063704937)
    ·
      refine ⟨2301040309323189797778703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3068053745764253063704937 2301040309323189797778703)
      ·
        refine ⟨3451560463984784696668055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2301040309323189797778703 3451560463984784696668055)
        ·
          refine ⟨5177340695977177045002083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3451560463984784696668055 5177340695977177045002083)
          ·
            refine ⟨7766011043965765567503125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5177340695977177045002083 7766011043965765567503125)
            ·
              refine ⟨364031767685895260976709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7766011043965765567503125 364031767685895260976709)
              ·
                refine ⟨68255956441105361433133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364031767685895260976709 68255956441105361433133)
                ·
                  refine ⟨25595983665414510537425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68255956441105361433133 25595983665414510537425)
                  ·
                    rfl

theorem cell20_56079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 4, 3].length) (baseStart_56079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56079 prefixEnd_56079 := by exact prefixLift 56079
  have htrace : WordTrace (prefixWord ++ tailWord_56079) baseStart_56079 baseEnd_56079 := by
    simpa [prefixWord, tailWord_56079, baseEnd_56079] using wordTrace_append hprefix tailTrace_56079
  have hstable : (prefixWord ++ tailWord_56079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56079).length < 2 ^ (prefixWord ++ tailWord_56079).sum := by decide
  have hdescent : baseEnd_56079 < baseStart_56079 := by decide
  rcases family_descends (prefixWord ++ tailWord_56079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56096 : List Nat := [2, 1, 1, 5, 1, 3, 1, 3, 3]
def baseStart_56096 : Nat := 118140960795 + 56096 * 2 ^ 59
def prefixEnd_56096 : Nat := 4983230072969 + 3 ^ 40 * 56096 * 2
def baseEnd_56096 : Nat := 25603742928638006970689

theorem tailTrace_56096 : CollatzResearch.WordTrace tailWord_56096 prefixEnd_56096 25603742928638006970689 := by
  unfold tailWord_56096
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022994602390623639586071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1363992803187498186114761 1022994602390623639586071)
  ·
    refine ⟨1534491903585935459379107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1022994602390623639586071 1534491903585935459379107)
    ·
      refine ⟨2301737855378903189068661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1534491903585935459379107 2301737855378903189068661)
      ·
        refine ⟨215787923941772173975187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2301737855378903189068661 215787923941772173975187)
        ·
          refine ⟨323681885912658260962781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215787923941772173975187 323681885912658260962781)
          ·
            refine ⟨121380707217246847861043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 323681885912658260962781 121380707217246847861043)
            ·
              refine ⟨182071060825870271791565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121380707217246847861043 182071060825870271791565)
              ·
                refine ⟨68276647809701351921837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182071060825870271791565 68276647809701351921837)
                ·
                  refine ⟨25603742928638006970689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68276647809701351921837 25603742928638006970689)
                  ·
                    rfl

theorem cell20_56096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_56096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56096 prefixEnd_56096 := by exact prefixLift 56096
  have htrace : WordTrace (prefixWord ++ tailWord_56096) baseStart_56096 baseEnd_56096 := by
    simpa [prefixWord, tailWord_56096, baseEnd_56096] using wordTrace_append hprefix tailTrace_56096
  have hstable : (prefixWord ++ tailWord_56096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56096).length < 2 ^ (prefixWord ++ tailWord_56096).sum := by decide
  have hdescent : baseEnd_56096 < baseStart_56096 := by decide
  rcases family_descends (prefixWord ++ tailWord_56096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56137 : List Nat := [1, 2, 1, 1, 2, 7, 2, 2, 2]
def baseStart_56137 : Nat := 118140960795 + 56137 * 2 ^ 59
def prefixEnd_56137 : Nat := 4983230072969 + 3 ^ 40 * 56137 * 2
def baseEnd_56137 : Nat := 25622456445824086603855

theorem tailTrace_56137 : CollatzResearch.WordTrace tailWord_56137 prefixEnd_56137 25622456445824086603855 := by
  unfold tailWord_56137
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047484597632711281414665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1364989731755140854276443 2047484597632711281414665)
  ·
    refine ⟨1535613448224533461060999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2047484597632711281414665 1535613448224533461060999)
    ·
      refine ⟨2303420172336800191591499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1535613448224533461060999 2303420172336800191591499)
      ·
        refine ⟨3455130258505200287387249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2303420172336800191591499 3455130258505200287387249)
        ·
          refine ⟨2591347693878900215540437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3455130258505200287387249 2591347693878900215540437)
          ·
            refine ⟨60734711575286723801729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 2591347693878900215540437 60734711575286723801729)
            ·
              refine ⟨45551033681465042851297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60734711575286723801729 45551033681465042851297)
              ·
                refine ⟨34163275261098782138473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45551033681465042851297 34163275261098782138473)
                ·
                  refine ⟨25622456445824086603855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34163275261098782138473 25622456445824086603855)
                  ·
                    rfl

theorem cell20_56137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 2, 2].length) (baseStart_56137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56137 prefixEnd_56137 := by exact prefixLift 56137
  have htrace : WordTrace (prefixWord ++ tailWord_56137) baseStart_56137 baseEnd_56137 := by
    simpa [prefixWord, tailWord_56137, baseEnd_56137] using wordTrace_append hprefix tailTrace_56137
  have hstable : (prefixWord ++ tailWord_56137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56137).length < 2 ^ (prefixWord ++ tailWord_56137).sum := by decide
  have hdescent : baseEnd_56137 < baseStart_56137 := by decide
  rcases family_descends (prefixWord ++ tailWord_56137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56179 : List Nat := [1, 1, 1, 2, 2, 1, 5, 5, 2]
def baseStart_56179 : Nat := 118140960795 + 56179 * 2 ^ 59
def prefixEnd_56179 : Nat := 4983230072969 + 3 ^ 40 * 56179 * 2
def baseEnd_56179 : Nat := 25641626390258607203683

theorem tailTrace_56179 : CollatzResearch.WordTrace tailWord_56179 prefixEnd_56179 25641626390258607203683 := by
  unfold tailWord_56179
  simp only [CollatzResearch.WordTrace]
  refine ⟨2049016463480552454443591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1366010975653701636295727 2049016463480552454443591)
  ·
    refine ⟨3073524695220828681665387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2049016463480552454443591 3073524695220828681665387)
    ·
      refine ⟨4610287042831243022498081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3073524695220828681665387 4610287042831243022498081)
      ·
        refine ⟨3457715282123432266873561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4610287042831243022498081 3457715282123432266873561)
        ·
          refine ⟨2593286461592574200155171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3457715282123432266873561 2593286461592574200155171)
          ·
            refine ⟨3889929692388861300232757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2593286461592574200155171 3889929692388861300232757)
            ·
              refine ⟨364680908661455746896821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3889929692388861300232757 364680908661455746896821)
              ·
                refine ⟨34188835187011476271577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 364680908661455746896821 34188835187011476271577)
                ·
                  refine ⟨25641626390258607203683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34188835187011476271577 25641626390258607203683)
                  ·
                    rfl

theorem cell20_56179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 5, 2].length) (baseStart_56179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56179 prefixEnd_56179 := by exact prefixLift 56179
  have htrace : WordTrace (prefixWord ++ tailWord_56179) baseStart_56179 baseEnd_56179 := by
    simpa [prefixWord, tailWord_56179, baseEnd_56179] using wordTrace_append hprefix tailTrace_56179
  have hstable : (prefixWord ++ tailWord_56179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56179).length < 2 ^ (prefixWord ++ tailWord_56179).sum := by decide
  have hdescent : baseEnd_56179 < baseStart_56179 := by decide
  rcases family_descends (prefixWord ++ tailWord_56179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56220 : List Nat := [2, 2, 3, 3, 2, 2, 2, 4]
def baseStart_56220 : Nat := 118140960795 + 56220 * 2 ^ 59
def prefixEnd_56220 : Nat := 4983230072969 + 3 ^ 40 * 56220 * 2
def baseEnd_56220 : Nat := 8553446635814895612283

theorem tailTrace_56220 : CollatzResearch.WordTrace tailWord_56220 prefixEnd_56220 8553446635814895612283 := by
  unfold tailWord_56220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025255928166008228343057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1367007904221344304457409 1025255928166008228343057)
  ·
    refine ⟨768941946124506171257293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1025255928166008228343057 768941946124506171257293)
    ·
      refine ⟨288353229796689814221485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 768941946124506171257293 288353229796689814221485)
      ·
        refine ⟨108132461173758680333057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288353229796689814221485 108132461173758680333057)
        ·
          refine ⟨81099345880319010249793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108132461173758680333057 81099345880319010249793)
          ·
            refine ⟨60824509410239257687345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81099345880319010249793 60824509410239257687345)
            ·
              refine ⟨45618382057679443265509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60824509410239257687345 45618382057679443265509)
              ·
                refine ⟨8553446635814895612283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45618382057679443265509 8553446635814895612283)
                ·
                  rfl

theorem cell20_56220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_56220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56220 prefixEnd_56220 := by exact prefixLift 56220
  have htrace : WordTrace (prefixWord ++ tailWord_56220) baseStart_56220 baseEnd_56220 := by
    simpa [prefixWord, tailWord_56220, baseEnd_56220] using wordTrace_append hprefix tailTrace_56220
  have hstable : (prefixWord ++ tailWord_56220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56220).length < 2 ^ (prefixWord ++ tailWord_56220).sum := by decide
  have hdescent : baseEnd_56220 < baseStart_56220 := by decide
  rcases family_descends (prefixWord ++ tailWord_56220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56224 : List Nat := [2, 1, 1, 4, 1, 1, 6, 4]
def baseStart_56224 : Nat := 118140960795 + 56224 * 2 ^ 59
def prefixEnd_56224 : Nat := 4983230072969 + 3 ^ 40 * 56224 * 2
def baseEnd_56224 : Nat := 8554055205479483567833

theorem tailTrace_56224 : CollatzResearch.WordTrace tailWord_56224 prefixEnd_56224 8554055205479483567833 := by
  unfold tailWord_56224
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025328874158762569915863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1367105165545016759887817 1025328874158762569915863)
  ·
    refine ⟨1537993311238143854873795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1025328874158762569915863 1537993311238143854873795)
    ·
      refine ⟨2306989966857215782310693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1537993311238143854873795 2306989966857215782310693)
      ·
        refine ⟨432560618785727959183255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2306989966857215782310693 432560618785727959183255)
        ·
          refine ⟨648840928178591938774883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432560618785727959183255 648840928178591938774883)
          ·
            refine ⟨973261392267887908162325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648840928178591938774883 973261392267887908162325)
            ·
              refine ⟨45621627762557245695109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 973261392267887908162325 45621627762557245695109)
              ·
                refine ⟨8554055205479483567833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45621627762557245695109 8554055205479483567833)
                ·
                  rfl

theorem cell20_56224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_56224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56224 prefixEnd_56224 := by exact prefixLift 56224
  have htrace : WordTrace (prefixWord ++ tailWord_56224) baseStart_56224 baseEnd_56224 := by
    simpa [prefixWord, tailWord_56224, baseEnd_56224] using wordTrace_append hprefix tailTrace_56224
  have hstable : (prefixWord ++ tailWord_56224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56224).length < 2 ^ (prefixWord ++ tailWord_56224).sum := by decide
  have hdescent : baseEnd_56224 < baseStart_56224 := by decide
  rcases family_descends (prefixWord ++ tailWord_56224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56241 : List Nat := [1, 2, 2, 4, 4, 1, 6]
def baseStart_56241 : Nat := 118140960795 + 56241 * 2 ^ 59
def prefixEnd_56241 : Nat := 4983230072969 + 3 ^ 40 * 56241 * 2
def baseEnd_56241 : Nat := 2852213875517994126307

theorem tailTrace_56241 : CollatzResearch.WordTrace tailWord_56241 prefixEnd_56241 2852213875517994126307 := by
  unfold tailWord_56241
  simp only [CollatzResearch.WordTrace]
  refine ⟨2051277789255937043200577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1367518526170624695467051 2051277789255937043200577)
  ·
    refine ⟨1538458341941952782400433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2051277789255937043200577 1538458341941952782400433)
    ·
      refine ⟨1153843756456464586800325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1538458341941952782400433 1153843756456464586800325)
      ·
        refine ⟨216345704335587110025061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1153843756456464586800325 216345704335587110025061)
        ·
          refine ⟨40564819562922583129699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216345704335587110025061 40564819562922583129699)
          ·
            refine ⟨60847229344383874694549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40564819562922583129699 60847229344383874694549)
            ·
              refine ⟨2852213875517994126307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60847229344383874694549 2852213875517994126307)
              ·
                rfl

theorem cell20_56241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 6].length) (baseStart_56241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56241 prefixEnd_56241 := by exact prefixLift 56241
  have htrace : WordTrace (prefixWord ++ tailWord_56241) baseStart_56241 baseEnd_56241 := by
    simpa [prefixWord, tailWord_56241, baseEnd_56241] using wordTrace_append hprefix tailTrace_56241
  have hstable : (prefixWord ++ tailWord_56241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56241).length < 2 ^ (prefixWord ++ tailWord_56241).sum := by decide
  have hdescent : baseEnd_56241 < baseStart_56241 := by decide
  rcases family_descends (prefixWord ++ tailWord_56241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56362 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 5]
def baseStart_56362 : Nat := 118140960795 + 56362 * 2 ^ 59
def prefixEnd_56362 : Nat := 4983230072969 + 3 ^ 40 * 56362 * 2
def baseEnd_56362 : Nat := 25725152576723304102935

theorem tailTrace_56362 : CollatzResearch.WordTrace tailWord_56362 prefixEnd_56362 25725152576723304102935 := by
  unfold tailWord_56362
  simp only [CollatzResearch.WordTrace]
  refine ⟨513922755454393677088835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1370460681211716472236893 513922755454393677088835)
  ·
    refine ⟨770884133181590515633253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 513922755454393677088835 770884133181590515633253)
    ·
      refine ⟨144540774971548221681235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 770884133181590515633253 144540774971548221681235)
      ·
        refine ⟨216811162457322332521853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144540774971548221681235 216811162457322332521853)
        ·
          refine ⟨81304185921495874695695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216811162457322332521853 81304185921495874695695)
          ·
            refine ⟨121956278882243812043543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81304185921495874695695 121956278882243812043543)
            ·
              refine ⟨182934418323365718065315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121956278882243812043543 182934418323365718065315)
              ·
                refine ⟨274401627485048577097973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182934418323365718065315 274401627485048577097973)
                ·
                  refine ⟨25725152576723304102935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274401627485048577097973 25725152576723304102935)
                  ·
                    rfl

theorem cell20_56362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_56362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56362 prefixEnd_56362 := by exact prefixLift 56362
  have htrace : WordTrace (prefixWord ++ tailWord_56362) baseStart_56362 baseEnd_56362 := by
    simpa [prefixWord, tailWord_56362, baseEnd_56362] using wordTrace_append hprefix tailTrace_56362
  have hstable : (prefixWord ++ tailWord_56362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56362).length < 2 ^ (prefixWord ++ tailWord_56362).sum := by decide
  have hdescent : baseEnd_56362 < baseStart_56362 := by decide
  rcases family_descends (prefixWord ++ tailWord_56362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56369 : List Nat := [1, 2, 2, 3, 1, 2, 1, 6, 2]
def baseStart_56369 : Nat := 118140960795 + 56369 * 2 ^ 59
def prefixEnd_56369 : Nat := 4983230072969 + 3 ^ 40 * 56369 * 2
def baseEnd_56369 : Nat := 25728347567462390869573

theorem tailTrace_56369 : CollatzResearch.WordTrace tailWord_56369 prefixEnd_56369 25728347567462390869573 := by
  unfold tailWord_56369
  simp only [CollatzResearch.WordTrace]
  refine ⟨2055946332792214903860161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1370630888528143269240107 2055946332792214903860161)
  ·
    refine ⟨1541959749594161177895121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2055946332792214903860161 1541959749594161177895121)
    ·
      refine ⟨1156469812195620883421341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1541959749594161177895121 1156469812195620883421341)
      ·
        refine ⟨433676179573357831283003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1156469812195620883421341 433676179573357831283003)
        ·
          refine ⟨650514269360036746924505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433676179573357831283003 650514269360036746924505)
          ·
            refine ⟨487885702020027560193379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650514269360036746924505 487885702020027560193379)
            ·
              refine ⟨731828553030041340290069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487885702020027560193379 731828553030041340290069)
              ·
                refine ⟨34304463423283187826097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 731828553030041340290069 34304463423283187826097)
                ·
                  refine ⟨25728347567462390869573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34304463423283187826097 25728347567462390869573)
                  ·
                    rfl

theorem cell20_56369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 6, 2].length) (baseStart_56369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56369 prefixEnd_56369 := by exact prefixLift 56369
  have htrace : WordTrace (prefixWord ++ tailWord_56369) baseStart_56369 baseEnd_56369 := by
    simpa [prefixWord, tailWord_56369, baseEnd_56369] using wordTrace_append hprefix tailTrace_56369
  have hstable : (prefixWord ++ tailWord_56369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56369).length < 2 ^ (prefixWord ++ tailWord_56369).sum := by decide
  have hdescent : baseEnd_56369 < baseStart_56369 := by decide
  rcases family_descends (prefixWord ++ tailWord_56369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56421 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 3]
def baseStart_56421 : Nat := 118140960795 + 56421 * 2 ^ 59
def prefixEnd_56421 : Nat := 4983230072969 + 3 ^ 40 * 56421 * 2
def baseEnd_56421 : Nat := 25752081784381321136027

theorem tailTrace_56421 : CollatzResearch.WordTrace tailWord_56421 prefixEnd_56421 25752081784381321136027 := by
  unfold tailWord_56421
  simp only [CollatzResearch.WordTrace]
  refine ⟨2057842928603827784753117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1371895285735885189835411 2057842928603827784753117)
  ·
    refine ⟨771691098226435419282419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2057842928603827784753117 771691098226435419282419)
    ·
      refine ⟨1157536647339653128923629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771691098226435419282419 1157536647339653128923629)
      ·
        refine ⟨434076242752369923346361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1157536647339653128923629 434076242752369923346361)
        ·
          refine ⟨325557182064277442509771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434076242752369923346361 325557182064277442509771)
          ·
            refine ⟨488335773096416163764657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325557182064277442509771 488335773096416163764657)
            ·
              refine ⟨366251829822312122823493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488335773096416163764657 366251829822312122823493)
              ·
                refine ⟨68672218091683523029405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366251829822312122823493 68672218091683523029405)
                ·
                  refine ⟨25752081784381321136027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68672218091683523029405 25752081784381321136027)
                  ·
                    rfl

theorem cell20_56421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_56421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56421 prefixEnd_56421 := by exact prefixLift 56421
  have htrace : WordTrace (prefixWord ++ tailWord_56421) baseStart_56421 baseEnd_56421 := by
    simpa [prefixWord, tailWord_56421, baseEnd_56421] using wordTrace_append hprefix tailTrace_56421
  have hstable : (prefixWord ++ tailWord_56421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56421).length < 2 ^ (prefixWord ++ tailWord_56421).sum := by decide
  have hdescent : baseEnd_56421 < baseStart_56421 := by decide
  rcases family_descends (prefixWord ++ tailWord_56421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56438 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_56438 : Nat := 118140960795 + 56438 * 2 ^ 59
def prefixEnd_56438 : Nat := 4983230072969 + 3 ^ 40 * 56438 * 2
def baseEnd_56438 : Nat := 25759841047604817569291

theorem tailTrace_56438 : CollatzResearch.WordTrace tailWord_56438 prefixEnd_56438 25759841047604817569291 := by
  unfold tailWord_56438
  simp only [CollatzResearch.WordTrace]
  refine ⟨128653935596389980507623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1372308646361493125414645 128653935596389980507623)
  ·
    refine ⟨192980903394584970761435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128653935596389980507623 192980903394584970761435)
    ·
      refine ⟨289471355091877456142153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192980903394584970761435 289471355091877456142153)
      ·
        refine ⟨217103516318908092106615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289471355091877456142153 217103516318908092106615)
        ·
          refine ⟨325655274478362138159923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217103516318908092106615 325655274478362138159923)
          ·
            refine ⟨488482911717543207239885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325655274478362138159923 488482911717543207239885)
            ·
              refine ⟨183181091894078702714957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488482911717543207239885 183181091894078702714957)
              ·
                refine ⟨68692909460279513518109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183181091894078702714957 68692909460279513518109)
                ·
                  refine ⟨25759841047604817569291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68692909460279513518109 25759841047604817569291)
                  ·
                    rfl

theorem cell20_56438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_56438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56438 prefixEnd_56438 := by exact prefixLift 56438
  have htrace : WordTrace (prefixWord ++ tailWord_56438) baseStart_56438 baseEnd_56438 := by
    simpa [prefixWord, tailWord_56438, baseEnd_56438] using wordTrace_append hprefix tailTrace_56438
  have hstable : (prefixWord ++ tailWord_56438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56438).length < 2 ^ (prefixWord ++ tailWord_56438).sum := by decide
  have hdescent : baseEnd_56438 < baseStart_56438 := by decide
  rcases family_descends (prefixWord ++ tailWord_56438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56476 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 3]
def baseStart_56476 : Nat := 118140960795 + 56476 * 2 ^ 59
def prefixEnd_56476 : Nat := 4983230072969 + 3 ^ 40 * 56476 * 2
def baseEnd_56476 : Nat := 25777185283045574302469

theorem tailTrace_56476 : CollatzResearch.WordTrace tailWord_56476 prefixEnd_56476 25777185283045574302469 := by
  unfold tailWord_56476
  simp only [CollatzResearch.WordTrace]
  refine ⟨1029924471702286089002641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1373232628936381452003521 1029924471702286089002641)
  ·
    refine ⟨772443353776714566751981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1029924471702286089002641 772443353776714566751981)
    ·
      refine ⟨289666257666267962531993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 772443353776714566751981 289666257666267962531993)
      ·
        refine ⟨217249693249700971898995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289666257666267962531993 217249693249700971898995)
        ·
          refine ⟨325874539874551457848493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217249693249700971898995 325874539874551457848493)
          ·
            refine ⟨122202952452956796693185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325874539874551457848493 122202952452956796693185)
            ·
              refine ⟨91652214339717597519889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122202952452956796693185 91652214339717597519889)
              ·
                refine ⟨68739160754788198139917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91652214339717597519889 68739160754788198139917)
                ·
                  refine ⟨25777185283045574302469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68739160754788198139917 25777185283045574302469)
                  ·
                    rfl

theorem cell20_56476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_56476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56476 prefixEnd_56476 := by exact prefixLift 56476
  have htrace : WordTrace (prefixWord ++ tailWord_56476) baseStart_56476 baseEnd_56476 := by
    simpa [prefixWord, tailWord_56476, baseEnd_56476] using wordTrace_append hprefix tailTrace_56476
  have hstable : (prefixWord ++ tailWord_56476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56476).length < 2 ^ (prefixWord ++ tailWord_56476).sum := by decide
  have hdescent : baseEnd_56476 < baseStart_56476 := by decide
  rcases family_descends (prefixWord ++ tailWord_56476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56535 : List Nat := [1, 1, 3, 2, 1, 2, 5, 2, 3]
def baseStart_56535 : Nat := 118140960795 + 56535 * 2 ^ 59
def prefixEnd_56535 : Nat := 4983230072969 + 3 ^ 40 * 56535 * 2
def baseEnd_56535 : Nat := 25804114490703591335561

theorem tailTrace_56535 : CollatzResearch.WordTrace tailWord_56535 prefixEnd_56535 25804114490703591335561 := by
  unfold tailWord_56535
  simp only [CollatzResearch.WordTrace]
  refine ⟨2062000850190825254403059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1374667233460550169602039 2062000850190825254403059)
  ·
    refine ⟨3093001275286237881604589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2062000850190825254403059 3093001275286237881604589)
    ·
      refine ⟨1159875478232339205601721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3093001275286237881604589 1159875478232339205601721)
      ·
        refine ⟨869906608674254404201291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1159875478232339205601721 869906608674254404201291)
        ·
          refine ⟨1304859913011381606301937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869906608674254404201291 1304859913011381606301937)
          ·
            refine ⟨978644934758536204726453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1304859913011381606301937 978644934758536204726453)
            ·
              refine ⟨91747962633612769193105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 978644934758536204726453 91747962633612769193105)
              ·
                refine ⟨68810971975209576894829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91747962633612769193105 68810971975209576894829)
                ·
                  refine ⟨25804114490703591335561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68810971975209576894829 25804114490703591335561)
                  ·
                    rfl

theorem cell20_56535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 2, 3].length) (baseStart_56535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56535 prefixEnd_56535 := by exact prefixLift 56535
  have htrace : WordTrace (prefixWord ++ tailWord_56535) baseStart_56535 baseEnd_56535 := by
    simpa [prefixWord, tailWord_56535, baseEnd_56535] using wordTrace_append hprefix tailTrace_56535
  have hstable : (prefixWord ++ tailWord_56535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56535).length < 2 ^ (prefixWord ++ tailWord_56535).sum := by decide
  have hdescent : baseEnd_56535 < baseStart_56535 := by decide
  rcases family_descends (prefixWord ++ tailWord_56535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56552 : List Nat := [2, 1, 4, 1, 2, 1, 5, 1, 3]
def baseStart_56552 : Nat := 118140960795 + 56552 * 2 ^ 59
def prefixEnd_56552 : Nat := 4983230072969 + 3 ^ 40 * 56552 * 2
def baseEnd_56552 : Nat := 25811873753927087768825

theorem tailTrace_56552 : CollatzResearch.WordTrace tailWord_56552 prefixEnd_56552 25811873753927087768825 := by
  unfold tailWord_56552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1031310445564618578885955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1375080594086158105181273 1031310445564618578885955)
  ·
    refine ⟨1546965668346927868328933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1031310445564618578885955 1546965668346927868328933)
    ·
      refine ⟨290056062815048975311675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1546965668346927868328933 290056062815048975311675)
      ·
        refine ⟨435084094222573462967513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290056062815048975311675 435084094222573462967513)
        ·
          refine ⟨326313070666930097225635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435084094222573462967513 326313070666930097225635)
          ·
            refine ⟨489469606000395145838453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326313070666930097225635 489469606000395145838453)
            ·
              refine ⟨45887775562537044922355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 489469606000395145838453 45887775562537044922355)
              ·
                refine ⟨68831663343805567383533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45887775562537044922355 68831663343805567383533)
                ·
                  refine ⟨25811873753927087768825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68831663343805567383533 25811873753927087768825)
                  ·
                    rfl

theorem cell20_56552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_56552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56552 prefixEnd_56552 := by exact prefixLift 56552
  have htrace : WordTrace (prefixWord ++ tailWord_56552) baseStart_56552 baseEnd_56552 := by
    simpa [prefixWord, tailWord_56552, baseEnd_56552] using wordTrace_append hprefix tailTrace_56552
  have hstable : (prefixWord ++ tailWord_56552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56552).length < 2 ^ (prefixWord ++ tailWord_56552).sum := by decide
  have hdescent : baseEnd_56552 < baseStart_56552 := by decide
  rcases family_descends (prefixWord ++ tailWord_56552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56562 : List Nat := [3, 2, 1, 3, 4, 1, 2, 4]
def baseStart_56562 : Nat := 118140960795 + 56562 * 2 ^ 59
def prefixEnd_56562 : Nat := 4983230072969 + 3 ^ 40 * 56562 * 2
def baseEnd_56562 : Nat := 8605479342137165811817

theorem tailTrace_56562 : CollatzResearch.WordTrace tailWord_56562 prefixEnd_56562 8605479342137165811817 := by
  unfold tailWord_56562
  simp only [CollatzResearch.WordTrace]
  refine ⟨515746405273252216408985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1375323747395339243757293 515746405273252216408985)
  ·
    refine ⟨386809803954939162306739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 515746405273252216408985 386809803954939162306739)
    ·
      refine ⟨580214705932408743460109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386809803954939162306739 580214705932408743460109)
      ·
        refine ⟨217580514724653278797541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580214705932408743460109 217580514724653278797541)
        ·
          refine ⟨40796346510872489774539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217580514724653278797541 40796346510872489774539)
          ·
            refine ⟨61194519766308734661809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40796346510872489774539 61194519766308734661809)
            ·
              refine ⟨45895889824731550996357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61194519766308734661809 45895889824731550996357)
              ·
                refine ⟨8605479342137165811817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45895889824731550996357 8605479342137165811817)
                ·
                  rfl

theorem cell20_56562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_56562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56562 prefixEnd_56562 := by exact prefixLift 56562
  have htrace : WordTrace (prefixWord ++ tailWord_56562) baseStart_56562 baseEnd_56562 := by
    simpa [prefixWord, tailWord_56562, baseEnd_56562] using wordTrace_append hprefix tailTrace_56562
  have hstable : (prefixWord ++ tailWord_56562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56562).length < 2 ^ (prefixWord ++ tailWord_56562).sum := by decide
  have hdescent : baseEnd_56562 < baseStart_56562 := by decide
  rcases family_descends (prefixWord ++ tailWord_56562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56587 : List Nat := [1, 1, 1, 1, 5, 5, 6]
def baseStart_56587 : Nat := 118140960795 + 56587 * 2 ^ 59
def prefixEnd_56587 : Nat := 4983230072969 + 3 ^ 40 * 56587 * 2
def baseEnd_56587 : Nat := 2869760967513613511335

theorem tailTrace_56587 : CollatzResearch.WordTrace tailWord_56587 prefixEnd_56587 2869760967513613511335 := by
  unfold tailWord_56587
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063897446002438135296015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1375931630668292090197343 2063897446002438135296015)
  ·
    refine ⟨3095846169003657202944023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2063897446002438135296015 3095846169003657202944023)
    ·
      refine ⟨4643769253505485804416035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095846169003657202944023 4643769253505485804416035)
      ·
        refine ⟨6965653880258228706624053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4643769253505485804416035 6965653880258228706624053)
        ·
          refine ⟨653030051274208941246005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6965653880258228706624053 653030051274208941246005)
          ·
            refine ⟨61221567306957088241813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 653030051274208941246005 61221567306957088241813)
            ·
              refine ⟨2869760967513613511335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61221567306957088241813 2869760967513613511335)
              ·
                rfl

theorem cell20_56587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 6].length) (baseStart_56587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56587 prefixEnd_56587 := by exact prefixLift 56587
  have htrace : WordTrace (prefixWord ++ tailWord_56587) baseStart_56587 baseEnd_56587 := by
    simpa [prefixWord, tailWord_56587, baseEnd_56587] using wordTrace_append hprefix tailTrace_56587
  have hstable : (prefixWord ++ tailWord_56587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56587).length < 2 ^ (prefixWord ++ tailWord_56587).sum := by decide
  have hdescent : baseEnd_56587 < baseStart_56587 := by decide
  rcases family_descends (prefixWord ++ tailWord_56587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56607 : List Nat := [1, 1, 2, 4, 4, 2, 2, 1, 3]
def baseStart_56607 : Nat := 118140960795 + 56607 * 2 ^ 59
def prefixEnd_56607 : Nat := 4983230072969 + 3 ^ 40 * 56607 * 2
def baseEnd_56607 : Nat := 25836977252591340935267

theorem tailTrace_56607 : CollatzResearch.WordTrace tailWord_56607 prefixEnd_56607 25836977252591340935267 := by
  unfold tailWord_56607
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064626905929981551024075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1376417937286654367349383 2064626905929981551024075)
  ·
    refine ⟨3096940358894972326536113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2064626905929981551024075 3096940358894972326536113)
    ·
      refine ⟨2322705269171229244902085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3096940358894972326536113 2322705269171229244902085)
      ·
        refine ⟨435507237969605483419141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2322705269171229244902085 435507237969605483419141)
        ·
          refine ⟨81657607119301028141089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435507237969605483419141 81657607119301028141089)
          ·
            refine ⟨61243205339475771105817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81657607119301028141089 61243205339475771105817)
            ·
              refine ⟨45932404004606828329363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61243205339475771105817 45932404004606828329363)
              ·
                refine ⟨68898606006910242494045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45932404004606828329363 68898606006910242494045)
                ·
                  refine ⟨25836977252591340935267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68898606006910242494045 25836977252591340935267)
                  ·
                    rfl

theorem cell20_56607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 1, 3].length) (baseStart_56607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56607 prefixEnd_56607 := by exact prefixLift 56607
  have htrace : WordTrace (prefixWord ++ tailWord_56607) baseStart_56607 baseEnd_56607 := by
    simpa [prefixWord, tailWord_56607, baseEnd_56607] using wordTrace_append hprefix tailTrace_56607
  have hstable : (prefixWord ++ tailWord_56607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56607).length < 2 ^ (prefixWord ++ tailWord_56607).sum := by decide
  have hdescent : baseEnd_56607 < baseStart_56607 := by decide
  rcases family_descends (prefixWord ++ tailWord_56607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56611 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 3]
def baseStart_56611 : Nat := 118140960795 + 56611 * 2 ^ 59
def prefixEnd_56611 : Nat := 4983230072969 + 3 ^ 40 * 56611 * 2
def baseEnd_56611 : Nat := 25838802961585104801917

theorem tailTrace_56611 : CollatzResearch.WordTrace tailWord_56611 prefixEnd_56611 25838802961585104801917 := by
  unfold tailWord_56611
  simp only [CollatzResearch.WordTrace]
  refine ⟨2064772797915490234169687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1376515198610326822779791 2064772797915490234169687)
  ·
    refine ⟨3097159196873235351254531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2064772797915490234169687 3097159196873235351254531)
    ·
      refine ⟨4645738795309853026881797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3097159196873235351254531 4645738795309853026881797)
      ·
        refine ⟨871076024120597442540337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4645738795309853026881797 871076024120597442540337)
        ·
          refine ⟨653307018090448081905253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 871076024120597442540337 653307018090448081905253)
          ·
            refine ⟨122495065891959015357235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 653307018090448081905253 122495065891959015357235)
            ·
              refine ⟨183742598837938523035853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122495065891959015357235 183742598837938523035853)
              ·
                refine ⟨68903474564226946138445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 183742598837938523035853 68903474564226946138445)
                ·
                  refine ⟨25838802961585104801917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68903474564226946138445 25838802961585104801917)
                  ·
                    rfl

theorem cell20_56611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 3].length) (baseStart_56611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56611 prefixEnd_56611 := by exact prefixLift 56611
  have htrace : WordTrace (prefixWord ++ tailWord_56611) baseStart_56611 baseEnd_56611 := by
    simpa [prefixWord, tailWord_56611, baseEnd_56611] using wordTrace_append hprefix tailTrace_56611
  have hstable : (prefixWord ++ tailWord_56611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56611).length < 2 ^ (prefixWord ++ tailWord_56611).sum := by decide
  have hdescent : baseEnd_56611 < baseStart_56611 := by decide
  rcases family_descends (prefixWord ++ tailWord_56611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56625 : List Nat := [1, 2, 2, 3, 3, 1, 2, 6]
def baseStart_56625 : Nat := 118140960795 + 56625 * 2 ^ 59
def prefixEnd_56625 : Nat := 4983230072969 + 3 ^ 40 * 56625 * 2
def baseEnd_56625 : Nat := 8615064314354426111731

theorem tailTrace_56625 : CollatzResearch.WordTrace tailWord_56625 prefixEnd_56625 8615064314354426111731 := by
  unfold tailWord_56625
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065283419864770625179329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1376855613243180416786219 2065283419864770625179329)
  ·
    refine ⟨1548962564898577968884497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2065283419864770625179329 1548962564898577968884497)
    ·
      refine ⟨1161721923673933476663373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1548962564898577968884497 1161721923673933476663373)
      ·
        refine ⟨435645721377725053748765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1161721923673933476663373 435645721377725053748765)
        ·
          refine ⟨163367145516646895155787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 435645721377725053748765 163367145516646895155787)
          ·
            refine ⟨245050718274970342733681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163367145516646895155787 245050718274970342733681)
            ·
              refine ⟨183788038706227757050261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245050718274970342733681 183788038706227757050261)
              ·
                refine ⟨8615064314354426111731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 183788038706227757050261 8615064314354426111731)
                ·
                  rfl

theorem cell20_56625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_56625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56625 prefixEnd_56625 := by exact prefixLift 56625
  have htrace : WordTrace (prefixWord ++ tailWord_56625) baseStart_56625 baseEnd_56625 := by
    simpa [prefixWord, tailWord_56625, baseEnd_56625] using wordTrace_append hprefix tailTrace_56625
  have hstable : (prefixWord ++ tailWord_56625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56625).length < 2 ^ (prefixWord ++ tailWord_56625).sum := by decide
  have hdescent : baseEnd_56625 < baseStart_56625 := by decide
  rcases family_descends (prefixWord ++ tailWord_56625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56652 : List Nat := [2, 2, 1, 3, 2, 2, 4, 2, 2]
def baseStart_56652 : Nat := 118140960795 + 56652 * 2 ^ 59
def prefixEnd_56652 : Nat := 4983230072969 + 3 ^ 40 * 56652 * 2
def baseEnd_56652 : Nat := 25857516478771184435083

theorem tailTrace_56652 : CollatzResearch.WordTrace tailWord_56652 prefixEnd_56652 25857516478771184435083 := by
  unfold tailWord_56652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1033134095383477118206105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1377512127177969490941473 1033134095383477118206105)
  ·
    refine ⟨774850571537607838654579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1033134095383477118206105 774850571537607838654579)
    ·
      refine ⟨1162275857306411757981869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 774850571537607838654579 1162275857306411757981869)
      ·
        refine ⟨435853446489904409243201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1162275857306411757981869 435853446489904409243201)
        ·
          refine ⟨326890084867428306932401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 435853446489904409243201 326890084867428306932401)
          ·
            refine ⟨245167563650571230199301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326890084867428306932401 245167563650571230199301)
            ·
              refine ⟨45968918184482105662369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245167563650571230199301 45968918184482105662369)
              ·
                refine ⟨34476688638361579246777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45968918184482105662369 34476688638361579246777)
                ·
                  refine ⟨25857516478771184435083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34476688638361579246777 25857516478771184435083)
                  ·
                    rfl

theorem cell20_56652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_56652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56652 prefixEnd_56652 := by exact prefixLift 56652
  have htrace : WordTrace (prefixWord ++ tailWord_56652) baseStart_56652 baseEnd_56652 := by
    simpa [prefixWord, tailWord_56652, baseEnd_56652] using wordTrace_append hprefix tailTrace_56652
  have hstable : (prefixWord ++ tailWord_56652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56652).length < 2 ^ (prefixWord ++ tailWord_56652).sum := by decide
  have hdescent : baseEnd_56652 < baseStart_56652 := by decide
  rcases family_descends (prefixWord ++ tailWord_56652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56663 : List Nat := [1, 1, 3, 2, 3, 2, 3, 5]
def baseStart_56663 : Nat := 118140960795 + 56663 * 2 ^ 59
def prefixEnd_56663 : Nat := 4983230072969 + 3 ^ 40 * 56663 * 2
def baseEnd_56663 : Nat := 8620845726168011689457

theorem tailTrace_56663 : CollatzResearch.WordTrace tailWord_56663 prefixEnd_56663 8620845726168011689457 := by
  unfold tailWord_56663
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066669393727103115062643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1377779595818068743375095 2066669393727103115062643)
  ·
    refine ⟨3100004090590654672593965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2066669393727103115062643 3100004090590654672593965)
    ·
      refine ⟨1162501533971495502222737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3100004090590654672593965 1162501533971495502222737)
      ·
        refine ⟨871876150478621626667053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1162501533971495502222737 871876150478621626667053)
        ·
          refine ⟨326953556429483110000145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 871876150478621626667053 326953556429483110000145)
          ·
            refine ⟨245215167322112332500109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326953556429483110000145 245215167322112332500109)
            ·
              refine ⟨91955687745792124687541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245215167322112332500109 91955687745792124687541)
              ·
                refine ⟨8620845726168011689457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91955687745792124687541 8620845726168011689457)
                ·
                  rfl

theorem cell20_56663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_56663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56663 prefixEnd_56663 := by exact prefixLift 56663
  have htrace : WordTrace (prefixWord ++ tailWord_56663) baseStart_56663 baseEnd_56663 := by
    simpa [prefixWord, tailWord_56663, baseEnd_56663] using wordTrace_append hprefix tailTrace_56663
  have hstable : (prefixWord ++ tailWord_56663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56663).length < 2 ^ (prefixWord ++ tailWord_56663).sum := by decide
  have hdescent : baseEnd_56663 < baseStart_56663 := by decide
  rcases family_descends (prefixWord ++ tailWord_56663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56669 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 4]
def baseStart_56669 : Nat := 118140960795 + 56669 * 2 ^ 59
def prefixEnd_56669 : Nat := 4983230072969 + 3 ^ 40 * 56669 * 2
def baseEnd_56669 : Nat := 25865275741994680868347

theorem tailTrace_56669 : CollatzResearch.WordTrace tailWord_56669 prefixEnd_56669 25865275741994680868347 := by
  unfold tailWord_56669
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066888231705366139781061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1377925487803577426520707 2066888231705366139781061)
  ·
    refine ⟨387541543444756151208949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2066888231705366139781061 387541543444756151208949)
    ·
      refine ⟨36332019697945889175839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 387541543444756151208949 36332019697945889175839)
      ·
        refine ⟨54498029546918833763759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36332019697945889175839 54498029546918833763759)
        ·
          refine ⟨81747044320378250645639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54498029546918833763759 81747044320378250645639)
          ·
            refine ⟨122620566480567375968459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81747044320378250645639 122620566480567375968459)
            ·
              refine ⟨183930849720851063952689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122620566480567375968459 183930849720851063952689)
              ·
                refine ⟨137948137290638297964517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 183930849720851063952689 137948137290638297964517)
                ·
                  refine ⟨25865275741994680868347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137948137290638297964517 25865275741994680868347)
                  ·
                    rfl

theorem cell20_56669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_56669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56669 prefixEnd_56669 := by exact prefixLift 56669
  have htrace : WordTrace (prefixWord ++ tailWord_56669) baseStart_56669 baseEnd_56669 := by
    simpa [prefixWord, tailWord_56669, baseEnd_56669] using wordTrace_append hprefix tailTrace_56669
  have hstable : (prefixWord ++ tailWord_56669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56669).length < 2 ^ (prefixWord ++ tailWord_56669).sum := by decide
  have hdescent : baseEnd_56669 < baseStart_56669 := by decide
  rcases family_descends (prefixWord ++ tailWord_56669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56711 : List Nat := [1, 1, 4, 2, 2, 2, 2, 4, 2]
def baseStart_56711 : Nat := 118140960795 + 56711 * 2 ^ 59
def prefixEnd_56711 : Nat := 4983230072969 + 3 ^ 40 * 56711 * 2
def baseEnd_56711 : Nat := 25884445686429201468175

theorem tailTrace_56711 : CollatzResearch.WordTrace tailWord_56711 prefixEnd_56711 25884445686429201468175 := by
  unfold tailWord_56711
  simp only [CollatzResearch.WordTrace]
  refine ⟨2068420097553207312809987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1378946731702138208539991 2068420097553207312809987)
  ·
    refine ⟨3102630146329810969214981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2068420097553207312809987 3102630146329810969214981)
    ·
      refine ⟨581743152436839556727809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3102630146329810969214981 581743152436839556727809)
      ·
        refine ⟨436307364327629667545857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581743152436839556727809 436307364327629667545857)
        ·
          refine ⟨327230523245722250659393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 436307364327629667545857 327230523245722250659393)
          ·
            refine ⟨245422892434291687994545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327230523245722250659393 245422892434291687994545)
            ·
              refine ⟨184067169325718765995909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245422892434291687994545 184067169325718765995909)
              ·
                refine ⟨34512594248572268624233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184067169325718765995909 34512594248572268624233)
                ·
                  refine ⟨25884445686429201468175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34512594248572268624233 25884445686429201468175)
                  ·
                    rfl

theorem cell20_56711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 2].length) (baseStart_56711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56711 prefixEnd_56711 := by exact prefixLift 56711
  have htrace : WordTrace (prefixWord ++ tailWord_56711) baseStart_56711 baseEnd_56711 := by
    simpa [prefixWord, tailWord_56711, baseEnd_56711] using wordTrace_append hprefix tailTrace_56711
  have hstable : (prefixWord ++ tailWord_56711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56711).length < 2 ^ (prefixWord ++ tailWord_56711).sum := by decide
  have hdescent : baseEnd_56711 < baseStart_56711 := by decide
  rcases family_descends (prefixWord ++ tailWord_56711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56760 : List Nat := [2, 1, 2, 1, 2, 2, 10]
def baseStart_56760 : Nat := 118140960795 + 56760 * 2 ^ 59
def prefixEnd_56760 : Nat := 4983230072969 + 3 ^ 40 * 56760 * 2
def baseEnd_56760 : Nat := 2878534513511423203849

theorem tailTrace_56760 : CollatzResearch.WordTrace tailWord_56760 prefixEnd_56760 2878534513511423203849 := by
  unfold tailWord_56760
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035103637187844340671867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1380138182917125787562489 1035103637187844340671867)
  ·
    refine ⟨1552655455781766511007801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1035103637187844340671867 1552655455781766511007801)
    ·
      refine ⟨1164491591836324883255851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1552655455781766511007801 1164491591836324883255851)
      ·
        refine ⟨1746737387754487324883777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164491591836324883255851 1746737387754487324883777)
        ·
          refine ⟨1310053040815865493662833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746737387754487324883777 1310053040815865493662833)
          ·
            refine ⟨982539780611899120247125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1310053040815865493662833 982539780611899120247125)
            ·
              refine ⟨2878534513511423203849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 982539780611899120247125 2878534513511423203849)
              ·
                rfl

theorem cell20_56760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 10].length) (baseStart_56760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56760 prefixEnd_56760 := by exact prefixLift 56760
  have htrace : WordTrace (prefixWord ++ tailWord_56760) baseStart_56760 baseEnd_56760 := by
    simpa [prefixWord, tailWord_56760, baseEnd_56760] using wordTrace_append hprefix tailTrace_56760
  have hstable : (prefixWord ++ tailWord_56760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56760).length < 2 ^ (prefixWord ++ tailWord_56760).sum := by decide
  have hdescent : baseEnd_56760 < baseStart_56760 := by decide
  rcases family_descends (prefixWord ++ tailWord_56760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56780 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 3]
def baseStart_56780 : Nat := 118140960795 + 56780 * 2 ^ 59
def prefixEnd_56780 : Nat := 4983230072969 + 3 ^ 40 * 56780 * 2
def baseEnd_56780 : Nat := 25915939166571628167893

theorem tailTrace_56780 : CollatzResearch.WordTrace tailWord_56780 prefixEnd_56780 25915939166571628167893 := by
  unfold tailWord_56780
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035468367151616048535897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1380624489535488064714529 1035468367151616048535897)
  ·
    refine ⟨776601275363712036401923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1035468367151616048535897 776601275363712036401923)
    ·
      refine ⟨1164901913045568054602885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 776601275363712036401923 1164901913045568054602885)
      ·
        refine ⟨218419108696044010238041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1164901913045568054602885 218419108696044010238041)
        ·
          refine ⟨163814331522033007678531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218419108696044010238041 163814331522033007678531)
          ·
            refine ⟨245721497283049511517797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163814331522033007678531 245721497283049511517797)
            ·
              refine ⟨46072780740571783409587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245721497283049511517797 46072780740571783409587)
              ·
                refine ⟨69109171110857675114381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46072780740571783409587 69109171110857675114381)
                ·
                  refine ⟨25915939166571628167893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69109171110857675114381 25915939166571628167893)
                  ·
                    rfl

theorem cell20_56780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_56780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56780 prefixEnd_56780 := by exact prefixLift 56780
  have htrace : WordTrace (prefixWord ++ tailWord_56780) baseStart_56780 baseEnd_56780 := by
    simpa [prefixWord, tailWord_56780, baseEnd_56780] using wordTrace_append hprefix tailTrace_56780
  have hstable : (prefixWord ++ tailWord_56780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56780).length < 2 ^ (prefixWord ++ tailWord_56780).sum := by decide
  have hdescent : baseEnd_56780 < baseStart_56780 := by decide
  rcases family_descends (prefixWord ++ tailWord_56780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56784 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 3]
def baseStart_56784 : Nat := 118140960795 + 56784 * 2 ^ 59
def prefixEnd_56784 : Nat := 4983230072969 + 3 ^ 40 * 56784 * 2
def baseEnd_56784 : Nat := 25917764875565392034543

theorem tailTrace_56784 : CollatzResearch.WordTrace tailWord_56784 prefixEnd_56784 25917764875565392034543 := by
  unfold tailWord_56784
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035541313144370390108703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1380721750859160520144937 1035541313144370390108703)
  ·
    refine ⟨1553311969716555585163055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1035541313144370390108703 1553311969716555585163055)
    ·
      refine ⟨2329967954574833377744583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1553311969716555585163055 2329967954574833377744583)
      ·
        refine ⟨3494951931862250066616875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2329967954574833377744583 3494951931862250066616875)
        ·
          refine ⟨5242427897793375099925313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494951931862250066616875 5242427897793375099925313)
          ·
            refine ⟨3931820923345031324943985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5242427897793375099925313 3931820923345031324943985)
            ·
              refine ⟨2948865692508773493707989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3931820923345031324943985 2948865692508773493707989)
              ·
                refine ⟨69114039668174378758781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2948865692508773493707989 69114039668174378758781)
                ·
                  refine ⟨25917764875565392034543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69114039668174378758781 25917764875565392034543)
                  ·
                    rfl

theorem cell20_56784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_56784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56784 prefixEnd_56784 := by exact prefixLift 56784
  have htrace : WordTrace (prefixWord ++ tailWord_56784) baseStart_56784 baseEnd_56784 := by
    simpa [prefixWord, tailWord_56784, baseEnd_56784] using wordTrace_append hprefix tailTrace_56784
  have hstable : (prefixWord ++ tailWord_56784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56784).length < 2 ^ (prefixWord ++ tailWord_56784).sum := by decide
  have hdescent : baseEnd_56784 < baseStart_56784 := by decide
  rcases family_descends (prefixWord ++ tailWord_56784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56791 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 4]
def baseStart_56791 : Nat := 118140960795 + 56791 * 2 ^ 59
def prefixEnd_56791 : Nat := 4983230072969 + 3 ^ 40 * 56791 * 2
def baseEnd_56791 : Nat := 25920959866304478801181

theorem tailTrace_56791 : CollatzResearch.WordTrace tailWord_56791 prefixEnd_56791 25920959866304478801181 := by
  unfold tailWord_56791
  simp only [CollatzResearch.WordTrace]
  refine ⟨2071337937263380975722227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1380891958175587317148151 2071337937263380975722227)
  ·
    refine ⟨3107006905895071463583341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2071337937263380975722227 3107006905895071463583341)
    ·
      refine ⟨1165127589710651798843753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3107006905895071463583341 1165127589710651798843753)
      ·
        refine ⟨873845692282988849132815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1165127589710651798843753 873845692282988849132815)
        ·
          refine ⟨1310768538424483273699223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873845692282988849132815 1310768538424483273699223)
          ·
            refine ⟨1966152807636724910548835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310768538424483273699223 1966152807636724910548835)
            ·
              refine ⟨2949229211455087365823253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966152807636724910548835 2949229211455087365823253)
              ·
                refine ⟨138245119286957220272965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2949229211455087365823253 138245119286957220272965)
                ·
                  refine ⟨25920959866304478801181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138245119286957220272965 25920959866304478801181)
                  ·
                    rfl

theorem cell20_56791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_56791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56791 prefixEnd_56791 := by exact prefixLift 56791
  have htrace : WordTrace (prefixWord ++ tailWord_56791) baseStart_56791 baseEnd_56791 := by
    simpa [prefixWord, tailWord_56791, baseEnd_56791] using wordTrace_append hprefix tailTrace_56791
  have hstable : (prefixWord ++ tailWord_56791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56791).length < 2 ^ (prefixWord ++ tailWord_56791).sum := by decide
  have hdescent : baseEnd_56791 < baseStart_56791 := by decide
  rcases family_descends (prefixWord ++ tailWord_56791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56818 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_56818 : Nat := 118140960795 + 56818 * 2 ^ 59
def prefixEnd_56818 : Nat := 4983230072969 + 3 ^ 40 * 56818 * 2
def baseEnd_56818 : Nat := 25933283402012384901071

theorem tailTrace_56818 : CollatzResearch.WordTrace tailWord_56818 prefixEnd_56818 25933283402012384901071 := by
  unfold tailWord_56818
  simp only [CollatzResearch.WordTrace]
  refine ⟨518080677041391146738777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1381548472110376391303405 518080677041391146738777)
  ·
    refine ⟨388560507781043360054083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 518080677041391146738777 388560507781043360054083)
    ·
      refine ⟨582840761671565040081125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388560507781043360054083 582840761671565040081125)
      ·
        refine ⟨109282642813418445015211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 582840761671565040081125 109282642813418445015211)
        ·
          refine ⟨163923964220127667522817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109282642813418445015211 163923964220127667522817)
          ·
            refine ⟨122942973165095750642113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163923964220127667522817 122942973165095750642113)
            ·
              refine ⟨92207229873821812981585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122942973165095750642113 92207229873821812981585)
              ·
                refine ⟨69155422405366359736189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92207229873821812981585 69155422405366359736189)
                ·
                  refine ⟨25933283402012384901071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69155422405366359736189 25933283402012384901071)
                  ·
                    rfl

theorem cell20_56818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_56818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56818 prefixEnd_56818 := by exact prefixLift 56818
  have htrace : WordTrace (prefixWord ++ tailWord_56818) baseStart_56818 baseEnd_56818 := by
    simpa [prefixWord, tailWord_56818, baseEnd_56818] using wordTrace_append hprefix tailTrace_56818
  have hstable : (prefixWord ++ tailWord_56818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56818).length < 2 ^ (prefixWord ++ tailWord_56818).sum := by decide
  have hdescent : baseEnd_56818 < baseStart_56818 := by decide
  rcases family_descends (prefixWord ++ tailWord_56818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56821 : List Nat := [1, 3, 5, 1, 1, 1, 4, 2, 2]
def baseStart_56821 : Nat := 118140960795 + 56821 * 2 ^ 59
def prefixEnd_56821 : Nat := 4983230072969 + 3 ^ 40 * 56821 * 2
def baseEnd_56821 : Nat := 25934652683757707801059

theorem tailTrace_56821 : CollatzResearch.WordTrace tailWord_56821 prefixEnd_56821 25934652683757707801059 := by
  unfold tailWord_56821
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072432127154696099314317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1381621418103130732876211 2072432127154696099314317)
  ·
    refine ⟨777162047683011037242869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2072432127154696099314317 777162047683011037242869)
    ·
      refine ⟨72858941970282284741519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 777162047683011037242869 72858941970282284741519)
      ·
        refine ⟨109288412955423427112279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72858941970282284741519 109288412955423427112279)
        ·
          refine ⟨163932619433135140668419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109288412955423427112279 163932619433135140668419)
          ·
            refine ⟨245898929149702711002629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163932619433135140668419 245898929149702711002629)
            ·
              refine ⟨46106049215569258312993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 245898929149702711002629 46106049215569258312993)
              ·
                refine ⟨34579536911676943734745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46106049215569258312993 34579536911676943734745)
                ·
                  refine ⟨25934652683757707801059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34579536911676943734745 25934652683757707801059)
                  ·
                    rfl

theorem cell20_56821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_56821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56821 prefixEnd_56821 := by exact prefixLift 56821
  have htrace : WordTrace (prefixWord ++ tailWord_56821) baseStart_56821 baseEnd_56821 := by
    simpa [prefixWord, tailWord_56821, baseEnd_56821] using wordTrace_append hprefix tailTrace_56821
  have hstable : (prefixWord ++ tailWord_56821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56821).length < 2 ^ (prefixWord ++ tailWord_56821).sum := by decide
  have hdescent : baseEnd_56821 < baseStart_56821 := by decide
  rcases family_descends (prefixWord ++ tailWord_56821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56839 : List Nat := [1, 1, 4, 3, 2, 1, 2, 3, 3]
def baseStart_56839 : Nat := 118140960795 + 56839 * 2 ^ 59
def prefixEnd_56839 : Nat := 4983230072969 + 3 ^ 40 * 56839 * 2
def baseEnd_56839 : Nat := 25942868374229645200985

theorem tailTrace_56839 : CollatzResearch.WordTrace tailWord_56839 prefixEnd_56839 25942868374229645200985 := by
  unfold tailWord_56839
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073088641089485173469571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1382059094059656782313047 2073088641089485173469571)
  ·
    refine ⟨3109632961634227760204357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2073088641089485173469571 3109632961634227760204357)
    ·
      refine ⟨583056180306417705038317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3109632961634227760204357 583056180306417705038317)
      ·
        refine ⟨218646067614906639389369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 583056180306417705038317 218646067614906639389369)
        ·
          refine ⟨163984550711179979542027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218646067614906639389369 163984550711179979542027)
          ·
            refine ⟨245976826066769969313041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163984550711179979542027 245976826066769969313041)
            ·
              refine ⟨184482619550077476984781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245976826066769969313041 184482619550077476984781)
              ·
                refine ⟨69180982331279053869293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184482619550077476984781 69180982331279053869293)
                ·
                  refine ⟨25942868374229645200985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69180982331279053869293 25942868374229645200985)
                  ·
                    rfl

theorem cell20_56839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 3].length) (baseStart_56839 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56839 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56839 prefixEnd_56839 := by exact prefixLift 56839
  have htrace : WordTrace (prefixWord ++ tailWord_56839) baseStart_56839 baseEnd_56839 := by
    simpa [prefixWord, tailWord_56839, baseEnd_56839] using wordTrace_append hprefix tailTrace_56839
  have hstable : (prefixWord ++ tailWord_56839).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56839).length < 2 ^ (prefixWord ++ tailWord_56839).sum := by decide
  have hdescent : baseEnd_56839 < baseStart_56839 := by decide
  rcases family_descends (prefixWord ++ tailWord_56839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56860 : List Nat := [2, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_56860 : Nat := 118140960795 + 56860 * 2 ^ 59
def prefixEnd_56860 : Nat := 4983230072969 + 3 ^ 40 * 56860 * 2
def baseEnd_56860 : Nat := 25952453346446905500899

theorem tailTrace_56860 : CollatzResearch.WordTrace tailWord_56860 prefixEnd_56860 25952453346446905500899 := by
  unfold tailWord_56860
  simp only [CollatzResearch.WordTrace]
  refine ⟨1036927287006702879992017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1382569716008937173322689 1036927287006702879992017)
  ·
    refine ⟨777695465255027159994013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1036927287006702879992017 777695465255027159994013)
    ·
      refine ⟨291635799470635184997755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 777695465255027159994013 291635799470635184997755)
      ·
        refine ⟨437453699205952777496633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291635799470635184997755 437453699205952777496633)
        ·
          refine ⟨328090274404464583122475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437453699205952777496633 328090274404464583122475)
          ·
            refine ⟨492135411606696874683713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 328090274404464583122475 492135411606696874683713)
            ·
              refine ⟨369101558705022656012785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492135411606696874683713 369101558705022656012785)
              ·
                refine ⟨276826169028766992009589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369101558705022656012785 276826169028766992009589)
                ·
                  refine ⟨25952453346446905500899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 276826169028766992009589 25952453346446905500899)
                  ·
                    rfl

theorem cell20_56860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_56860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56860 prefixEnd_56860 := by exact prefixLift 56860
  have htrace : WordTrace (prefixWord ++ tailWord_56860) baseStart_56860 baseEnd_56860 := by
    simpa [prefixWord, tailWord_56860, baseEnd_56860] using wordTrace_append hprefix tailTrace_56860
  have hstable : (prefixWord ++ tailWord_56860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56860).length < 2 ^ (prefixWord ++ tailWord_56860).sum := by decide
  have hdescent : baseEnd_56860 < baseStart_56860 := by decide
  rcases family_descends (prefixWord ++ tailWord_56860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56908 : List Nat := [2, 2, 1, 3, 1, 5, 2, 4]
def baseStart_56908 : Nat := 118140960795 + 56908 * 2 ^ 59
def prefixEnd_56908 : Nat := 4983230072969 + 3 ^ 40 * 56908 * 2
def baseEnd_56908 : Nat := 8658120618124023966901

theorem tailTrace_56908 : CollatzResearch.WordTrace tailWord_56908 prefixEnd_56908 8658120618124023966901 := by
  unfold tailWord_56908
  simp only [CollatzResearch.WordTrace]
  refine ⟨1037802638919754978865689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1383736851893006638487585 1037802638919754978865689)
  ·
    refine ⟨778351979189816234149267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1037802638919754978865689 778351979189816234149267)
    ·
      refine ⟨1167527968784724351223901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 778351979189816234149267 1167527968784724351223901)
      ·
        refine ⟨437822988294271631708963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1167527968784724351223901 437822988294271631708963)
        ·
          refine ⟨656734482441407447563445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437822988294271631708963 656734482441407447563445)
          ·
            refine ⟨61568857728881948209073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 656734482441407447563445 61568857728881948209073)
            ·
              refine ⟨46176643296661461156805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61568857728881948209073 46176643296661461156805)
              ·
                refine ⟨8658120618124023966901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46176643296661461156805 8658120618124023966901)
                ·
                  rfl

theorem cell20_56908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_56908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56908 prefixEnd_56908 := by exact prefixLift 56908
  have htrace : WordTrace (prefixWord ++ tailWord_56908) baseStart_56908 baseEnd_56908 := by
    simpa [prefixWord, tailWord_56908, baseEnd_56908] using wordTrace_append hprefix tailTrace_56908
  have hstable : (prefixWord ++ tailWord_56908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56908).length < 2 ^ (prefixWord ++ tailWord_56908).sum := by decide
  have hdescent : baseEnd_56908 < baseStart_56908 := by decide
  rcases family_descends (prefixWord ++ tailWord_56908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56912 : List Nat := [2, 1, 1, 1, 1, 3, 5, 6]
def baseStart_56912 : Nat := 118140960795 + 56912 * 2 ^ 59
def prefixEnd_56912 : Nat := 4983230072969 + 3 ^ 40 * 56912 * 2
def baseEnd_56912 : Nat := 8658729187788611922451

theorem tailTrace_56912 : CollatzResearch.WordTrace tailWord_56912 prefixEnd_56912 8658729187788611922451 := by
  unfold tailWord_56912
  simp only [CollatzResearch.WordTrace]
  refine ⟨1037875584912509320438495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1383834113216679093917993 1037875584912509320438495)
  ·
    refine ⟨1556813377368763980657743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1037875584912509320438495 1556813377368763980657743)
    ·
      refine ⟨2335220066053145970986615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1556813377368763980657743 2335220066053145970986615)
      ·
        refine ⟨3502830099079718956479923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2335220066053145970986615 3502830099079718956479923)
        ·
          refine ⟨5254245148619578434719885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3502830099079718956479923 5254245148619578434719885)
          ·
            refine ⟨1970341930732341913019957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5254245148619578434719885 1970341930732341913019957)
            ·
              refine ⟨184719556006157054345621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1970341930732341913019957 184719556006157054345621)
              ·
                refine ⟨8658729187788611922451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 184719556006157054345621 8658729187788611922451)
                ·
                  rfl

theorem cell20_56912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_56912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56912 prefixEnd_56912 := by exact prefixLift 56912
  have htrace : WordTrace (prefixWord ++ tailWord_56912) baseStart_56912 baseEnd_56912 := by
    simpa [prefixWord, tailWord_56912, baseEnd_56912] using wordTrace_append hprefix tailTrace_56912
  have hstable : (prefixWord ++ tailWord_56912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56912).length < 2 ^ (prefixWord ++ tailWord_56912).sum := by decide
  have hdescent : baseEnd_56912 < baseStart_56912 := by decide
  rcases family_descends (prefixWord ++ tailWord_56912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56925 : List Nat := [1, 4, 4, 2, 1, 2, 6]
def baseStart_56925 : Nat := 118140960795 + 56925 * 2 ^ 59
def prefixEnd_56925 : Nat := 4983230072969 + 3 ^ 40 * 56925 * 2
def baseEnd_56925 : Nat := 2886902346399507592663

theorem tailTrace_56925 : CollatzResearch.WordTrace tailWord_56925 prefixEnd_56925 2886902346399507592663 := by
  unfold tailWord_56925
  simp only [CollatzResearch.WordTrace]
  refine ⟨2076225318777921861100229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1384150212518614574066819 2076225318777921861100229)
  ·
    refine ⟨389292247270860348956293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2076225318777921861100229 389292247270860348956293)
    ·
      refine ⟨72992296363286315429305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 389292247270860348956293 72992296363286315429305)
      ·
        refine ⟨54744222272464736571979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72992296363286315429305 54744222272464736571979)
        ·
          refine ⟨82116333408697104857969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54744222272464736571979 82116333408697104857969)
          ·
            refine ⟨61587250056522828643477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82116333408697104857969 61587250056522828643477)
            ·
              refine ⟨2886902346399507592663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61587250056522828643477 2886902346399507592663)
              ·
                rfl

theorem cell20_56925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 6].length) (baseStart_56925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56925 prefixEnd_56925 := by exact prefixLift 56925
  have htrace : WordTrace (prefixWord ++ tailWord_56925) baseStart_56925 baseEnd_56925 := by
    simpa [prefixWord, tailWord_56925, baseEnd_56925] using wordTrace_append hprefix tailTrace_56925
  have hstable : (prefixWord ++ tailWord_56925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56925).length < 2 ^ (prefixWord ++ tailWord_56925).sum := by decide
  have hdescent : baseEnd_56925 < baseStart_56925 := by decide
  rcases family_descends (prefixWord ++ tailWord_56925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56949 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 3]
def baseStart_56949 : Nat := 118140960795 + 56949 * 2 ^ 59
def prefixEnd_56949 : Nat := 4983230072969 + 3 ^ 40 * 56949 * 2
def baseEnd_56949 : Nat := 25993075371558151533869

theorem tailTrace_56949 : CollatzResearch.WordTrace tailWord_56949 prefixEnd_56949 25993075371558151533869 := by
  unfold tailWord_56949
  simp only [CollatzResearch.WordTrace]
  refine ⟨2077100670690973959973901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1384733780460649306649267 2077100670690973959973901)
  ·
    refine ⟨778912751509115234990213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2077100670690973959973901 778912751509115234990213)
    ·
      refine ⟨146046140907959106560665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 778912751509115234990213 146046140907959106560665)
      ·
        refine ⟨109534605680969329920499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146046140907959106560665 109534605680969329920499)
        ·
          refine ⟨164301908521453994880749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109534605680969329920499 164301908521453994880749)
          ·
            refine ⟨61613215695545248080281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 164301908521453994880749 61613215695545248080281)
            ·
              refine ⟨46209911771658936060211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61613215695545248080281 46209911771658936060211)
              ·
                refine ⟨69314867657488404090317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46209911771658936060211 69314867657488404090317)
                ·
                  refine ⟨25993075371558151533869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69314867657488404090317 25993075371558151533869)
                  ·
                    rfl

theorem cell20_56949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_56949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56949 prefixEnd_56949 := by exact prefixLift 56949
  have htrace : WordTrace (prefixWord ++ tailWord_56949) baseStart_56949 baseEnd_56949 := by
    simpa [prefixWord, tailWord_56949, baseEnd_56949] using wordTrace_append hprefix tailTrace_56949
  have hstable : (prefixWord ++ tailWord_56949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56949).length < 2 ^ (prefixWord ++ tailWord_56949).sum := by decide
  have hdescent : baseEnd_56949 < baseStart_56949 := by decide
  rcases family_descends (prefixWord ++ tailWord_56949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_56988 : List Nat := [2, 2, 3, 2, 11]
def baseStart_56988 : Nat := 118140960795 + 56988 * 2 ^ 59
def prefixEnd_56988 : Nat := 4983230072969 + 3 ^ 40 * 56988 * 2
def baseEnd_56988 : Nat := 321121926348732706589

theorem tailTrace_56988 : CollatzResearch.WordTrace tailWord_56988 prefixEnd_56988 321121926348732706589 := by
  unfold tailWord_56988
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039261558774841810321809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1385682078366455747095745 1039261558774841810321809)
  ·
    refine ⟨779446169081131357741357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1039261558774841810321809 779446169081131357741357)
    ·
      refine ⟨292292313405424259153009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 779446169081131357741357 292292313405424259153009)
      ·
        refine ⟨219219235054068194364757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292292313405424259153009 219219235054068194364757)
        ·
          refine ⟨321121926348732706589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 219219235054068194364757 321121926348732706589)
          ·
            rfl

theorem cell20_56988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 11].length) (baseStart_56988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_56988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_56988 prefixEnd_56988 := by exact prefixLift 56988
  have htrace : WordTrace (prefixWord ++ tailWord_56988) baseStart_56988 baseEnd_56988 := by
    simpa [prefixWord, tailWord_56988, baseEnd_56988] using wordTrace_append hprefix tailTrace_56988
  have hstable : (prefixWord ++ tailWord_56988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_56988).length < 2 ^ (prefixWord ++ tailWord_56988).sum := by decide
  have hdescent : baseEnd_56988 < baseStart_56988 := by decide
  rcases family_descends (prefixWord ++ tailWord_56988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57022 : List Nat := [4, 2, 1, 1, 2, 3, 3, 4]
def baseStart_57022 : Nat := 118140960795 + 57022 * 2 ^ 59
def prefixEnd_57022 : Nat := 4983230072969 + 3 ^ 40 * 57022 * 2
def baseEnd_57022 : Nat := 8675464853564780700079

theorem tailTrace_57022 : CollatzResearch.WordTrace tailWord_57022 prefixEnd_57022 8675464853564780700079 := by
  unfold tailWord_57022
  simp only [CollatzResearch.WordTrace]
  refine ⟨259970399928313428422665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1386508799617671618254213 259970399928313428422665)
  ·
    refine ⟨194977799946235071316999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259970399928313428422665 194977799946235071316999)
    ·
      refine ⟨292466699919352606975499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194977799946235071316999 292466699919352606975499)
      ·
        refine ⟨438700049879028910463249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292466699919352606975499 438700049879028910463249)
        ·
          refine ⟨329025037409271682847437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438700049879028910463249 329025037409271682847437)
          ·
            refine ⟨123384389028476881067789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 329025037409271682847437 123384389028476881067789)
            ·
              refine ⟨46269145885678830400421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123384389028476881067789 46269145885678830400421)
              ·
                refine ⟨8675464853564780700079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46269145885678830400421 8675464853564780700079)
                ·
                  rfl

theorem cell20_57022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_57022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57022 prefixEnd_57022 := by exact prefixLift 57022
  have htrace : WordTrace (prefixWord ++ tailWord_57022) baseStart_57022 baseEnd_57022 := by
    simpa [prefixWord, tailWord_57022, baseEnd_57022] using wordTrace_append hprefix tailTrace_57022
  have hstable : (prefixWord ++ tailWord_57022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57022).length < 2 ^ (prefixWord ++ tailWord_57022).sum := by decide
  have hdescent : baseEnd_57022 < baseStart_57022 := by decide
  rcases family_descends (prefixWord ++ tailWord_57022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57050 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_57050 : Nat := 118140960795 + 57050 * 2 ^ 59
def prefixEnd_57050 : Nat := 4983230072969 + 3 ^ 40 * 57050 * 2
def baseEnd_57050 : Nat := 26039174523650689166789

theorem tailTrace_57050 : CollatzResearch.WordTrace tailWord_57050 prefixEnd_57050 26039174523650689166789 := by
  unfold tailWord_57050
  simp only [CollatzResearch.WordTrace]
  refine ⟨520196110831267052350151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1387189628883378806267069 520196110831267052350151)
  ·
    refine ⟨780294166246900578525227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 520196110831267052350151 780294166246900578525227)
    ·
      refine ⟨1170441249370350867787841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780294166246900578525227 1170441249370350867787841)
      ·
        refine ⟨877830937027763150840881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1170441249370350867787841 877830937027763150840881)
        ·
          refine ⟨658373202770822363130661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 877830937027763150840881 658373202770822363130661)
          ·
            refine ⟨123444975519529193086999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 658373202770822363130661 123444975519529193086999)
            ·
              refine ⟨185167463279293789630499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123444975519529193086999 185167463279293789630499)
              ·
                refine ⟨277751194918940684445749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185167463279293789630499 277751194918940684445749)
                ·
                  refine ⟨26039174523650689166789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 277751194918940684445749 26039174523650689166789)
                  ·
                    rfl

theorem cell20_57050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_57050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57050 prefixEnd_57050 := by exact prefixLift 57050
  have htrace : WordTrace (prefixWord ++ tailWord_57050) baseStart_57050 baseEnd_57050 := by
    simpa [prefixWord, tailWord_57050, baseEnd_57050] using wordTrace_append hprefix tailTrace_57050
  have hstable : (prefixWord ++ tailWord_57050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57050).length < 2 ^ (prefixWord ++ tailWord_57050).sum := by decide
  have hdescent : baseEnd_57050 < baseStart_57050 := by decide
  rcases family_descends (prefixWord ++ tailWord_57050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57063 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 3]
def baseStart_57063 : Nat := 118140960795 + 57063 * 2 ^ 59
def prefixEnd_57063 : Nat := 4983230072969 + 3 ^ 40 * 57063 * 2
def baseEnd_57063 : Nat := 26045108077880421733403

theorem tailTrace_57063 : CollatzResearch.WordTrace tailWord_57063 prefixEnd_57063 26045108077880421733403 := by
  unfold tailWord_57063
  simp only [CollatzResearch.WordTrace]
  refine ⟨2081258592277971429623843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1387505728185314286415895 2081258592277971429623843)
  ·
    refine ⟨3121887888416957144435765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2081258592277971429623843 3121887888416957144435765)
    ·
      refine ⟨292676989539089732290853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3121887888416957144435765 292676989539089732290853)
      ·
        refine ⟨54876935538579324804535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 292676989539089732290853 54876935538579324804535)
        ·
          refine ⟨82315403307868987206803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54876935538579324804535 82315403307868987206803)
          ·
            refine ⟨123473104961803480810205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82315403307868987206803 123473104961803480810205)
            ·
              refine ⟨46302414360676305303827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123473104961803480810205 46302414360676305303827)
              ·
                refine ⟨69453621541014457955741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46302414360676305303827 69453621541014457955741)
                ·
                  refine ⟨26045108077880421733403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69453621541014457955741 26045108077880421733403)
                  ·
                    rfl

theorem cell20_57063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 3].length) (baseStart_57063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57063 prefixEnd_57063 := by exact prefixLift 57063
  have htrace : WordTrace (prefixWord ++ tailWord_57063) baseStart_57063 baseEnd_57063 := by
    simpa [prefixWord, tailWord_57063, baseEnd_57063] using wordTrace_append hprefix tailTrace_57063
  have hstable : (prefixWord ++ tailWord_57063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57063).length < 2 ^ (prefixWord ++ tailWord_57063).sum := by decide
  have hdescent : baseEnd_57063 < baseStart_57063 := by decide
  rcases family_descends (prefixWord ++ tailWord_57063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57102 : List Nat := [4, 1, 1, 2, 1, 1, 10]
def baseStart_57102 : Nat := 118140960795 + 57102 * 2 ^ 59
def prefixEnd_57102 : Nat := 4983230072969 + 3 ^ 40 * 57102 * 2
def baseEnd_57102 : Nat := 2895878748952179937027

theorem tailTrace_57102 : CollatzResearch.WordTrace tailWord_57102 prefixEnd_57102 2895878748952179937027 := by
  unfold tailWord_57102
  simp only [CollatzResearch.WordTrace]
  refine ⟨260335129892085136286695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1388454026091120726862373 260335129892085136286695)
  ·
    refine ⟨390502694838127704430043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260335129892085136286695 390502694838127704430043)
    ·
      refine ⟨585754042257191556645065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390502694838127704430043 585754042257191556645065)
      ·
        refine ⟨439315531692893667483799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 585754042257191556645065 439315531692893667483799)
        ·
          refine ⟨658973297539340501225699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439315531692893667483799 658973297539340501225699)
          ·
            refine ⟨988459946309010751838549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 658973297539340501225699 988459946309010751838549)
            ·
              refine ⟨2895878748952179937027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 988459946309010751838549 2895878748952179937027)
              ·
                rfl

theorem cell20_57102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 10].length) (baseStart_57102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57102 prefixEnd_57102 := by exact prefixLift 57102
  have htrace : WordTrace (prefixWord ++ tailWord_57102) baseStart_57102 baseEnd_57102 := by
    simpa [prefixWord, tailWord_57102, baseEnd_57102] using wordTrace_append hprefix tailTrace_57102
  have hstable : (prefixWord ++ tailWord_57102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57102).length < 2 ^ (prefixWord ++ tailWord_57102).sum := by decide
  have hdescent : baseEnd_57102 < baseStart_57102 := by decide
  rcases family_descends (prefixWord ++ tailWord_57102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57112 : List Nat := [2, 1, 2, 3, 1, 1, 2, 6, 2]
def baseStart_57112 : Nat := 118140960795 + 57112 * 2 ^ 59
def prefixEnd_57112 : Nat := 4983230072969 + 3 ^ 40 * 57112 * 2
def baseEnd_57112 : Nat := 26067473013054029099869

theorem tailTrace_57112 : CollatzResearch.WordTrace tailWord_57112 prefixEnd_57112 26067473013054029099869 := by
  unfold tailWord_57112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041522884550226399078795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1388697179400301865438393 1041522884550226399078795)
  ·
    refine ⟨1562284326825339598618193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1041522884550226399078795 1562284326825339598618193)
    ·
      refine ⟨1171713245119004698963645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1562284326825339598618193 1171713245119004698963645)
      ·
        refine ⟨439392466919626762111367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1171713245119004698963645 439392466919626762111367)
        ·
          refine ⟨659088700379440143167051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439392466919626762111367 659088700379440143167051)
          ·
            refine ⟨988633050569160214750577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659088700379440143167051 988633050569160214750577)
            ·
              refine ⟨741474787926870161062933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988633050569160214750577 741474787926870161062933)
              ·
                refine ⟨34756630684072038799825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 741474787926870161062933 34756630684072038799825)
                ·
                  refine ⟨26067473013054029099869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34756630684072038799825 26067473013054029099869)
                  ·
                    rfl

theorem cell20_57112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 2].length) (baseStart_57112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57112 prefixEnd_57112 := by exact prefixLift 57112
  have htrace : WordTrace (prefixWord ++ tailWord_57112) baseStart_57112 baseEnd_57112 := by
    simpa [prefixWord, tailWord_57112, baseEnd_57112] using wordTrace_append hprefix tailTrace_57112
  have hstable : (prefixWord ++ tailWord_57112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57112).length < 2 ^ (prefixWord ++ tailWord_57112).sum := by decide
  have hdescent : baseEnd_57112 < baseStart_57112 := by decide
  rcases family_descends (prefixWord ++ tailWord_57112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57188 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 4]
def baseStart_57188 : Nat := 118140960795 + 57188 * 2 ^ 59
def prefixEnd_57188 : Nat := 4983230072969 + 3 ^ 40 * 57188 * 2
def baseEnd_57188 : Nat := 26102161483935542566225

theorem tailTrace_57188 : CollatzResearch.WordTrace tailWord_57188 prefixEnd_57188 26102161483935542566225 := by
  unfold tailWord_57188
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042908858412558888962109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1390545144550078518616145 1042908858412558888962109)
  ·
    refine ⟨391090821904709583360791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1042908858412558888962109 391090821904709583360791)
    ·
      refine ⟨586636232857064375041187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391090821904709583360791 586636232857064375041187)
      ·
        refine ⟨879954349285596562561781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586636232857064375041187 879954349285596562561781)
        ·
          refine ⟨82495720245524677740167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 879954349285596562561781 82495720245524677740167)
          ·
            refine ⟨123743580368287016610251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82495720245524677740167 123743580368287016610251)
            ·
              refine ⟨185615370552430524915377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123743580368287016610251 185615370552430524915377)
              ·
                refine ⟨139211527914322893686533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185615370552430524915377 139211527914322893686533)
                ·
                  refine ⟨26102161483935542566225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139211527914322893686533 26102161483935542566225)
                  ·
                    rfl

theorem cell20_57188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_57188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57188 prefixEnd_57188 := by exact prefixLift 57188
  have htrace : WordTrace (prefixWord ++ tailWord_57188) baseStart_57188 baseEnd_57188 := by
    simpa [prefixWord, tailWord_57188, baseEnd_57188] using wordTrace_append hprefix tailTrace_57188
  have hstable : (prefixWord ++ tailWord_57188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57188).length < 2 ^ (prefixWord ++ tailWord_57188).sum := by decide
  have hdescent : baseEnd_57188 < baseStart_57188 := by decide
  rcases family_descends (prefixWord ++ tailWord_57188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57205 : List Nat := [1, 3, 4, 1, 1, 1, 4, 3, 2]
def baseStart_57205 : Nat := 118140960795 + 57205 * 2 ^ 59
def prefixEnd_57205 : Nat := 4983230072969 + 3 ^ 40 * 57205 * 2
def baseEnd_57205 : Nat := 26109920747159038999489

theorem tailTrace_57205 : CollatzResearch.WordTrace tailWord_57205 prefixEnd_57205 26109920747159038999489 := by
  unfold tailWord_57205
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086437757763529681293069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1390958505175686454195379 2086437757763529681293069)
  ·
    refine ⟨782414159161323630484901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2086437757763529681293069 782414159161323630484901)
    ·
      refine ⟨146702654842748180715919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 782414159161323630484901 146702654842748180715919)
      ·
        refine ⟨220053982264122271073879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146702654842748180715919 220053982264122271073879)
        ·
          refine ⟨330080973396183406610819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220053982264122271073879 330080973396183406610819)
          ·
            refine ⟨495121460094275109916229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330080973396183406610819 495121460094275109916229)
            ·
              refine ⟨92835273767676583109293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 495121460094275109916229 92835273767676583109293)
              ·
                refine ⟨34813227662878718665985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92835273767676583109293 34813227662878718665985)
                ·
                  refine ⟨26109920747159038999489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34813227662878718665985 26109920747159038999489)
                  ·
                    rfl

theorem cell20_57205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_57205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57205 prefixEnd_57205 := by exact prefixLift 57205
  have htrace : WordTrace (prefixWord ++ tailWord_57205) baseStart_57205 baseEnd_57205 := by
    simpa [prefixWord, tailWord_57205, baseEnd_57205] using wordTrace_append hprefix tailTrace_57205
  have hstable : (prefixWord ++ tailWord_57205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57205).length < 2 ^ (prefixWord ++ tailWord_57205).sum := by decide
  have hdescent : baseEnd_57205 < baseStart_57205 := by decide
  rcases family_descends (prefixWord ++ tailWord_57205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57219 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 3]
def baseStart_57219 : Nat := 118140960795 + 57219 * 2 ^ 59
def prefixEnd_57219 : Nat := 4983230072969 + 3 ^ 40 * 57219 * 2
def baseEnd_57219 : Nat := 26116310728637212532765

theorem tailTrace_57219 : CollatzResearch.WordTrace tailWord_57219 prefixEnd_57219 26116310728637212532765 := by
  unfold tailWord_57219
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086948379712810072302711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1391298919808540048201807 2086948379712810072302711)
  ·
    refine ⟨3130422569569215108454067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2086948379712810072302711 3130422569569215108454067)
    ·
      refine ⟨4695633854353822662681101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3130422569569215108454067 4695633854353822662681101)
      ·
        refine ⟨1760862695382683498505413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4695633854353822662681101 1760862695382683498505413)
        ·
          refine ⟨330161755384253155969765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1760862695382683498505413 330161755384253155969765)
          ·
            refine ⟨61905329134547466744331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330161755384253155969765 61905329134547466744331)
            ·
              refine ⟨92857993701821200116497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61905329134547466744331 92857993701821200116497)
              ·
                refine ⟨69643495276365900087373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92857993701821200116497 69643495276365900087373)
                ·
                  refine ⟨26116310728637212532765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69643495276365900087373 26116310728637212532765)
                  ·
                    rfl

theorem cell20_57219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 3].length) (baseStart_57219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57219 prefixEnd_57219 := by exact prefixLift 57219
  have htrace : WordTrace (prefixWord ++ tailWord_57219) baseStart_57219 baseEnd_57219 := by
    simpa [prefixWord, tailWord_57219, baseEnd_57219] using wordTrace_append hprefix tailTrace_57219
  have hstable : (prefixWord ++ tailWord_57219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57219).length < 2 ^ (prefixWord ++ tailWord_57219).sum := by decide
  have hdescent : baseEnd_57219 < baseStart_57219 := by decide
  rcases family_descends (prefixWord ++ tailWord_57219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57236 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 3]
def baseStart_57236 : Nat := 118140960795 + 57236 * 2 ^ 59
def prefixEnd_57236 : Nat := 4983230072969 + 3 ^ 40 * 57236 * 2
def baseEnd_57236 : Nat := 26124069991860708966029

theorem tailTrace_57236 : CollatzResearch.WordTrace tailWord_57236 prefixEnd_57236 26124069991860708966029 := by
  unfold tailWord_57236
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043784210325610987835781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1391712280434147983781041 1043784210325610987835781)
  ·
    refine ⟨195709539436052060219209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1043784210325610987835781 195709539436052060219209)
    ·
      refine ⟨146782154577039045164407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195709539436052060219209 146782154577039045164407)
      ·
        refine ⟨220173231865558567746611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146782154577039045164407 220173231865558567746611)
        ·
          refine ⟨330259847798337851619917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220173231865558567746611 330259847798337851619917)
          ·
            refine ⟨123847442924376694357469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330259847798337851619917 123847442924376694357469)
            ·
              refine ⟨46442791096641260384051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123847442924376694357469 46442791096641260384051)
              ·
                refine ⟨69664186644961890576077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46442791096641260384051 69664186644961890576077)
                ·
                  refine ⟨26124069991860708966029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69664186644961890576077 26124069991860708966029)
                  ·
                    rfl

theorem cell20_57236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_57236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57236 prefixEnd_57236 := by exact prefixLift 57236
  have htrace : WordTrace (prefixWord ++ tailWord_57236) baseStart_57236 baseEnd_57236 := by
    simpa [prefixWord, tailWord_57236, baseEnd_57236] using wordTrace_append hprefix tailTrace_57236
  have hstable : (prefixWord ++ tailWord_57236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57236).length < 2 ^ (prefixWord ++ tailWord_57236).sum := by decide
  have hdescent : baseEnd_57236 < baseStart_57236 := by decide
  rcases family_descends (prefixWord ++ tailWord_57236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57246 : List Nat := [4, 3, 1, 3, 1, 2, 2, 4]
def baseStart_57246 : Nat := 118140960795 + 57246 * 2 ^ 59
def prefixEnd_57246 : Nat := 4983230072969 + 3 ^ 40 * 57246 * 2
def baseEnd_57246 : Nat := 8709544754781706210885

theorem tailTrace_57246 : CollatzResearch.WordTrace tailWord_57246 prefixEnd_57246 8709544754781706210885 := by
  unfold tailWord_57246
  simp only [CollatzResearch.WordTrace]
  refine ⟨260991643826874210441949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1391955433743329122357061 260991643826874210441949)
  ·
    refine ⟨97871866435077828915731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 260991643826874210441949 97871866435077828915731)
    ·
      refine ⟨146807799652616743373597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97871866435077828915731 146807799652616743373597)
      ·
        refine ⟨55052924869731278765099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146807799652616743373597 55052924869731278765099)
        ·
          refine ⟨82579387304596918147649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55052924869731278765099 82579387304596918147649)
          ·
            refine ⟨61934540478447688610737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82579387304596918147649 61934540478447688610737)
            ·
              refine ⟨46450905358835766458053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61934540478447688610737 46450905358835766458053)
              ·
                refine ⟨8709544754781706210885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46450905358835766458053 8709544754781706210885)
                ·
                  rfl

theorem cell20_57246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_57246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57246 prefixEnd_57246 := by exact prefixLift 57246
  have htrace : WordTrace (prefixWord ++ tailWord_57246) baseStart_57246 baseEnd_57246 := by
    simpa [prefixWord, tailWord_57246, baseEnd_57246] using wordTrace_append hprefix tailTrace_57246
  have hstable : (prefixWord ++ tailWord_57246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57246).length < 2 ^ (prefixWord ++ tailWord_57246).sum := by decide
  have hdescent : baseEnd_57246 < baseStart_57246 := by decide
  rcases family_descends (prefixWord ++ tailWord_57246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57256 : List Nat := [2, 1, 6, 2, 2, 1, 1, 3, 2]
def baseStart_57256 : Nat := 118140960795 + 57256 * 2 ^ 59
def prefixEnd_57256 : Nat := 4983230072969 + 3 ^ 40 * 57256 * 2
def baseEnd_57256 : Nat := 26133198536829528299281

theorem tailTrace_57256 : CollatzResearch.WordTrace tailWord_57256 prefixEnd_57256 26133198536829528299281 := by
  unfold tailWord_57256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044148940289382695699811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1392198587052510260933081 1044148940289382695699811)
  ·
    refine ⟨1566223410434074043549717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1044148940289382695699811 1566223410434074043549717)
    ·
      refine ⟨73416722364097220791393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1566223410434074043549717 73416722364097220791393)
      ·
        refine ⟨55062541773072915593545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73416722364097220791393 55062541773072915593545)
        ·
          refine ⟨41296906329804686695159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55062541773072915593545 41296906329804686695159)
          ·
            refine ⟨61945359494707030042739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41296906329804686695159 61945359494707030042739)
            ·
              refine ⟨92918039242060545064109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61945359494707030042739 92918039242060545064109)
              ·
                refine ⟨34844264715772704399041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92918039242060545064109 34844264715772704399041)
                ·
                  refine ⟨26133198536829528299281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34844264715772704399041 26133198536829528299281)
                  ·
                    rfl

theorem cell20_57256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 3, 2].length) (baseStart_57256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57256 prefixEnd_57256 := by exact prefixLift 57256
  have htrace : WordTrace (prefixWord ++ tailWord_57256) baseStart_57256 baseEnd_57256 := by
    simpa [prefixWord, tailWord_57256, baseEnd_57256] using wordTrace_append hprefix tailTrace_57256
  have hstable : (prefixWord ++ tailWord_57256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57256).length < 2 ^ (prefixWord ++ tailWord_57256).sum := by decide
  have hdescent : baseEnd_57256 < baseStart_57256 := by decide
  rcases family_descends (prefixWord ++ tailWord_57256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57278 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_57278 : Nat := 118140960795 + 57278 * 2 ^ 59
def prefixEnd_57278 : Nat := 4983230072969 + 3 ^ 40 * 57278 * 2
def baseEnd_57278 : Nat := 26143239936295229565857

theorem tailTrace_57278 : CollatzResearch.WordTrace tailWord_57278 prefixEnd_57278 26143239936295229565857 := by
  unfold tailWord_57278
  simp only [CollatzResearch.WordTrace]
  refine ⟨261137535812382893587561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1392733524332708765800325 261137535812382893587561)
  ·
    refine ⟨195853151859287170190671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261137535812382893587561 195853151859287170190671)
    ·
      refine ⟨293779727788930755286007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195853151859287170190671 293779727788930755286007)
      ·
        refine ⟨440669591683396132929011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293779727788930755286007 440669591683396132929011)
        ·
          refine ⟨661004387525094199393517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440669591683396132929011 661004387525094199393517)
          ·
            refine ⟨247876645321910324772569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661004387525094199393517 247876645321910324772569)
            ·
              refine ⟨185907483991432743579427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247876645321910324772569 185907483991432743579427)
              ·
                refine ⟨278861225987149115369141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 185907483991432743579427 278861225987149115369141)
                ·
                  refine ⟨26143239936295229565857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 278861225987149115369141 26143239936295229565857)
                  ·
                    rfl

theorem cell20_57278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_57278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57278 prefixEnd_57278 := by exact prefixLift 57278
  have htrace : WordTrace (prefixWord ++ tailWord_57278) baseStart_57278 baseEnd_57278 := by
    simpa [prefixWord, tailWord_57278, baseEnd_57278] using wordTrace_append hprefix tailTrace_57278
  have hstable : (prefixWord ++ tailWord_57278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57278).length < 2 ^ (prefixWord ++ tailWord_57278).sum := by decide
  have hdescent : baseEnd_57278 < baseStart_57278 := by decide
  rcases family_descends (prefixWord ++ tailWord_57278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57292 : List Nat := [2, 2, 1, 4, 1, 2, 1, 7]
def baseStart_57292 : Nat := 118140960795 + 57292 * 2 ^ 59
def prefixEnd_57292 : Nat := 4983230072969 + 3 ^ 40 * 57292 * 2
def baseEnd_57292 : Nat := 8716543305924467699711

theorem tailTrace_57292 : CollatzResearch.WordTrace tailWord_57292 prefixEnd_57292 8716543305924467699711 := by
  unfold tailWord_57292
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044805454224171769855065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1393073938965562359806753 1044805454224171769855065)
  ·
    refine ⟨783604090668128827391299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1044805454224171769855065 783604090668128827391299)
    ·
      refine ⟨1175406136002193241086949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783604090668128827391299 1175406136002193241086949)
      ·
        refine ⟨220388650500411232703803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1175406136002193241086949 220388650500411232703803)
        ·
          refine ⟨330582975750616849055705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220388650500411232703803 330582975750616849055705)
          ·
            refine ⟨247937231812962636791779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330582975750616849055705 247937231812962636791779)
            ·
              refine ⟨371905847719443955187669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247937231812962636791779 371905847719443955187669)
              ·
                refine ⟨8716543305924467699711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 371905847719443955187669 8716543305924467699711)
                ·
                  rfl

theorem cell20_57292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_57292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57292 prefixEnd_57292 := by exact prefixLift 57292
  have htrace : WordTrace (prefixWord ++ tailWord_57292) baseStart_57292 baseEnd_57292 := by
    simpa [prefixWord, tailWord_57292, baseEnd_57292] using wordTrace_append hprefix tailTrace_57292
  have hstable : (prefixWord ++ tailWord_57292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57292).length < 2 ^ (prefixWord ++ tailWord_57292).sum := by decide
  have hdescent : baseEnd_57292 < baseStart_57292 := by decide
  rcases family_descends (prefixWord ++ tailWord_57292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57340 : List Nat := [2, 2, 2, 1, 2, 2, 3, 4, 2]
def baseStart_57340 : Nat := 118140960795 + 57340 * 2 ^ 59
def prefixEnd_57340 : Nat := 4983230072969 + 3 ^ 40 * 57340 * 2
def baseEnd_57340 : Nat := 26171538425698569498937

theorem tailTrace_57340 : CollatzResearch.WordTrace tailWord_57340 prefixEnd_57340 26171538425698569498937 := by
  unfold tailWord_57340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045680806137223868728737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1394241074849631824971649 1045680806137223868728737)
  ·
    refine ⟨784260604602917901546553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1045680806137223868728737 784260604602917901546553)
    ·
      refine ⟨588195453452188426159915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 784260604602917901546553 588195453452188426159915)
      ·
        refine ⟨882293180178282639239873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 588195453452188426159915 882293180178282639239873)
        ·
          refine ⟨661719885133711979429905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 882293180178282639239873 661719885133711979429905)
          ·
            refine ⟨496289913850283984572429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661719885133711979429905 496289913850283984572429)
            ·
              refine ⟨186108717693856494214661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 496289913850283984572429 186108717693856494214661)
              ·
                refine ⟨34895384567598092665249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186108717693856494214661 34895384567598092665249)
                ·
                  refine ⟨26171538425698569498937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34895384567598092665249 26171538425698569498937)
                  ·
                    rfl

theorem cell20_57340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_57340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57340 prefixEnd_57340 := by exact prefixLift 57340
  have htrace : WordTrace (prefixWord ++ tailWord_57340) baseStart_57340 baseEnd_57340 := by
    simpa [prefixWord, tailWord_57340, baseEnd_57340] using wordTrace_append hprefix tailTrace_57340
  have hstable : (prefixWord ++ tailWord_57340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57340).length < 2 ^ (prefixWord ++ tailWord_57340).sum := by decide
  have hdescent : baseEnd_57340 < baseStart_57340 := by decide
  rcases family_descends (prefixWord ++ tailWord_57340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57375 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_57375 : Nat := 118140960795 + 57375 * 2 ^ 59
def prefixEnd_57375 : Nat := 4983230072969 + 3 ^ 40 * 57375 * 2
def baseEnd_57375 : Nat := 26187513379394003332127

theorem tailTrace_57375 : CollatzResearch.WordTrace tailWord_57375 prefixEnd_57375 26187513379394003332127 := by
  unfold tailWord_57375
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092638167147648714981579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1395092111431765809987719 2092638167147648714981579)
  ·
    refine ⟨3138957250721473072472369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2092638167147648714981579 3138957250721473072472369)
    ·
      refine ⟨2354217938041104804354277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3138957250721473072472369 2354217938041104804354277)
      ·
        refine ⟨441415863382707150816427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2354217938041104804354277 441415863382707150816427)
        ·
          refine ⟨662123795074060726224641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441415863382707150816427 662123795074060726224641)
          ·
            refine ⟨496592846305545544668481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 662123795074060726224641 496592846305545544668481)
            ·
              refine ⟨372444634729159158501361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 496592846305545544668481 372444634729159158501361)
              ·
                refine ⟨279333476046869368876021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372444634729159158501361 279333476046869368876021)
                ·
                  refine ⟨26187513379394003332127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 279333476046869368876021 26187513379394003332127)
                  ·
                    rfl

theorem cell20_57375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_57375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57375 prefixEnd_57375 := by exact prefixLift 57375
  have htrace : WordTrace (prefixWord ++ tailWord_57375) baseStart_57375 baseEnd_57375 := by
    simpa [prefixWord, tailWord_57375, baseEnd_57375] using wordTrace_append hprefix tailTrace_57375
  have hstable : (prefixWord ++ tailWord_57375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57375).length < 2 ^ (prefixWord ++ tailWord_57375).sum := by decide
  have hdescent : baseEnd_57375 < baseStart_57375 := by decide
  rcases family_descends (prefixWord ++ tailWord_57375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57392 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 3]
def baseStart_57392 : Nat := 118140960795 + 57392 * 2 ^ 59
def prefixEnd_57392 : Nat := 4983230072969 + 3 ^ 40 * 57392 * 2
def baseEnd_57392 : Nat := 26195272642617499765391

theorem tailTrace_57392 : CollatzResearch.WordTrace tailWord_57392 prefixEnd_57392 26195272642617499765391 := by
  unfold tailWord_57392
  simp only [CollatzResearch.WordTrace]
  refine ⟨1046629104043030309175215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1395505472057373745566953 1046629104043030309175215)
  ·
    refine ⟨1569943656064545463762823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1046629104043030309175215 1569943656064545463762823)
    ·
      refine ⟨2354915484096818195644235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1569943656064545463762823 2354915484096818195644235)
      ·
        refine ⟨3532373226145227293466353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354915484096818195644235 3532373226145227293466353)
        ·
          refine ⟨2649279919608920470099765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3532373226145227293466353 2649279919608920470099765)
          ·
            refine ⟨248369992463336294071853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2649279919608920470099765 248369992463336294071853)
            ·
              refine ⟨93138747173751110276945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248369992463336294071853 93138747173751110276945)
              ·
                refine ⟨69854060380313332707709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93138747173751110276945 69854060380313332707709)
                ·
                  refine ⟨26195272642617499765391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69854060380313332707709 26195272642617499765391)
                  ·
                    rfl

theorem cell20_57392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_57392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57392 prefixEnd_57392 := by exact prefixLift 57392
  have htrace : WordTrace (prefixWord ++ tailWord_57392) baseStart_57392 baseEnd_57392 := by
    simpa [prefixWord, tailWord_57392, baseEnd_57392] using wordTrace_append hprefix tailTrace_57392
  have hstable : (prefixWord ++ tailWord_57392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57392).length < 2 ^ (prefixWord ++ tailWord_57392).sum := by decide
  have hdescent : baseEnd_57392 < baseStart_57392 := by decide
  rcases family_descends (prefixWord ++ tailWord_57392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57450 : List Nat := [3, 1, 3, 2, 3, 1, 3, 2, 2]
def baseStart_57450 : Nat := 118140960795 + 57450 * 2 ^ 59
def prefixEnd_57450 : Nat := 4983230072969 + 3 ^ 40 * 57450 * 2
def baseEnd_57450 : Nat := 26221745423027075831821

theorem tailTrace_57450 : CollatzResearch.WordTrace tailWord_57450 prefixEnd_57450 26221745423027075831821 := by
  unfold tailWord_57450
  simp only [CollatzResearch.WordTrace]
  refine ⟨523843410468984130990451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1396915761250624349307869 523843410468984130990451)
  ·
    refine ⟨785765115703476196485677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 523843410468984130990451 785765115703476196485677)
    ·
      refine ⟨294661918388803573682129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 785765115703476196485677 294661918388803573682129)
      ·
        refine ⟨220996438791602680261597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294661918388803573682129 220996438791602680261597)
        ·
          refine ⟨82873664546851005098099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220996438791602680261597 82873664546851005098099)
          ·
            refine ⟨124310496820276507647149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82873664546851005098099 124310496820276507647149)
            ·
              refine ⟨46616436307603690367681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124310496820276507647149 46616436307603690367681)
              ·
                refine ⟨34962327230702767775761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46616436307603690367681 34962327230702767775761)
                ·
                  refine ⟨26221745423027075831821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34962327230702767775761 26221745423027075831821)
                  ·
                    rfl

theorem cell20_57450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_57450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57450 prefixEnd_57450 := by exact prefixLift 57450
  have htrace : WordTrace (prefixWord ++ tailWord_57450) baseStart_57450 baseEnd_57450 := by
    simpa [prefixWord, tailWord_57450, baseEnd_57450] using wordTrace_append hprefix tailTrace_57450
  have hstable : (prefixWord ++ tailWord_57450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57450).length < 2 ^ (prefixWord ++ tailWord_57450).sum := by decide
  have hdescent : baseEnd_57450 < baseStart_57450 := by decide
  rcases family_descends (prefixWord ++ tailWord_57450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57468 : List Nat := [2, 2, 2, 1, 1, 5, 1, 3, 3]
def baseStart_57468 : Nat := 118140960795 + 57468 * 2 ^ 59
def prefixEnd_57468 : Nat := 4983230072969 + 3 ^ 40 * 57468 * 2
def baseEnd_57468 : Nat := 26229961113499013231747

theorem tailTrace_57468 : CollatzResearch.WordTrace tailWord_57468 prefixEnd_57468 26229961113499013231747 := by
  unfold tailWord_57468
  simp only [CollatzResearch.WordTrace]
  refine ⟨1048015077905362799058529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1397353437207150398744705 1048015077905362799058529)
  ·
    refine ⟨786011308429022099293897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1048015077905362799058529 786011308429022099293897)
    ·
      refine ⟨589508481321766574470423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 786011308429022099293897 589508481321766574470423)
      ·
        refine ⟨884262721982649861705635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589508481321766574470423 884262721982649861705635)
        ·
          refine ⟨1326394082973974792558453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884262721982649861705635 1326394082973974792558453)
          ·
            refine ⟨124349445278810136802355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1326394082973974792558453 124349445278810136802355)
            ·
              refine ⟨186524167918215205203533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124349445278810136802355 186524167918215205203533)
              ·
                refine ⟨69946562969330701951325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186524167918215205203533 69946562969330701951325)
                ·
                  refine ⟨26229961113499013231747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69946562969330701951325 26229961113499013231747)
                  ·
                    rfl

theorem cell20_57468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_57468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57468 prefixEnd_57468 := by exact prefixLift 57468
  have htrace : WordTrace (prefixWord ++ tailWord_57468) baseStart_57468 baseEnd_57468 := by
    simpa [prefixWord, tailWord_57468, baseEnd_57468] using wordTrace_append hprefix tailTrace_57468
  have hstable : (prefixWord ++ tailWord_57468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57468).length < 2 ^ (prefixWord ++ tailWord_57468).sum := by decide
  have hdescent : baseEnd_57468 < baseStart_57468 := by decide
  rcases family_descends (prefixWord ++ tailWord_57468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57482 : List Nat := [3, 1, 2, 3, 1, 2, 2, 6]
def baseStart_57482 : Nat := 118140960795 + 57482 * 2 ^ 59
def prefixEnd_57482 : Nat := 4983230072969 + 3 ^ 40 * 57482 * 2
def baseEnd_57482 : Nat := 8745450364992395588341

theorem tailTrace_57482 : CollatzResearch.WordTrace tailWord_57482 prefixEnd_57482 8745450364992395588341 := by
  unfold tailWord_57482
  simp only [CollatzResearch.WordTrace]
  refine ⟨524135194440001497281675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1397693851840003992751133 524135194440001497281675)
  ·
    refine ⟨786202791660002245922513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524135194440001497281675 786202791660002245922513)
    ·
      refine ⟨589652093745001684441885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 786202791660002245922513 589652093745001684441885)
      ·
        refine ⟨221119535154375631665707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589652093745001684441885 221119535154375631665707)
        ·
          refine ⟨331679302731563447498561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221119535154375631665707 331679302731563447498561)
          ·
            refine ⟨248759477048672585623921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331679302731563447498561 248759477048672585623921)
            ·
              refine ⟨186569607786504439217941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248759477048672585623921 186569607786504439217941)
              ·
                refine ⟨8745450364992395588341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186569607786504439217941 8745450364992395588341)
                ·
                  rfl

theorem cell20_57482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_57482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57482 prefixEnd_57482 := by exact prefixLift 57482
  have htrace : WordTrace (prefixWord ++ tailWord_57482) baseStart_57482 baseEnd_57482 := by
    simpa [prefixWord, tailWord_57482, baseEnd_57482] using wordTrace_append hprefix tailTrace_57482
  have hstable : (prefixWord ++ tailWord_57482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57482).length < 2 ^ (prefixWord ++ tailWord_57482).sum := by decide
  have hdescent : baseEnd_57482 < baseStart_57482 := by decide
  rcases family_descends (prefixWord ++ tailWord_57482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57502 : List Nat := [4, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_57502 : Nat := 118140960795 + 57502 * 2 ^ 59
def prefixEnd_57502 : Nat := 4983230072969 + 3 ^ 40 * 57502 * 2
def baseEnd_57502 : Nat := 26245479639946006098275

theorem tailTrace_57502 : CollatzResearch.WordTrace tailWord_57502 prefixEnd_57502 26245479639946006098275 := by
  unfold tailWord_57502
  simp only [CollatzResearch.WordTrace]
  refine ⟨262158779710943675606845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1398180158458366269903173 262158779710943675606845)
  ·
    refine ⟨98309542391603878352567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262158779710943675606845 98309542391603878352567)
    ·
      refine ⟨147464313587405817528851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98309542391603878352567 147464313587405817528851)
      ·
        refine ⟨221196470381108726293277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147464313587405817528851 221196470381108726293277)
        ·
          refine ⟨82948676392915772359979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221196470381108726293277 82948676392915772359979)
          ·
            refine ⟨124423014589373658539969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82948676392915772359979 124423014589373658539969)
            ·
              refine ⟨93317260942030243904977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124423014589373658539969 93317260942030243904977)
              ·
                refine ⟨69987945706522682928733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93317260942030243904977 69987945706522682928733)
                ·
                  refine ⟨26245479639946006098275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69987945706522682928733 26245479639946006098275)
                  ·
                    rfl

theorem cell20_57502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_57502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57502 prefixEnd_57502 := by exact prefixLift 57502
  have htrace : WordTrace (prefixWord ++ tailWord_57502) baseStart_57502 baseEnd_57502 := by
    simpa [prefixWord, tailWord_57502, baseEnd_57502] using wordTrace_append hprefix tailTrace_57502
  have hstable : (prefixWord ++ tailWord_57502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57502).length < 2 ^ (prefixWord ++ tailWord_57502).sum := by decide
  have hdescent : baseEnd_57502 < baseStart_57502 := by decide
  rcases family_descends (prefixWord ++ tailWord_57502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57541 : List Nat := [1, 3, 1, 1, 1, 1, 4, 8]
def baseStart_57541 : Nat := 118140960795 + 57541 * 2 ^ 59
def prefixEnd_57541 : Nat := 4983230072969 + 3 ^ 40 * 57541 * 2
def baseEnd_57541 : Nat := 8754426767545067932705

theorem tailTrace_57541 : CollatzResearch.WordTrace tailWord_57541 prefixEnd_57541 8754426767545067932705 := by
  unfold tailWord_57541
  simp only [CollatzResearch.WordTrace]
  refine ⟨2098692684546259065524477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1399128456364172710349651 2098692684546259065524477)
  ·
    refine ⟨787009756704847149571679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2098692684546259065524477 787009756704847149571679)
    ·
      refine ⟨1180514635057270724357519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 787009756704847149571679 1180514635057270724357519)
      ·
        refine ⟨1770771952585906086536279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1180514635057270724357519 1770771952585906086536279)
        ·
          refine ⟨2656157928878859129804419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770771952585906086536279 2656157928878859129804419)
          ·
            refine ⟨3984236893318288694706629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2656157928878859129804419 3984236893318288694706629)
            ·
              refine ⟨747044417497179130257493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3984236893318288694706629 747044417497179130257493)
              ·
                refine ⟨8754426767545067932705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 747044417497179130257493 8754426767545067932705)
                ·
                  rfl

theorem cell20_57541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_57541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57541 prefixEnd_57541 := by exact prefixLift 57541
  have htrace : WordTrace (prefixWord ++ tailWord_57541) baseStart_57541 baseEnd_57541 := by
    simpa [prefixWord, tailWord_57541, baseEnd_57541] using wordTrace_append hprefix tailTrace_57541
  have hstable : (prefixWord ++ tailWord_57541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57541).length < 2 ^ (prefixWord ++ tailWord_57541).sum := by decide
  have hdescent : baseEnd_57541 < baseStart_57541 := by decide
  rcases family_descends (prefixWord ++ tailWord_57541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57579 : List Nat := [1, 1, 1, 1, 2, 5, 2, 7]
def baseStart_57579 : Nat := 118140960795 + 57579 * 2 ^ 59
def prefixEnd_57579 : Nat := 4983230072969 + 3 ^ 40 * 57579 * 2
def baseEnd_57579 : Nat := 8760208179358653510431

theorem tailTrace_57579 : CollatzResearch.WordTrace tailWord_57579 prefixEnd_57579 8760208179358653510431 := by
  unfold tailWord_57579
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100078658408591555407791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1400052438939061036938527 2100078658408591555407791)
  ·
    refine ⟨3150117987612887333111687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2100078658408591555407791 3150117987612887333111687)
    ·
      refine ⟨4725176981419330999667531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150117987612887333111687 4725176981419330999667531)
      ·
        refine ⟨7087765472128996499501297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4725176981419330999667531 7087765472128996499501297)
        ·
          refine ⟨5315824104096747374625973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7087765472128996499501297 5315824104096747374625973)
          ·
            refine ⟨498358509759070066371185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5315824104096747374625973 498358509759070066371185)
            ·
              refine ⟨373768882319302549778389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498358509759070066371185 373768882319302549778389)
              ·
                refine ⟨8760208179358653510431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 373768882319302549778389 8760208179358653510431)
                ·
                  rfl

theorem cell20_57579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_57579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57579 prefixEnd_57579 := by exact prefixLift 57579
  have htrace : WordTrace (prefixWord ++ tailWord_57579) baseStart_57579 baseEnd_57579 := by
    simpa [prefixWord, tailWord_57579, baseEnd_57579] using wordTrace_append hprefix tailTrace_57579
  have hstable : (prefixWord ++ tailWord_57579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57579).length < 2 ^ (prefixWord ++ tailWord_57579).sum := by decide
  have hdescent : baseEnd_57579 < baseStart_57579 := by decide
  rcases family_descends (prefixWord ++ tailWord_57579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57596 : List Nat := [2, 2, 2, 1, 4, 2, 1, 6]
def baseStart_57596 : Nat := 118140960795 + 57596 * 2 ^ 59
def prefixEnd_57596 : Nat := 4983230072969 + 3 ^ 40 * 57596 * 2
def baseEnd_57596 : Nat := 8762794600433152321519

theorem tailTrace_57596 : CollatzResearch.WordTrace tailWord_57596 prefixEnd_57596 8762794600433152321519 := by
  unfold tailWord_57596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050349349673501729388321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1400465799564668972517761 1050349349673501729388321)
  ·
    refine ⟨787762012255126297041241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1050349349673501729388321 787762012255126297041241)
    ·
      refine ⟨590821509191344722780931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 787762012255126297041241 590821509191344722780931)
      ·
        refine ⟨886232263787017084171397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590821509191344722780931 886232263787017084171397)
        ·
          refine ⟨166168549460065703282137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 886232263787017084171397 166168549460065703282137)
          ·
            refine ⟨124626412095049277461603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166168549460065703282137 124626412095049277461603)
            ·
              refine ⟨186939618142573916192405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124626412095049277461603 186939618142573916192405)
              ·
                refine ⟨8762794600433152321519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186939618142573916192405 8762794600433152321519)
                ·
                  rfl

theorem cell20_57596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_57596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57596 prefixEnd_57596 := by exact prefixLift 57596
  have htrace : WordTrace (prefixWord ++ tailWord_57596) baseStart_57596 baseEnd_57596 := by
    simpa [prefixWord, tailWord_57596, baseEnd_57596] using wordTrace_append hprefix tailTrace_57596
  have hstable : (prefixWord ++ tailWord_57596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57596).length < 2 ^ (prefixWord ++ tailWord_57596).sum := by decide
  have hdescent : baseEnd_57596 < baseStart_57596 := by decide
  rcases family_descends (prefixWord ++ tailWord_57596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57602 : List Nat := [3, 4, 1, 1, 2, 3, 1, 3, 2]
def baseStart_57602 : Nat := 118140960795 + 57602 * 2 ^ 59
def prefixEnd_57602 : Nat := 4983230072969 + 3 ^ 40 * 57602 * 2
def baseEnd_57602 : Nat := 26291122364790102764533

theorem tailTrace_57602 : CollatzResearch.WordTrace tailWord_57602 prefixEnd_57602 26291122364790102764533 := by
  unfold tailWord_57602
  simp only [CollatzResearch.WordTrace]
  refine ⟨525229384331316620873765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1400611691550177655663373 525229384331316620873765)
  ·
    refine ⟨98480509562121866413831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 525229384331316620873765 98480509562121866413831)
    ·
      refine ⟨147720764343182799620747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98480509562121866413831 147720764343182799620747)
      ·
        refine ⟨221581146514774199431121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147720764343182799620747 221581146514774199431121)
        ·
          refine ⟨166185859886080649573341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221581146514774199431121 166185859886080649573341)
          ·
            refine ⟨62319697457280243590003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 166185859886080649573341 62319697457280243590003)
            ·
              refine ⟨93479546185920365385005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62319697457280243590003 93479546185920365385005)
              ·
                refine ⟨35054829819720137019377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93479546185920365385005 35054829819720137019377)
                ·
                  refine ⟨26291122364790102764533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35054829819720137019377 26291122364790102764533)
                  ·
                    rfl

theorem cell20_57602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_57602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57602 prefixEnd_57602 := by exact prefixLift 57602
  have htrace : WordTrace (prefixWord ++ tailWord_57602) baseStart_57602 baseEnd_57602 := by
    simpa [prefixWord, tailWord_57602, baseEnd_57602] using wordTrace_append hprefix tailTrace_57602
  have hstable : (prefixWord ++ tailWord_57602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57602).length < 2 ^ (prefixWord ++ tailWord_57602).sum := by decide
  have hdescent : baseEnd_57602 < baseStart_57602 := by decide
  rcases family_descends (prefixWord ++ tailWord_57602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57610 : List Nat := [3, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_57610 : Nat := 118140960795 + 57610 * 2 ^ 59
def prefixEnd_57610 : Nat := 4983230072969 + 3 ^ 40 * 57610 * 2
def baseEnd_57610 : Nat := 26294773782777630497833

theorem tailTrace_57610 : CollatzResearch.WordTrace tailWord_57610 prefixEnd_57610 26294773782777630497833 := by
  unfold tailWord_57610
  simp only [CollatzResearch.WordTrace]
  refine ⟨525302330324070962446571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1400806214197522566524189 525302330324070962446571)
  ·
    refine ⟨787953495486106443669857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 525302330324070962446571 787953495486106443669857)
    ·
      refine ⟨590965121614579832752393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 787953495486106443669857 590965121614579832752393)
      ·
        refine ⟨443223841210934874564295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 590965121614579832752393 443223841210934874564295)
        ·
          refine ⟨664835761816402311846443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443223841210934874564295 664835761816402311846443)
          ·
            refine ⟨997253642724603467769665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664835761816402311846443 997253642724603467769665)
            ·
              refine ⟨747940232043452600827249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997253642724603467769665 747940232043452600827249)
              ·
                refine ⟨560955174032589450620437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747940232043452600827249 560955174032589450620437)
                ·
                  refine ⟨26294773782777630497833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 560955174032589450620437 26294773782777630497833)
                  ·
                    rfl

theorem cell20_57610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_57610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57610 prefixEnd_57610 := by exact prefixLift 57610
  have htrace : WordTrace (prefixWord ++ tailWord_57610) baseStart_57610 baseEnd_57610 := by
    simpa [prefixWord, tailWord_57610, baseEnd_57610] using wordTrace_append hprefix tailTrace_57610
  have hstable : (prefixWord ++ tailWord_57610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57610).length < 2 ^ (prefixWord ++ tailWord_57610).sum := by decide
  have hdescent : baseEnd_57610 < baseStart_57610 := by decide
  rcases family_descends (prefixWord ++ tailWord_57610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57617 : List Nat := [1, 2, 2, 1, 1, 5, 8]
def baseStart_57617 : Nat := 118140960795 + 57617 * 2 ^ 59
def prefixEnd_57617 : Nat := 4983230072969 + 3 ^ 40 * 57617 * 2
def baseEnd_57617 : Nat := 2921996530390746362719

theorem tailTrace_57617 : CollatzResearch.WordTrace tailWord_57617 prefixEnd_57617 2921996530390746362719 := by
  unfold tailWord_57617
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101464632270924045291105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1400976421513949363527403 2101464632270924045291105)
  ·
    refine ⟨1576098474203193033968329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2101464632270924045291105 1576098474203193033968329)
    ·
      refine ⟨1182073855652394775476247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1576098474203193033968329 1182073855652394775476247)
      ·
        refine ⟨1773110783478592163214371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182073855652394775476247 1773110783478592163214371)
        ·
          refine ⟨2659666175217888244821557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773110783478592163214371 2659666175217888244821557)
          ·
            refine ⟨249343703926677022952021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2659666175217888244821557 249343703926677022952021)
            ·
              refine ⟨2921996530390746362719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 249343703926677022952021 2921996530390746362719)
              ·
                rfl

theorem cell20_57617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 8].length) (baseStart_57617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57617 prefixEnd_57617 := by exact prefixLift 57617
  have htrace : WordTrace (prefixWord ++ tailWord_57617) baseStart_57617 baseEnd_57617 := by
    simpa [prefixWord, tailWord_57617, baseEnd_57617] using wordTrace_append hprefix tailTrace_57617
  have hstable : (prefixWord ++ tailWord_57617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57617).length < 2 ^ (prefixWord ++ tailWord_57617).sum := by decide
  have hdescent : baseEnd_57617 < baseStart_57617 := by decide
  rcases family_descends (prefixWord ++ tailWord_57617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57623 : List Nat := [1, 1, 3, 4, 1, 3, 3, 2, 2]
def baseStart_57623 : Nat := 118140960795 + 57623 * 2 ^ 59
def prefixEnd_57623 : Nat := 4983230072969 + 3 ^ 40 * 57623 * 2
def baseEnd_57623 : Nat := 26300707337007363064447

theorem tailTrace_57623 : CollatzResearch.WordTrace tailWord_57623 prefixEnd_57623 26300707337007363064447 := by
  unfold tailWord_57623
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101683470249187070009523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1401122313499458046673015 2101683470249187070009523)
  ·
    refine ⟨3152525205373780605014285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2101683470249187070009523 3152525205373780605014285)
    ·
      refine ⟨1182196952015167726880357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3152525205373780605014285 1182196952015167726880357)
      ·
        refine ⟨221661928502843948790067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1182196952015167726880357 221661928502843948790067)
        ·
          refine ⟨332492892754265923185101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221661928502843948790067 332492892754265923185101)
          ·
            refine ⟨124684834782849721194413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332492892754265923185101 124684834782849721194413)
            ·
              refine ⟨46756813043568645447905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124684834782849721194413 46756813043568645447905)
              ·
                refine ⟨35067609782676484085929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46756813043568645447905 35067609782676484085929)
                ·
                  refine ⟨26300707337007363064447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35067609782676484085929 26300707337007363064447)
                  ·
                    rfl

theorem cell20_57623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 2].length) (baseStart_57623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57623 prefixEnd_57623 := by exact prefixLift 57623
  have htrace : WordTrace (prefixWord ++ tailWord_57623) baseStart_57623 baseEnd_57623 := by
    simpa [prefixWord, tailWord_57623, baseEnd_57623] using wordTrace_append hprefix tailTrace_57623
  have hstable : (prefixWord ++ tailWord_57623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57623).length < 2 ^ (prefixWord ++ tailWord_57623).sum := by decide
  have hdescent : baseEnd_57623 < baseStart_57623 := by decide
  rcases family_descends (prefixWord ++ tailWord_57623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57627 : List Nat := [1, 1, 1, 1, 1, 1, 6, 6, 2]
def baseStart_57627 : Nat := 118140960795 + 57627 * 2 ^ 59
def prefixEnd_57627 : Nat := 4983230072969 + 3 ^ 40 * 57627 * 2
def baseEnd_57627 : Nat := 26302533046001126931097

theorem tailTrace_57627 : CollatzResearch.WordTrace tailWord_57627 prefixEnd_57627 26302533046001126931097 := by
  unfold tailWord_57627
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101829362234695753155135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1401219574823130502103423 2101829362234695753155135)
  ·
    refine ⟨3152744043352043629732703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2101829362234695753155135 3152744043352043629732703)
    ·
      refine ⟨4729116065028065444599055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3152744043352043629732703 4729116065028065444599055)
      ·
        refine ⟨7093674097542098166898583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4729116065028065444599055 7093674097542098166898583)
        ·
          refine ⟨10640511146313147250347875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7093674097542098166898583 10640511146313147250347875)
          ·
            refine ⟨15960766719469720875521813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10640511146313147250347875 15960766719469720875521813)
            ·
              refine ⟨748160939975143166040085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15960766719469720875521813 748160939975143166040085)
              ·
                refine ⟨35070044061334835908129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 748160939975143166040085 35070044061334835908129)
                ·
                  refine ⟨26302533046001126931097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35070044061334835908129 26302533046001126931097)
                  ·
                    rfl

theorem cell20_57627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 2].length) (baseStart_57627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57627 prefixEnd_57627 := by exact prefixLift 57627
  have htrace : WordTrace (prefixWord ++ tailWord_57627) baseStart_57627 baseEnd_57627 := by
    simpa [prefixWord, tailWord_57627, baseEnd_57627] using wordTrace_append hprefix tailTrace_57627
  have hstable : (prefixWord ++ tailWord_57627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57627).length < 2 ^ (prefixWord ++ tailWord_57627).sum := by decide
  have hdescent : baseEnd_57627 < baseStart_57627 := by decide
  rcases family_descends (prefixWord ++ tailWord_57627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57630 : List Nat := [4, 3, 2, 1, 1, 2, 2, 5]
def baseStart_57630 : Nat := 118140960795 + 57630 * 2 ^ 59
def prefixEnd_57630 : Nat := 4983230072969 + 3 ^ 40 * 57630 * 2
def baseEnd_57630 : Nat := 8767967442582149943695

theorem tailTrace_57630 : CollatzResearch.WordTrace tailWord_57630 prefixEnd_57630 8767967442582149943695 := by
  unfold tailWord_57630
  simp only [CollatzResearch.WordTrace]
  refine ⟨262742347652978408189293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1401292520815884843676229 262742347652978408189293)
  ·
    refine ⟨98528380369866903070985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262742347652978408189293 98528380369866903070985)
    ·
      refine ⟨73896285277400177303239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98528380369866903070985 73896285277400177303239)
      ·
        refine ⟨110844427916100265954859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73896285277400177303239 110844427916100265954859)
        ·
          refine ⟨166266641874150398932289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110844427916100265954859 166266641874150398932289)
          ·
            refine ⟨124699981405612799199217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166266641874150398932289 124699981405612799199217)
            ·
              refine ⟨93524986054209599399413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124699981405612799199217 93524986054209599399413)
              ·
                refine ⟨8767967442582149943695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93524986054209599399413 8767967442582149943695)
                ·
                  rfl

theorem cell20_57630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_57630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57630 prefixEnd_57630 := by exact prefixLift 57630
  have htrace : WordTrace (prefixWord ++ tailWord_57630) baseStart_57630 baseEnd_57630 := by
    simpa [prefixWord, tailWord_57630, baseEnd_57630] using wordTrace_append hprefix tailTrace_57630
  have hstable : (prefixWord ++ tailWord_57630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57630).length < 2 ^ (prefixWord ++ tailWord_57630).sum := by decide
  have hdescent : baseEnd_57630 < baseStart_57630 := by decide
  rcases family_descends (prefixWord ++ tailWord_57630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57634 : List Nat := [3, 3, 1, 1, 3, 1, 1, 7]
def baseStart_57634 : Nat := 118140960795 + 57634 * 2 ^ 59
def prefixEnd_57634 : Nat := 4983230072969 + 3 ^ 40 * 57634 * 2
def baseEnd_57634 : Nat := 8768576012246737899245

theorem tailTrace_57634 : CollatzResearch.WordTrace tailWord_57634 prefixEnd_57634 8768576012246737899245 := by
  unfold tailWord_57634
  simp only [CollatzResearch.WordTrace]
  refine ⟨525521168302333987164989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1401389782139557299106637 525521168302333987164989)
  ·
    refine ⟨197070438113375245186871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 525521168302333987164989 197070438113375245186871)
    ·
      refine ⟨295605657170062867780307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 197070438113375245186871 295605657170062867780307)
      ·
        refine ⟨443408485755094301670461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295605657170062867780307 443408485755094301670461)
        ·
          refine ⟨166278182158160363126423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443408485755094301670461 166278182158160363126423)
          ·
            refine ⟨249417273237240544689635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166278182158160363126423 249417273237240544689635)
            ·
              refine ⟨374125909855860817034453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249417273237240544689635 374125909855860817034453)
              ·
                refine ⟨8768576012246737899245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 374125909855860817034453 8768576012246737899245)
                ·
                  rfl

theorem cell20_57634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_57634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57634 prefixEnd_57634 := by exact prefixLift 57634
  have htrace : WordTrace (prefixWord ++ tailWord_57634) baseStart_57634 baseEnd_57634 := by
    simpa [prefixWord, tailWord_57634, baseEnd_57634] using wordTrace_append hprefix tailTrace_57634
  have hstable : (prefixWord ++ tailWord_57634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57634).length < 2 ^ (prefixWord ++ tailWord_57634).sum := by decide
  have hdescent : baseEnd_57634 < baseStart_57634 := by decide
  rcases family_descends (prefixWord ++ tailWord_57634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57703 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 4]
def baseStart_57703 : Nat := 118140960795 + 57703 * 2 ^ 59
def prefixEnd_57703 : Nat := 4983230072969 + 3 ^ 40 * 57703 * 2
def baseEnd_57703 : Nat := 26337221516882640397453

theorem tailTrace_57703 : CollatzResearch.WordTrace tailWord_57703 prefixEnd_57703 26337221516882640397453 := by
  unfold tailWord_57703
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104601309959360732921763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1403067539972907155281175 2104601309959360732921763)
  ·
    refine ⟨3156901964939041099382645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2104601309959360732921763 3156901964939041099382645)
    ·
      refine ⟨295959559213035103067123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3156901964939041099382645 295959559213035103067123)
      ·
        refine ⟨443939338819552654600685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295959559213035103067123 443939338819552654600685)
        ·
          refine ⟨166477252057332245475257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443939338819552654600685 166477252057332245475257)
          ·
            refine ⟨124857939042999184106443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166477252057332245475257 124857939042999184106443)
            ·
              refine ⟨187286908564498776159665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124857939042999184106443 187286908564498776159665)
              ·
                refine ⟨140465181423374082119749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187286908564498776159665 140465181423374082119749)
                ·
                  refine ⟨26337221516882640397453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140465181423374082119749 26337221516882640397453)
                  ·
                    rfl

theorem cell20_57703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_57703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57703 prefixEnd_57703 := by exact prefixLift 57703
  have htrace : WordTrace (prefixWord ++ tailWord_57703) baseStart_57703 baseEnd_57703 := by
    simpa [prefixWord, tailWord_57703, baseEnd_57703] using wordTrace_append hprefix tailTrace_57703
  have hstable : (prefixWord ++ tailWord_57703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57703).length < 2 ^ (prefixWord ++ tailWord_57703).sum := by decide
  have hdescent : baseEnd_57703 < baseStart_57703 := by decide
  rcases family_descends (prefixWord ++ tailWord_57703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57758 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_57758 : Nat := 118140960795 + 57758 * 2 ^ 59
def prefixEnd_57758 : Nat := 4983230072969 + 3 ^ 40 * 57758 * 2
def baseEnd_57758 : Nat := 26362325015546893563895

theorem tailTrace_57758 : CollatzResearch.WordTrace tailWord_57758 prefixEnd_57758 26362325015546893563895 := by
  unfold tailWord_57758
  simp only [CollatzResearch.WordTrace]
  refine ⟨263325915595013140771741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1404404883173403417449285 263325915595013140771741)
  ·
    refine ⟨98747218348129927789403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 263325915595013140771741 98747218348129927789403)
    ·
      refine ⟨148120827522194891684105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98747218348129927789403 148120827522194891684105)
      ·
        refine ⟨111090620641646168763079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148120827522194891684105 111090620641646168763079)
        ·
          refine ⟨166635930962469253144619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111090620641646168763079 166635930962469253144619)
          ·
            refine ⟨249953896443703879716929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166635930962469253144619 249953896443703879716929)
            ·
              refine ⟨187465422332777909787697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249953896443703879716929 187465422332777909787697)
              ·
                refine ⟨140599066749583432340773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 187465422332777909787697 140599066749583432340773)
                ·
                  refine ⟨26362325015546893563895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140599066749583432340773 26362325015546893563895)
                  ·
                    rfl

theorem cell20_57758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_57758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57758 prefixEnd_57758 := by exact prefixLift 57758
  have htrace : WordTrace (prefixWord ++ tailWord_57758) baseStart_57758 baseEnd_57758 := by
    simpa [prefixWord, tailWord_57758, baseEnd_57758] using wordTrace_append hprefix tailTrace_57758
  have hstable : (prefixWord ++ tailWord_57758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57758).length < 2 ^ (prefixWord ++ tailWord_57758).sum := by decide
  have hdescent : baseEnd_57758 < baseStart_57758 := by decide
  rcases family_descends (prefixWord ++ tailWord_57758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57761 : List Nat := [1, 2, 3, 5, 2, 1, 2, 4]
def baseStart_57761 : Nat := 118140960795 + 57761 * 2 ^ 59
def prefixEnd_57761 : Nat := 4983230072969 + 3 ^ 40 * 57761 * 2
def baseEnd_57761 : Nat := 8787898099097405487961

theorem tailTrace_57761 : CollatzResearch.WordTrace tailWord_57761 prefixEnd_57761 8787898099097405487961 := by
  unfold tailWord_57761
  simp only [CollatzResearch.WordTrace]
  refine ⟨2106716743749236638533137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1404477829166157759022091 2106716743749236638533137)
  ·
    refine ⟨1580037557811927478899853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2106716743749236638533137 1580037557811927478899853)
    ·
      refine ⟨592514084179472804587445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1580037557811927478899853 592514084179472804587445)
      ·
        refine ⟨55548195391825575430073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 592514084179472804587445 55548195391825575430073)
        ·
          refine ⟨41661146543869181572555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55548195391825575430073 41661146543869181572555)
          ·
            refine ⟨62491719815803772358833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41661146543869181572555 62491719815803772358833)
            ·
              refine ⟨46868789861852829269125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62491719815803772358833 46868789861852829269125)
              ·
                refine ⟨8787898099097405487961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46868789861852829269125 8787898099097405487961)
                ·
                  rfl

theorem cell20_57761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 4].length) (baseStart_57761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57761 prefixEnd_57761 := by exact prefixLift 57761
  have htrace : WordTrace (prefixWord ++ tailWord_57761) baseStart_57761 baseEnd_57761 := by
    simpa [prefixWord, tailWord_57761, baseEnd_57761] using wordTrace_append hprefix tailTrace_57761
  have hstable : (prefixWord ++ tailWord_57761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57761).length < 2 ^ (prefixWord ++ tailWord_57761).sum := by decide
  have hdescent : baseEnd_57761 < baseStart_57761 := by decide
  rcases family_descends (prefixWord ++ tailWord_57761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57855 : List Nat := [1, 1, 2, 2, 1, 2, 5, 4, 2]
def baseStart_57855 : Nat := 118140960795 + 57855 * 2 ^ 59
def prefixEnd_57855 : Nat := 4983230072969 + 3 ^ 40 * 57855 * 2
def baseEnd_57855 : Nat := 26406598458645667330165

theorem tailTrace_57855 : CollatzResearch.WordTrace tailWord_57855 prefixEnd_57855 26406598458645667330165 := by
  unfold tailWord_57855
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110145205408690692455019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1406763470272460461636679 2110145205408690692455019)
  ·
    refine ⟨3165217808113036038682529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110145205408690692455019 3165217808113036038682529)
    ·
      refine ⟨2373913356084777029011897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3165217808113036038682529 2373913356084777029011897)
      ·
        refine ⟨1780435017063582771758923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2373913356084777029011897 1780435017063582771758923)
        ·
          refine ⟨2670652525595374157638385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780435017063582771758923 2670652525595374157638385)
          ·
            refine ⟨2002989394196530618228789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2670652525595374157638385 2002989394196530618228789)
            ·
              refine ⟨187780255705924745458949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2002989394196530618228789 187780255705924745458949)
              ·
                refine ⟨35208797944860889773553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187780255705924745458949 35208797944860889773553)
                ·
                  refine ⟨26406598458645667330165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35208797944860889773553 26406598458645667330165)
                  ·
                    rfl

theorem cell20_57855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 2].length) (baseStart_57855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57855 prefixEnd_57855 := by exact prefixLift 57855
  have htrace : WordTrace (prefixWord ++ tailWord_57855) baseStart_57855 baseEnd_57855 := by
    simpa [prefixWord, tailWord_57855, baseEnd_57855] using wordTrace_append hprefix tailTrace_57855
  have hstable : (prefixWord ++ tailWord_57855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57855).length < 2 ^ (prefixWord ++ tailWord_57855).sum := by decide
  have hdescent : baseEnd_57855 < baseStart_57855 := by decide
  rcases family_descends (prefixWord ++ tailWord_57855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57858 : List Nat := [3, 4, 1, 2, 2, 2, 1, 5]
def baseStart_57858 : Nat := 118140960795 + 57858 * 2 ^ 59
def prefixEnd_57858 : Nat := 4983230072969 + 3 ^ 40 * 57858 * 2
def baseEnd_57858 : Nat := 8802655913463663410051

theorem tailTrace_57858 : CollatzResearch.WordTrace tailWord_57858 prefixEnd_57858 8802655913463663410051 := by
  unfold tailWord_57858
  simp only [CollatzResearch.WordTrace]
  refine ⟨527563656099455551203557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1406836416265214803209485 527563656099455551203557)
  ·
    refine ⟨98918185518647915850667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 527563656099455551203557 98918185518647915850667)
    ·
      refine ⟨148377278277971873776001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98918185518647915850667 148377278277971873776001)
      ·
        refine ⟨111282958708478905332001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148377278277971873776001 111282958708478905332001)
        ·
          refine ⟨83462219031359178999001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111282958708478905332001 83462219031359178999001)
          ·
            refine ⟨62596664273519384249251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83462219031359178999001 62596664273519384249251)
            ·
              refine ⟨93894996410279076373877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62596664273519384249251 93894996410279076373877)
              ·
                refine ⟨8802655913463663410051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93894996410279076373877 8802655913463663410051)
                ·
                  rfl

theorem cell20_57858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_57858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57858 prefixEnd_57858 := by exact prefixLift 57858
  have htrace : WordTrace (prefixWord ++ tailWord_57858) baseStart_57858 baseEnd_57858 := by
    simpa [prefixWord, tailWord_57858, baseEnd_57858] using wordTrace_append hprefix tailTrace_57858
  have hstable : (prefixWord ++ tailWord_57858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57858).length < 2 ^ (prefixWord ++ tailWord_57858).sum := by decide
  have hdescent : baseEnd_57858 < baseStart_57858 := by decide
  rcases family_descends (prefixWord ++ tailWord_57858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57893 : List Nat := [1, 3, 1, 2, 2, 1, 3, 5, 2]
def baseStart_57893 : Nat := 118140960795 + 57893 * 2 ^ 59
def prefixEnd_57893 : Nat := 4983230072969 + 3 ^ 40 * 57893 * 2
def baseEnd_57893 : Nat := 26423942694086424063343

theorem tailTrace_57893 : CollatzResearch.WordTrace tailWord_57893 prefixEnd_57893 26423942694086424063343 := by
  unfold tailWord_57893
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111531179271023182338333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1407687452847348788225555 2111531179271023182338333)
  ·
    refine ⟨791824192226633693376875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2111531179271023182338333 791824192226633693376875)
    ·
      refine ⟨1187736288339950540065313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791824192226633693376875 1187736288339950540065313)
      ·
        refine ⟨890802216254962905048985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1187736288339950540065313 890802216254962905048985)
        ·
          refine ⟨668101662191222178786739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890802216254962905048985 668101662191222178786739)
          ·
            refine ⟨1002152493286833268180109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668101662191222178786739 1002152493286833268180109)
            ·
              refine ⟨375807184982562475567541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1002152493286833268180109 375807184982562475567541)
              ·
                refine ⟨35231923592115232084457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 375807184982562475567541 35231923592115232084457)
                ·
                  refine ⟨26423942694086424063343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35231923592115232084457 26423942694086424063343)
                  ·
                    rfl

theorem cell20_57893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_57893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57893 prefixEnd_57893 := by exact prefixLift 57893
  have htrace : WordTrace (prefixWord ++ tailWord_57893) baseStart_57893 baseEnd_57893 := by
    simpa [prefixWord, tailWord_57893, baseEnd_57893] using wordTrace_append hprefix tailTrace_57893
  have hstable : (prefixWord ++ tailWord_57893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57893).length < 2 ^ (prefixWord ++ tailWord_57893).sum := by decide
  have hdescent : baseEnd_57893 < baseStart_57893 := by decide
  rcases family_descends (prefixWord ++ tailWord_57893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57910 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_57910 : Nat := 118140960795 + 57910 * 2 ^ 59
def prefixEnd_57910 : Nat := 4983230072969 + 3 ^ 40 * 57910 * 2
def baseEnd_57910 : Nat := 26431701957309920496607

theorem tailTrace_57910 : CollatzResearch.WordTrace tailWord_57910 prefixEnd_57910 26431701957309920496607 := by
  unfold tailWord_57910
  simp only [CollatzResearch.WordTrace]
  refine ⟨132009451263089692856699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1408100813472956723804789 132009451263089692856699)
  ·
    refine ⟨198014176894634539285049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132009451263089692856699 198014176894634539285049)
    ·
      refine ⟨148510632670975904463787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198014176894634539285049 148510632670975904463787)
      ·
        refine ⟨222765949006463856695681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148510632670975904463787 222765949006463856695681)
        ·
          refine ⟨167074461754847892521761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 222765949006463856695681 167074461754847892521761)
          ·
            refine ⟨125305846316135919391321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167074461754847892521761 125305846316135919391321)
            ·
              refine ⟨93979384737101939543491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125305846316135919391321 93979384737101939543491)
              ·
                refine ⟨140969077105652909315237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93979384737101939543491 140969077105652909315237)
                ·
                  refine ⟨26431701957309920496607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140969077105652909315237 26431701957309920496607)
                  ·
                    rfl

theorem cell20_57910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_57910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57910 prefixEnd_57910 := by exact prefixLift 57910
  have htrace : WordTrace (prefixWord ++ tailWord_57910) baseStart_57910 baseEnd_57910 := by
    simpa [prefixWord, tailWord_57910, baseEnd_57910] using wordTrace_append hprefix tailTrace_57910
  have hstable : (prefixWord ++ tailWord_57910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57910).length < 2 ^ (prefixWord ++ tailWord_57910).sum := by decide
  have hdescent : baseEnd_57910 < baseStart_57910 := by decide
  rcases family_descends (prefixWord ++ tailWord_57910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57914 : List Nat := [3, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_57914 : Nat := 118140960795 + 57914 * 2 ^ 59
def prefixEnd_57914 : Nat := 4983230072969 + 3 ^ 40 * 57914 * 2
def baseEnd_57914 : Nat := 26433527666303684363257

theorem tailTrace_57914 : CollatzResearch.WordTrace tailWord_57914 prefixEnd_57914 26433527666303684363257 := by
  unfold tailWord_57914
  simp only [CollatzResearch.WordTrace]
  refine ⟨528074278048735942213199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1408198074796629179235197 528074278048735942213199)
  ·
    refine ⟨792111417073103913319799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 528074278048735942213199 792111417073103913319799)
    ·
      refine ⟨1188167125609655869979699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 792111417073103913319799 1188167125609655869979699)
      ·
        refine ⟨1782250688414483804969549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188167125609655869979699 1782250688414483804969549)
        ·
          refine ⟨668344008155431426863581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1782250688414483804969549 668344008155431426863581)
          ·
            refine ⟨250629003058286785073843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 668344008155431426863581 250629003058286785073843)
            ·
              refine ⟨375943504587430177610765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250629003058286785073843 375943504587430177610765)
              ·
                refine ⟨140978814220286316604037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375943504587430177610765 140978814220286316604037)
                ·
                  refine ⟨26433527666303684363257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140978814220286316604037 26433527666303684363257)
                  ·
                    rfl

theorem cell20_57914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_57914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57914 prefixEnd_57914 := by exact prefixLift 57914
  have htrace : WordTrace (prefixWord ++ tailWord_57914) baseStart_57914 baseEnd_57914 := by
    simpa [prefixWord, tailWord_57914, baseEnd_57914] using wordTrace_append hprefix tailTrace_57914
  have hstable : (prefixWord ++ tailWord_57914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57914).length < 2 ^ (prefixWord ++ tailWord_57914).sum := by decide
  have hdescent : baseEnd_57914 < baseStart_57914 := by decide
  rcases family_descends (prefixWord ++ tailWord_57914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_57965 : List Nat := [1, 5, 1, 1, 3, 2, 3, 2, 2]
def baseStart_57965 : Nat := 118140960795 + 57965 * 2 ^ 59
def prefixEnd_57965 : Nat := 4983230072969 + 3 ^ 40 * 57965 * 2
def baseEnd_57965 : Nat := 26456805455974173663049

theorem tailTrace_57965 : CollatzResearch.WordTrace tailWord_57965 prefixEnd_57965 26456805455974173663049 := by
  unfold tailWord_57965
  simp only [CollatzResearch.WordTrace]
  refine ⟨2114157235010179478959349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1409438156673452985972899 2114157235010179478959349)
  ·
    refine ⟨198202240782204326152439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2114157235010179478959349 198202240782204326152439)
    ·
      refine ⟨297303361173306489228659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198202240782204326152439 297303361173306489228659)
      ·
        refine ⟨445955041759959733842989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297303361173306489228659 445955041759959733842989)
        ·
          refine ⟨167233140659984900191121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 445955041759959733842989 167233140659984900191121)
          ·
            refine ⟨125424855494988675143341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167233140659984900191121 125424855494988675143341)
            ·
              refine ⟨47034320810620753178753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125424855494988675143341 47034320810620753178753)
              ·
                refine ⟨35275740607965564884065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47034320810620753178753 35275740607965564884065)
                ·
                  refine ⟨26456805455974173663049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35275740607965564884065 26456805455974173663049)
                  ·
                    rfl

theorem cell20_57965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_57965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_57965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_57965 prefixEnd_57965 := by exact prefixLift 57965
  have htrace : WordTrace (prefixWord ++ tailWord_57965) baseStart_57965 baseEnd_57965 := by
    simpa [prefixWord, tailWord_57965, baseEnd_57965] using wordTrace_append hprefix tailTrace_57965
  have hstable : (prefixWord ++ tailWord_57965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_57965).length < 2 ^ (prefixWord ++ tailWord_57965).sum := by decide
  have hdescent : baseEnd_57965 < baseStart_57965 := by decide
  rcases family_descends (prefixWord ++ tailWord_57965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58007 : List Nat := [1, 1, 3, 3, 2, 1, 2, 5, 2]
def baseStart_58007 : Nat := 118140960795 + 58007 * 2 ^ 59
def prefixEnd_58007 : Nat := 4983230072969 + 3 ^ 40 * 58007 * 2
def baseEnd_58007 : Nat := 26475975400408694262877

theorem tailTrace_58007 : CollatzResearch.WordTrace tailWord_58007 prefixEnd_58007 26475975400408694262877 := by
  unfold tailWord_58007
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115689100858020651988275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1410459400572013767992183 2115689100858020651988275)
  ·
    refine ⟨3173533651287030977982413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2115689100858020651988275 3173533651287030977982413)
    ·
      refine ⟨1190075119232636616743405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3173533651287030977982413 1190075119232636616743405)
      ·
        refine ⟨446278169712238731278777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1190075119232636616743405 446278169712238731278777)
        ·
          refine ⟨334708627284179048459083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446278169712238731278777 334708627284179048459083)
          ·
            refine ⟨502062940926268572688625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334708627284179048459083 502062940926268572688625)
            ·
              refine ⟨376547205694701429516469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502062940926268572688625 376547205694701429516469)
              ·
                refine ⟨35301300533878259017169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376547205694701429516469 35301300533878259017169)
                ·
                  refine ⟨26475975400408694262877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35301300533878259017169 26475975400408694262877)
                  ·
                    rfl

theorem cell20_58007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 2].length) (baseStart_58007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58007 prefixEnd_58007 := by exact prefixLift 58007
  have htrace : WordTrace (prefixWord ++ tailWord_58007) baseStart_58007 baseEnd_58007 := by
    simpa [prefixWord, tailWord_58007, baseEnd_58007] using wordTrace_append hprefix tailTrace_58007
  have hstable : (prefixWord ++ tailWord_58007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58007).length < 2 ^ (prefixWord ++ tailWord_58007).sum := by decide
  have hdescent : baseEnd_58007 < baseStart_58007 := by decide
  rcases family_descends (prefixWord ++ tailWord_58007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58035 : List Nat := [1, 1, 1, 2, 3, 4, 3, 5]
def baseStart_58035 : Nat := 118140960795 + 58035 * 2 ^ 59
def prefixEnd_58035 : Nat := 4983230072969 + 3 ^ 40 * 58035 * 2
def baseEnd_58035 : Nat := 8829585121121680443143

theorem tailTrace_58035 : CollatzResearch.WordTrace tailWord_58035 prefixEnd_58035 8829585121121680443143 := by
  unfold tailWord_58035
  simp only [CollatzResearch.WordTrace]
  refine ⟨2116710344756581434007559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1411140229837720956005039 2116710344756581434007559)
  ·
    refine ⟨3175065517134872151011339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2116710344756581434007559 3175065517134872151011339)
    ·
      refine ⟨4762598275702308226517009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3175065517134872151011339 4762598275702308226517009)
      ·
        refine ⟨3571948706776731169887757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4762598275702308226517009 3571948706776731169887757)
        ·
          refine ⟨1339480765041274188707909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3571948706776731169887757 1339480765041274188707909)
          ·
            refine ⟨251152643445238910382733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1339480765041274188707909 251152643445238910382733)
            ·
              refine ⟨94182241291964591393525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251152643445238910382733 94182241291964591393525)
              ·
                refine ⟨8829585121121680443143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94182241291964591393525 8829585121121680443143)
                ·
                  rfl

theorem cell20_58035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_58035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58035 prefixEnd_58035 := by exact prefixLift 58035
  have htrace : WordTrace (prefixWord ++ tailWord_58035) baseStart_58035 baseEnd_58035 := by
    simpa [prefixWord, tailWord_58035, baseEnd_58035] using wordTrace_append hprefix tailTrace_58035
  have hstable : (prefixWord ++ tailWord_58035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58035).length < 2 ^ (prefixWord ++ tailWord_58035).sum := by decide
  have hdescent : baseEnd_58035 < baseStart_58035 := by decide
  rcases family_descends (prefixWord ++ tailWord_58035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58062 : List Nat := [4, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_58062 : Nat := 118140960795 + 58062 * 2 ^ 59
def prefixEnd_58062 : Nat := 4983230072969 + 3 ^ 40 * 58062 * 2
def baseEnd_58062 : Nat := 26501078899072947429319

theorem tailTrace_58062 : CollatzResearch.WordTrace tailWord_58062 prefixEnd_58062 26501078899072947429319 := by
  unfold tailWord_58062
  simp only [CollatzResearch.WordTrace]
  refine ⟨264711889457345630655055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1411796743772510030160293 264711889457345630655055)
  ·
    refine ⟨397067834186018445982583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264711889457345630655055 397067834186018445982583)
    ·
      refine ⟨595601751279027668973875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397067834186018445982583 595601751279027668973875)
      ·
        refine ⟨893402626918541503460813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595601751279027668973875 893402626918541503460813)
        ·
          refine ⟨335025985094453063797805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 893402626918541503460813 335025985094453063797805)
          ·
            refine ⟨125634744410419898924177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335025985094453063797805 125634744410419898924177)
            ·
              refine ⟨94226058307814924193133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125634744410419898924177 94226058307814924193133)
              ·
                refine ⟨35334771865430596572425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94226058307814924193133 35334771865430596572425)
                ·
                  refine ⟨26501078899072947429319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35334771865430596572425 26501078899072947429319)
                  ·
                    rfl

theorem cell20_58062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_58062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58062 prefixEnd_58062 := by exact prefixLift 58062
  have htrace : WordTrace (prefixWord ++ tailWord_58062) baseStart_58062 baseEnd_58062 := by
    simpa [prefixWord, tailWord_58062, baseEnd_58062] using wordTrace_append hprefix tailTrace_58062
  have hstable : (prefixWord ++ tailWord_58062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58062).length < 2 ^ (prefixWord ++ tailWord_58062).sum := by decide
  have hdescent : baseEnd_58062 < baseStart_58062 := by decide
  rcases family_descends (prefixWord ++ tailWord_58062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58076 : List Nat := [2, 2, 5, 1, 1, 2, 1, 1, 5]
def baseStart_58076 : Nat := 118140960795 + 58076 * 2 ^ 59
def prefixEnd_58076 : Nat := 4983230072969 + 3 ^ 40 * 58076 * 2
def baseEnd_58076 : Nat := 26507468880551120962595

theorem tailTrace_58076 : CollatzResearch.WordTrace tailWord_58076 prefixEnd_58076 26507468880551120962595 := by
  unfold tailWord_58076
  simp only [CollatzResearch.WordTrace]
  refine ⟨1059102868804022718125041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1412137158405363624166721 1059102868804022718125041)
  ·
    refine ⟨794327151603017038593781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1059102868804022718125041 794327151603017038593781)
    ·
      refine ⟨74468170462782847368167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 794327151603017038593781 74468170462782847368167)
      ·
        refine ⟨111702255694174271052251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74468170462782847368167 111702255694174271052251)
        ·
          refine ⟨167553383541261406578377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111702255694174271052251 167553383541261406578377)
          ·
            refine ⟨125665037655946054933783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167553383541261406578377 125665037655946054933783)
            ·
              refine ⟨188497556483919082400675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125665037655946054933783 188497556483919082400675)
              ·
                refine ⟨282746334725878623601013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188497556483919082400675 282746334725878623601013)
                ·
                  refine ⟨26507468880551120962595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 282746334725878623601013 26507468880551120962595)
                  ·
                    rfl

theorem cell20_58076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_58076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58076 prefixEnd_58076 := by exact prefixLift 58076
  have htrace : WordTrace (prefixWord ++ tailWord_58076) baseStart_58076 baseEnd_58076 := by
    simpa [prefixWord, tailWord_58076, baseEnd_58076] using wordTrace_append hprefix tailTrace_58076
  have hstable : (prefixWord ++ tailWord_58076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58076).length < 2 ^ (prefixWord ++ tailWord_58076).sum := by decide
  have hdescent : baseEnd_58076 < baseStart_58076 := by decide
  rcases family_descends (prefixWord ++ tailWord_58076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58083 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 4]
def baseStart_58083 : Nat := 118140960795 + 58083 * 2 ^ 59
def prefixEnd_58083 : Nat := 4983230072969 + 3 ^ 40 * 58083 * 2
def baseEnd_58083 : Nat := 26510663871290207729233

theorem tailTrace_58083 : CollatzResearch.WordTrace tailWord_58083 prefixEnd_58083 26510663871290207729233 := by
  unfold tailWord_58083
  simp only [CollatzResearch.WordTrace]
  refine ⟨2118461048582685631754903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1412307365721790421169935 2118461048582685631754903)
  ·
    refine ⟨3177691572874028447632355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2118461048582685631754903 3177691572874028447632355)
    ·
      refine ⟨4766537359311042671448533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3177691572874028447632355 4766537359311042671448533)
      ·
        refine ⟨111715719358852562612075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 4766537359311042671448533 111715719358852562612075)
        ·
          refine ⟨167573579038278843918113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111715719358852562612075 167573579038278843918113)
          ·
            refine ⟨125680184278709132938585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167573579038278843918113 125680184278709132938585)
            ·
              refine ⟨94260138209031849703939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125680184278709132938585 94260138209031849703939)
              ·
                refine ⟨141390207313547774555909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94260138209031849703939 141390207313547774555909)
                ·
                  refine ⟨26510663871290207729233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141390207313547774555909 26510663871290207729233)
                  ·
                    rfl

theorem cell20_58083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_58083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58083 prefixEnd_58083 := by exact prefixLift 58083
  have htrace : WordTrace (prefixWord ++ tailWord_58083) baseStart_58083 baseEnd_58083 := by
    simpa [prefixWord, tailWord_58083, baseEnd_58083] using wordTrace_append hprefix tailTrace_58083
  have hstable : (prefixWord ++ tailWord_58083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58083).length < 2 ^ (prefixWord ++ tailWord_58083).sum := by decide
  have hdescent : baseEnd_58083 < baseStart_58083 := by decide
  rcases family_descends (prefixWord ++ tailWord_58083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58121 : List Nat := [1, 2, 1, 1, 3, 2, 5, 3, 2]
def baseStart_58121 : Nat := 118140960795 + 58121 * 2 ^ 59
def prefixEnd_58121 : Nat := 4983230072969 + 3 ^ 40 * 58121 * 2
def baseEnd_58121 : Nat := 26528008106730964462411

theorem tailTrace_58121 : CollatzResearch.WordTrace tailWord_58121 prefixEnd_58121 26528008106730964462411 := by
  unfold tailWord_58121
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119847022445018121638217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1413231348296678747758811 2119847022445018121638217)
  ·
    refine ⟨1589885266833763591228663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2119847022445018121638217 1589885266833763591228663)
    ·
      refine ⟨2384827900250645386842995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589885266833763591228663 2384827900250645386842995)
      ·
        refine ⟨3577241850375968080264493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384827900250645386842995 3577241850375968080264493)
        ·
          refine ⟨1341465693890988030099185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3577241850375968080264493 1341465693890988030099185)
          ·
            refine ⟨1006099270418241022574389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1341465693890988030099185 1006099270418241022574389)
            ·
              refine ⟨94321806601710095866349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1006099270418241022574389 94321806601710095866349)
              ·
                refine ⟨35370677475641285949881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94321806601710095866349 35370677475641285949881)
                ·
                  refine ⟨26528008106730964462411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35370677475641285949881 26528008106730964462411)
                  ·
                    rfl

theorem cell20_58121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 2].length) (baseStart_58121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58121 prefixEnd_58121 := by exact prefixLift 58121
  have htrace : WordTrace (prefixWord ++ tailWord_58121) baseStart_58121 baseEnd_58121 := by
    simpa [prefixWord, tailWord_58121, baseEnd_58121] using wordTrace_append hprefix tailTrace_58121
  have hstable : (prefixWord ++ tailWord_58121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58121).length < 2 ^ (prefixWord ++ tailWord_58121).sum := by decide
  have hdescent : baseEnd_58121 < baseStart_58121 := by decide
  rcases family_descends (prefixWord ++ tailWord_58121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58138 : List Nat := [3, 1, 1, 3, 2, 1, 5, 2, 2]
def baseStart_58138 : Nat := 118140960795 + 58138 * 2 ^ 59
def prefixEnd_58138 : Nat := 4983230072969 + 3 ^ 40 * 58138 * 2
def baseEnd_58138 : Nat := 26535767369954460895675

theorem tailTrace_58138 : CollatzResearch.WordTrace tailWord_58138 prefixEnd_58138 26535767369954460895675 := by
  unfold tailWord_58138
  simp only [CollatzResearch.WordTrace]
  refine ⟨530116765845857506251767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1413644708922286683338045 530116765845857506251767)
  ·
    refine ⟨795175148768786259377651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 530116765845857506251767 795175148768786259377651)
    ·
      refine ⟨1192762723153179389066477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795175148768786259377651 1192762723153179389066477)
      ·
        refine ⟨447286021182442270899929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1192762723153179389066477 447286021182442270899929)
        ·
          refine ⟨335464515886831703174947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447286021182442270899929 335464515886831703174947)
          ·
            refine ⟨503196773830247554762421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335464515886831703174947 503196773830247554762421)
            ·
              refine ⟨47174697546585708258977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 503196773830247554762421 47174697546585708258977)
              ·
                refine ⟨35381023159939281194233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47174697546585708258977 35381023159939281194233)
                ·
                  refine ⟨26535767369954460895675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35381023159939281194233 26535767369954460895675)
                  ·
                    rfl

theorem cell20_58138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_58138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58138 prefixEnd_58138 := by exact prefixLift 58138
  have htrace : WordTrace (prefixWord ++ tailWord_58138) baseStart_58138 baseEnd_58138 := by
    simpa [prefixWord, tailWord_58138, baseEnd_58138] using wordTrace_append hprefix tailTrace_58138
  have hstable : (prefixWord ++ tailWord_58138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58138).length < 2 ^ (prefixWord ++ tailWord_58138).sum := by decide
  have hdescent : baseEnd_58138 < baseStart_58138 := by decide
  rcases family_descends (prefixWord ++ tailWord_58138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58148 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 3]
def baseStart_58148 : Nat := 118140960795 + 58148 * 2 ^ 59
def prefixEnd_58148 : Nat := 4983230072969 + 3 ^ 40 * 58148 * 2
def baseEnd_58148 : Nat := 26540331642438870562301

theorem tailTrace_58148 : CollatzResearch.WordTrace tailWord_58148 prefixEnd_58148 26540331642438870562301 := by
  unfold tailWord_58148
  simp only [CollatzResearch.WordTrace]
  refine ⟨1060415896673600866435549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1413887862231467821914065 1060415896673600866435549)
  ·
    refine ⟨397655961252600324913331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1060415896673600866435549 397655961252600324913331)
    ·
      refine ⟨596483941878900487369997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397655961252600324913331 596483941878900487369997)
      ·
        refine ⟨223681478204587682763749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 596483941878900487369997 223681478204587682763749)
        ·
          refine ⟨41940277163360190518203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223681478204587682763749 41940277163360190518203)
          ·
            refine ⟨62910415745040285777305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41940277163360190518203 62910415745040285777305)
            ·
              refine ⟨47182811808780214332979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62910415745040285777305 47182811808780214332979)
              ·
                refine ⟨70774217713170321499469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47182811808780214332979 70774217713170321499469)
                ·
                  refine ⟨26540331642438870562301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70774217713170321499469 26540331642438870562301)
                  ·
                    rfl

theorem cell20_58148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_58148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58148 prefixEnd_58148 := by exact prefixLift 58148
  have htrace : WordTrace (prefixWord ++ tailWord_58148) baseStart_58148 baseEnd_58148 := by
    simpa [prefixWord, tailWord_58148, baseEnd_58148] using wordTrace_append hprefix tailTrace_58148
  have hstable : (prefixWord ++ tailWord_58148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58148).length < 2 ^ (prefixWord ++ tailWord_58148).sum := by decide
  have hdescent : baseEnd_58148 < baseStart_58148 := by decide
  rcases family_descends (prefixWord ++ tailWord_58148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58149 : List Nat := [1, 3, 1, 2, 3, 1, 4, 5]
def baseStart_58149 : Nat := 118140960795 + 58149 * 2 ^ 59
def prefixEnd_58149 : Nat := 4983230072969 + 3 ^ 40 * 58149 * 2
def baseEnd_58149 : Nat := 8846929356562437176321

theorem tailTrace_58149 : CollatzResearch.WordTrace tailWord_58149 prefixEnd_58149 8846929356562437176321 := by
  unfold tailWord_58149
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120868266343578903657501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1413912177562385935771667 2120868266343578903657501)
  ·
    refine ⟨795325599878842088871563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2120868266343578903657501 795325599878842088871563)
    ·
      refine ⟨1192988399818263133307345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 795325599878842088871563 1192988399818263133307345)
      ·
        refine ⟨894741299863697349980509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1192988399818263133307345 894741299863697349980509)
        ·
          refine ⟨335527987448886506242691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 894741299863697349980509 335527987448886506242691)
          ·
            refine ⟨503291981173329759364037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335527987448886506242691 503291981173329759364037)
            ·
              refine ⟨94367246469999329880757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 503291981173329759364037 94367246469999329880757)
              ·
                refine ⟨8846929356562437176321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94367246469999329880757 8846929356562437176321)
                ·
                  rfl

theorem cell20_58149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_58149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58149 prefixEnd_58149 := by exact prefixLift 58149
  have htrace : WordTrace (prefixWord ++ tailWord_58149) baseStart_58149 baseEnd_58149 := by
    simpa [prefixWord, tailWord_58149, baseEnd_58149] using wordTrace_append hprefix tailTrace_58149
  have hstable : (prefixWord ++ tailWord_58149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58149).length < 2 ^ (prefixWord ++ tailWord_58149).sum := by decide
  have hdescent : baseEnd_58149 < baseStart_58149 := by decide
  rcases family_descends (prefixWord ++ tailWord_58149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58189 : List Nat := [1, 6, 1, 2, 3, 1, 2, 2, 2]
def baseStart_58189 : Nat := 118140960795 + 58189 * 2 ^ 59
def prefixEnd_58189 : Nat := 4983230072969 + 3 ^ 40 * 58189 * 2
def baseEnd_58189 : Nat := 26559045159624950195467

theorem tailTrace_58189 : CollatzResearch.WordTrace tailWord_58189 prefixEnd_58189 26559045159624950195467 := by
  unfold tailWord_58189
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122327186198665735113621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1414884790799110490075747 2122327186198665735113621)
  ·
    refine ⟨99484086853062456333451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2122327186198665735113621 99484086853062456333451)
    ·
      refine ⟨149226130279593684500177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99484086853062456333451 149226130279593684500177)
      ·
        refine ⟨111919597709695263375133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149226130279593684500177 111919597709695263375133)
        ·
          refine ⟨41969849141135723765675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111919597709695263375133 41969849141135723765675)
          ·
            refine ⟨62954773711703585648513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41969849141135723765675 62954773711703585648513)
            ·
              refine ⟨47216080283777689236385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62954773711703585648513 47216080283777689236385)
              ·
                refine ⟨35412060212833266927289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47216080283777689236385 35412060212833266927289)
                ·
                  refine ⟨26559045159624950195467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35412060212833266927289 26559045159624950195467)
                  ·
                    rfl

theorem cell20_58189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_58189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58189 prefixEnd_58189 := by exact prefixLift 58189
  have htrace : WordTrace (prefixWord ++ tailWord_58189) baseStart_58189 baseEnd_58189 := by
    simpa [prefixWord, tailWord_58189, baseEnd_58189] using wordTrace_append hprefix tailTrace_58189
  have hstable : (prefixWord ++ tailWord_58189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58189).length < 2 ^ (prefixWord ++ tailWord_58189).sum := by decide
  have hdescent : baseEnd_58189 < baseStart_58189 := by decide
  rcases family_descends (prefixWord ++ tailWord_58189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58193 : List Nat := [1, 2, 2, 1, 6, 2, 2, 2, 2]
def baseStart_58193 : Nat := 118140960795 + 58193 * 2 ^ 59
def prefixEnd_58193 : Nat := 4983230072969 + 3 ^ 40 * 58193 * 2
def baseEnd_58193 : Nat := 26560870868618714062117

theorem tailTrace_58193 : CollatzResearch.WordTrace tailWord_58193 prefixEnd_58193 26560870868618714062117 := by
  unfold tailWord_58193
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122473078184174418259233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1414982052122782945506155 2122473078184174418259233)
  ·
    refine ⟨1591854808638130813694425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2122473078184174418259233 1591854808638130813694425)
    ·
      refine ⟨1193891106478598110270819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1591854808638130813694425 1193891106478598110270819)
      ·
        refine ⟨1790836659717897165406229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1193891106478598110270819 1790836659717897165406229)
        ·
          refine ⟨83945468424276429628417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1790836659717897165406229 83945468424276429628417)
          ·
            refine ⟨62959101318207322221313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83945468424276429628417 62959101318207322221313)
            ·
              refine ⟨47219325988655491665985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62959101318207322221313 47219325988655491665985)
              ·
                refine ⟨35414494491491618749489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47219325988655491665985 35414494491491618749489)
                ·
                  refine ⟨26560870868618714062117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35414494491491618749489 26560870868618714062117)
                  ·
                    rfl

theorem cell20_58193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 2, 2].length) (baseStart_58193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58193 prefixEnd_58193 := by exact prefixLift 58193
  have htrace : WordTrace (prefixWord ++ tailWord_58193) baseStart_58193 baseEnd_58193 := by
    simpa [prefixWord, tailWord_58193, baseEnd_58193] using wordTrace_append hprefix tailTrace_58193
  have hstable : (prefixWord ++ tailWord_58193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58193).length < 2 ^ (prefixWord ++ tailWord_58193).sum := by decide
  have hdescent : baseEnd_58193 < baseStart_58193 := by decide
  rcases family_descends (prefixWord ++ tailWord_58193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58197 : List Nat := [1, 3, 2, 2, 2, 1, 3, 4, 2]
def baseStart_58197 : Nat := 118140960795 + 58197 * 2 ^ 59
def prefixEnd_58197 : Nat := 4983230072969 + 3 ^ 40 * 58197 * 2
def baseEnd_58197 : Nat := 26562696577612477928767

theorem tailTrace_58197 : CollatzResearch.WordTrace tailWord_58197 prefixEnd_58197 26562696577612477928767 := by
  unfold tailWord_58197
  simp only [CollatzResearch.WordTrace]
  refine ⟨2122618970169683101404845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1415079313446455400936563 2122618970169683101404845)
  ·
    refine ⟨795982113813631163026817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2122618970169683101404845 795982113813631163026817)
    ·
      refine ⟨596986585360223372270113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 795982113813631163026817 596986585360223372270113)
      ·
        refine ⟨447739939020167529202585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596986585360223372270113 447739939020167529202585)
        ·
          refine ⟨335804954265125646901939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447739939020167529202585 335804954265125646901939)
          ·
            refine ⟨503707431397688470352909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335804954265125646901939 503707431397688470352909)
            ·
              refine ⟨188890286774133176382341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 503707431397688470352909 188890286774133176382341)
              ·
                refine ⟨35416928770149970571689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188890286774133176382341 35416928770149970571689)
                ·
                  refine ⟨26562696577612477928767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35416928770149970571689 26562696577612477928767)
                  ·
                    rfl

theorem cell20_58197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_58197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58197 prefixEnd_58197 := by exact prefixLift 58197
  have htrace : WordTrace (prefixWord ++ tailWord_58197) baseStart_58197 baseEnd_58197 := by
    simpa [prefixWord, tailWord_58197, baseEnd_58197] using wordTrace_append hprefix tailTrace_58197
  have hstable : (prefixWord ++ tailWord_58197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58197).length < 2 ^ (prefixWord ++ tailWord_58197).sum := by decide
  have hdescent : baseEnd_58197 < baseStart_58197 := by decide
  rcases family_descends (prefixWord ++ tailWord_58197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58204 : List Nat := [2, 2, 4, 2, 1, 1, 3, 5]
def baseStart_58204 : Nat := 118140960795 + 58204 * 2 ^ 59
def prefixEnd_58204 : Nat := 4983230072969 + 3 ^ 40 * 58204 * 2
def baseEnd_58204 : Nat := 8855297189450521565135

theorem tailTrace_58204 : CollatzResearch.WordTrace tailWord_58204 prefixEnd_58204 8855297189450521565135 := by
  unfold tailWord_58204
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061437140572161648454833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1415249520762882197939777 1061437140572161648454833)
  ·
    refine ⟨796077855429121236341125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1061437140572161648454833 796077855429121236341125)
    ·
      refine ⟨149264597892960231813961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 796077855429121236341125 149264597892960231813961)
      ·
        refine ⟨111948448419720173860471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149264597892960231813961 111948448419720173860471)
        ·
          refine ⟨167922672629580260790707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111948448419720173860471 167922672629580260790707)
          ·
            refine ⟨251884008944370391186061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167922672629580260790707 251884008944370391186061)
            ·
              refine ⟨94456503354138896694773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251884008944370391186061 94456503354138896694773)
              ·
                refine ⟨8855297189450521565135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94456503354138896694773 8855297189450521565135)
                ·
                  rfl

theorem cell20_58204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_58204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58204 prefixEnd_58204 := by exact prefixLift 58204
  have htrace : WordTrace (prefixWord ++ tailWord_58204) baseStart_58204 baseEnd_58204 := by
    simpa [prefixWord, tailWord_58204, baseEnd_58204] using wordTrace_append hprefix tailTrace_58204
  have hstable : (prefixWord ++ tailWord_58204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58204).length < 2 ^ (prefixWord ++ tailWord_58204).sum := by decide
  have hdescent : baseEnd_58204 < baseStart_58204 := by decide
  rcases family_descends (prefixWord ++ tailWord_58204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58211 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 3]
def baseStart_58211 : Nat := 118140960795 + 58211 * 2 ^ 59
def prefixEnd_58211 : Nat := 4983230072969 + 3 ^ 40 * 58211 * 2
def baseEnd_58211 : Nat := 26569086559090651462043

theorem tailTrace_58211 : CollatzResearch.WordTrace tailWord_58211 prefixEnd_58211 26569086559090651462043 := by
  unfold tailWord_58211
  simp only [CollatzResearch.WordTrace]
  refine ⟨2123129592118963492414487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1415419728079308994942991 2123129592118963492414487)
  ·
    refine ⟨3184694388178445238621731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2123129592118963492414487 3184694388178445238621731)
    ·
      refine ⟨4777041582267667857932597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3184694388178445238621731 4777041582267667857932597)
      ·
        refine ⟨447847648337593861681181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4777041582267667857932597 447847648337593861681181)
        ·
          refine ⟨167942868126597698130443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447847648337593861681181 167942868126597698130443)
          ·
            refine ⟨251914302189896547195665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167942868126597698130443 251914302189896547195665)
            ·
              refine ⟨188935726642422410396749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251914302189896547195665 188935726642422410396749)
              ·
                refine ⟨70850897490908403898781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188935726642422410396749 70850897490908403898781)
                ·
                  refine ⟨26569086559090651462043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70850897490908403898781 26569086559090651462043)
                  ·
                    rfl

theorem cell20_58211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 3].length) (baseStart_58211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58211 prefixEnd_58211 := by exact prefixLift 58211
  have htrace : WordTrace (prefixWord ++ tailWord_58211) baseStart_58211 baseEnd_58211 := by
    simpa [prefixWord, tailWord_58211, baseEnd_58211] using wordTrace_append hprefix tailTrace_58211
  have hstable : (prefixWord ++ tailWord_58211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58211).length < 2 ^ (prefixWord ++ tailWord_58211).sum := by decide
  have hdescent : baseEnd_58211 < baseStart_58211 := by decide
  rcases family_descends (prefixWord ++ tailWord_58211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58249 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 3]
def baseStart_58249 : Nat := 118140960795 + 58249 * 2 ^ 59
def prefixEnd_58249 : Nat := 4983230072969 + 3 ^ 40 * 58249 * 2
def baseEnd_58249 : Nat := 26586430794531408195221

theorem tailTrace_58249 : CollatzResearch.WordTrace tailWord_58249 prefixEnd_58249 26586430794531408195221 := by
  unfold tailWord_58249
  simp only [CollatzResearch.WordTrace]
  refine ⟨2124515565981295982297801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1416343710654197321531867 2124515565981295982297801)
  ·
    refine ⟨1593386674485971986723351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2124515565981295982297801 1593386674485971986723351)
    ·
      refine ⟨2390080011728957980085027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1593386674485971986723351 2390080011728957980085027)
      ·
        refine ⟨3585120017593436970127541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2390080011728957980085027 3585120017593436970127541)
        ·
          refine ⟨336105001649384715949457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3585120017593436970127541 336105001649384715949457)
          ·
            refine ⟨252078751237038536962093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 336105001649384715949457 252078751237038536962093)
            ·
              refine ⟨94529531713889451360785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252078751237038536962093 94529531713889451360785)
              ·
                refine ⟨70897148785417088520589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94529531713889451360785 70897148785417088520589)
                ·
                  refine ⟨26586430794531408195221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70897148785417088520589 26586430794531408195221)
                  ·
                    rfl

theorem cell20_58249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_58249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58249 prefixEnd_58249 := by exact prefixLift 58249
  have htrace : WordTrace (prefixWord ++ tailWord_58249) baseStart_58249 baseEnd_58249 := by
    simpa [prefixWord, tailWord_58249, baseEnd_58249] using wordTrace_append hprefix tailTrace_58249
  have hstable : (prefixWord ++ tailWord_58249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58249).length < 2 ^ (prefixWord ++ tailWord_58249).sum := by decide
  have hdescent : baseEnd_58249 < baseStart_58249 := by decide
  rcases family_descends (prefixWord ++ tailWord_58249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58284 : List Nat := [2, 2, 1, 1, 1, 1, 2, 10]
def baseStart_58284 : Nat := 118140960795 + 58284 * 2 ^ 59
def prefixEnd_58284 : Nat := 4983230072969 + 3 ^ 40 * 58284 * 2
def baseEnd_58284 : Nat := 8867468582742280676137

theorem tailTrace_58284 : CollatzResearch.WordTrace tailWord_58284 prefixEnd_58284 8867468582742280676137 := by
  unfold tailWord_58284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1062896060427248479910953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1417194747236331306547937 1062896060427248479910953)
  ·
    refine ⟨797172045320436359933215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1062896060427248479910953 797172045320436359933215)
    ·
      refine ⟨1195758067980654539899823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 797172045320436359933215 1195758067980654539899823)
      ·
        refine ⟨1793637101970981809849735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195758067980654539899823 1793637101970981809849735)
        ·
          refine ⟨2690455652956472714774603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793637101970981809849735 2690455652956472714774603)
          ·
            refine ⟨4035683479434709072161905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690455652956472714774603 4035683479434709072161905)
            ·
              refine ⟨3026762609576031804121429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4035683479434709072161905 3026762609576031804121429)
              ·
                refine ⟨8867468582742280676137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3026762609576031804121429 8867468582742280676137)
                ·
                  rfl

theorem cell20_58284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_58284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58284 prefixEnd_58284 := by exact prefixLift 58284
  have htrace : WordTrace (prefixWord ++ tailWord_58284) baseStart_58284 baseEnd_58284 := by
    simpa [prefixWord, tailWord_58284, baseEnd_58284] using wordTrace_append hprefix tailTrace_58284
  have hstable : (prefixWord ++ tailWord_58284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58284).length < 2 ^ (prefixWord ++ tailWord_58284).sum := by decide
  have hdescent : baseEnd_58284 < baseStart_58284 := by decide
  rcases family_descends (prefixWord ++ tailWord_58284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58404 : List Nat := [2, 3, 1, 4, 1, 2, 2, 3, 2]
def baseStart_58404 : Nat := 118140960795 + 58404 * 2 ^ 59
def prefixEnd_58404 : Nat := 4983230072969 + 3 ^ 40 * 58404 * 2
def baseEnd_58404 : Nat := 26657177018039758027921

theorem tailTrace_58404 : CollatzResearch.WordTrace tailWord_58404 prefixEnd_58404 26657177018039758027921 := by
  unfold tailWord_58404
  simp only [CollatzResearch.WordTrace]
  refine ⟨1065084440209878727095133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1420112586946504969460177 1065084440209878727095133)
  ·
    refine ⟨399406665078704522660675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1065084440209878727095133 399406665078704522660675)
    ·
      refine ⟨599109997618056783991013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 399406665078704522660675 599109997618056783991013)
      ·
        refine ⟨112333124553385646998315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 599109997618056783991013 112333124553385646998315)
        ·
          refine ⟨168499686830078470497473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112333124553385646998315 168499686830078470497473)
          ·
            refine ⟨126374765122558852873105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168499686830078470497473 126374765122558852873105)
            ·
              refine ⟨94781073841919139654829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126374765122558852873105 94781073841919139654829)
              ·
                refine ⟨35542902690719677370561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94781073841919139654829 35542902690719677370561)
                ·
                  refine ⟨26657177018039758027921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35542902690719677370561 26657177018039758027921)
                  ·
                    rfl

theorem cell20_58404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_58404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58404 prefixEnd_58404 := by exact prefixLift 58404
  have htrace : WordTrace (prefixWord ++ tailWord_58404) baseStart_58404 baseEnd_58404 := by
    simpa [prefixWord, tailWord_58404, baseEnd_58404] using wordTrace_append hprefix tailTrace_58404
  have hstable : (prefixWord ++ tailWord_58404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58404).length < 2 ^ (prefixWord ++ tailWord_58404).sum := by decide
  have hdescent : baseEnd_58404 < baseStart_58404 := by decide
  rcases family_descends (prefixWord ++ tailWord_58404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58425 : List Nat := [1, 2, 1, 5, 2, 1, 2, 4, 2]
def baseStart_58425 : Nat := 118140960795 + 58425 * 2 ^ 59
def prefixEnd_58425 : Nat := 4983230072969 + 3 ^ 40 * 58425 * 2
def baseEnd_58425 : Nat := 26666761990257018327835

theorem tailTrace_58425 : CollatzResearch.WordTrace tailWord_58425 prefixEnd_58425 26666761990257018327835 := by
  unfold tailWord_58425
  simp only [CollatzResearch.WordTrace]
  refine ⟨2130934813343678040704729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1420623208895785360469819 2130934813343678040704729)
  ·
    refine ⟨1598201110007758530528547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2130934813343678040704729 1598201110007758530528547)
    ·
      refine ⟨2397301665011637795792821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1598201110007758530528547 2397301665011637795792821)
      ·
        refine ⟨224747031094841043355577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2397301665011637795792821 224747031094841043355577)
        ·
          refine ⟨168560273321130782516683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224747031094841043355577 168560273321130782516683)
          ·
            refine ⟨252840409981696173775025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168560273321130782516683 252840409981696173775025)
            ·
              refine ⟨189630307486272130331269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252840409981696173775025 189630307486272130331269)
              ·
                refine ⟨35555682653676024437113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189630307486272130331269 35555682653676024437113)
                ·
                  refine ⟨26666761990257018327835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35555682653676024437113 26666761990257018327835)
                  ·
                    rfl

theorem cell20_58425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 2].length) (baseStart_58425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58425 prefixEnd_58425 := by exact prefixLift 58425
  have htrace : WordTrace (prefixWord ++ tailWord_58425) baseStart_58425 baseEnd_58425 := by
    simpa [prefixWord, tailWord_58425, baseEnd_58425] using wordTrace_append hprefix tailTrace_58425
  have hstable : (prefixWord ++ tailWord_58425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58425).length < 2 ^ (prefixWord ++ tailWord_58425).sum := by decide
  have hdescent : baseEnd_58425 < baseStart_58425 := by decide
  rcases family_descends (prefixWord ++ tailWord_58425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58443 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 9]
def baseStart_58443 : Nat := 118140960795 + 58443 * 2 ^ 59
def prefixEnd_58443 : Nat := 4983230072969 + 3 ^ 40 * 58443 * 2
def baseEnd_58443 : Nat := 26674977680728955727761

theorem tailTrace_58443 : CollatzResearch.WordTrace tailWord_58443 prefixEnd_58443 26674977680728955727761 := by
  unfold tailWord_58443
  simp only [CollatzResearch.WordTrace]
  refine ⟨2131591327278467114859983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1421060884852311409906655 2131591327278467114859983)
  ·
    refine ⟨3197386990917700672289975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2131591327278467114859983 3197386990917700672289975)
    ·
      refine ⟨4796080486376551008434963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3197386990917700672289975 4796080486376551008434963)
      ·
        refine ⟨7194120729564826512652445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4796080486376551008434963 7194120729564826512652445)
        ·
          refine ⟨2697795273586809942244667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7194120729564826512652445 2697795273586809942244667)
          ·
            refine ⟨4046692910380214913367001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697795273586809942244667 4046692910380214913367001)
            ·
              refine ⟨3035019682785161185025251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4046692910380214913367001 3035019682785161185025251)
              ·
                refine ⟨4552529524177741777537877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3035019682785161185025251 4552529524177741777537877)
                ·
                  refine ⟨26674977680728955727761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4552529524177741777537877 26674977680728955727761)
                  ·
                    rfl

theorem cell20_58443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_58443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58443 prefixEnd_58443 := by exact prefixLift 58443
  have htrace : WordTrace (prefixWord ++ tailWord_58443) baseStart_58443 baseEnd_58443 := by
    simpa [prefixWord, tailWord_58443, baseEnd_58443] using wordTrace_append hprefix tailTrace_58443
  have hstable : (prefixWord ++ tailWord_58443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58443).length < 2 ^ (prefixWord ++ tailWord_58443).sum := by decide
  have hdescent : baseEnd_58443 < baseStart_58443 := by decide
  rcases family_descends (prefixWord ++ tailWord_58443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58460 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_58460 : Nat := 118140960795 + 58460 * 2 ^ 59
def prefixEnd_58460 : Nat := 4983230072969 + 3 ^ 40 * 58460 * 2
def baseEnd_58460 : Nat := 26682736943952452161025

theorem tailTrace_58460 : CollatzResearch.WordTrace tailWord_58460 prefixEnd_58460 26682736943952452161025 := by
  unfold tailWord_58460
  simp only [CollatzResearch.WordTrace]
  refine ⟨1066105684108439509114417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1421474245477919345485889 1066105684108439509114417)
  ·
    refine ⟨799579263081329631835813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1066105684108439509114417 799579263081329631835813)
    ·
      refine ⟨149921111827749305969215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 799579263081329631835813 149921111827749305969215)
      ·
        refine ⟨224881667741623958953823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149921111827749305969215 224881667741623958953823)
        ·
          refine ⟨337322501612435938430735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224881667741623958953823 337322501612435938430735)
          ·
            refine ⟨505983752418653907646103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337322501612435938430735 505983752418653907646103)
            ·
              refine ⟨758975628627980861469155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505983752418653907646103 758975628627980861469155)
              ·
                refine ⟨1138463442941971292203733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758975628627980861469155 1138463442941971292203733)
                ·
                  refine ⟨26682736943952452161025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1138463442941971292203733 26682736943952452161025)
                  ·
                    rfl

theorem cell20_58460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_58460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58460 prefixEnd_58460 := by exact prefixLift 58460
  have htrace : WordTrace (prefixWord ++ tailWord_58460) baseStart_58460 baseEnd_58460 := by
    simpa [prefixWord, tailWord_58460, baseEnd_58460] using wordTrace_append hprefix tailTrace_58460
  have hstable : (prefixWord ++ tailWord_58460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58460).length < 2 ^ (prefixWord ++ tailWord_58460).sum := by decide
  have hdescent : baseEnd_58460 < baseStart_58460 := by decide
  rcases family_descends (prefixWord ++ tailWord_58460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58535 : List Nat := [1, 1, 6, 2, 1, 3, 2, 2, 2]
def baseStart_58535 : Nat := 118140960795 + 58535 * 2 ^ 59
def prefixEnd_58535 : Nat := 4983230072969 + 3 ^ 40 * 58535 * 2
def baseEnd_58535 : Nat := 26716968987585524660719

theorem tailTrace_58535 : CollatzResearch.WordTrace tailWord_58535 prefixEnd_58535 26716968987585524660719 := by
  unfold tailWord_58535
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134946842945166827209059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1423297895296777884806039 2134946842945166827209059)
  ·
    refine ⟨3202420264417750240813589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2134946842945166827209059 3202420264417750240813589)
    ·
      refine ⟨150113449894582042538137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3202420264417750240813589 150113449894582042538137)
      ·
        refine ⟨112585087420936531903603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150113449894582042538137 112585087420936531903603)
        ·
          refine ⟨168877631131404797855405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112585087420936531903603 168877631131404797855405)
          ·
            refine ⟨63329111674276799195777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168877631131404797855405 63329111674276799195777)
            ·
              refine ⟨47496833755707599396833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63329111674276799195777 47496833755707599396833)
              ·
                refine ⟨35622625316780699547625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47496833755707599396833 35622625316780699547625)
                ·
                  refine ⟨26716968987585524660719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35622625316780699547625 26716968987585524660719)
                  ·
                    rfl

theorem cell20_58535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 2].length) (baseStart_58535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58535 prefixEnd_58535 := by exact prefixLift 58535
  have htrace : WordTrace (prefixWord ++ tailWord_58535) baseStart_58535 baseEnd_58535 := by
    simpa [prefixWord, tailWord_58535, baseEnd_58535] using wordTrace_append hprefix tailTrace_58535
  have hstable : (prefixWord ++ tailWord_58535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58535).length < 2 ^ (prefixWord ++ tailWord_58535).sum := by decide
  have hdescent : baseEnd_58535 < baseStart_58535 := by decide
  rcases family_descends (prefixWord ++ tailWord_58535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58560 : List Nat := [2, 1, 1, 2, 6, 1, 1, 2, 4]
def baseStart_58560 : Nat := 118140960795 + 58560 * 2 ^ 59
def prefixEnd_58560 : Nat := 4983230072969 + 3 ^ 40 * 58560 * 2
def baseEnd_58560 : Nat := 26728379668796548827283

theorem tailTrace_58560 : CollatzResearch.WordTrace tailWord_58560 prefixEnd_58560 26728379668796548827283 := by
  unfold tailWord_58560
  simp only [CollatzResearch.WordTrace]
  refine ⟨1067929333927298048434567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1423905778569730731246089 1067929333927298048434567)
  ·
    refine ⟨1601894000890947072651851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1067929333927298048434567 1601894000890947072651851)
    ·
      refine ⟨2402841001336420608977777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1601894000890947072651851 2402841001336420608977777)
      ·
        refine ⟨1802130751002315456733333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2402841001336420608977777 1802130751002315456733333)
        ·
          refine ⟨84474878953233537034375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1802130751002315456733333 84474878953233537034375)
          ·
            refine ⟨126712318429850305551563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84474878953233537034375 126712318429850305551563)
            ·
              refine ⟨190068477644775458327345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126712318429850305551563 190068477644775458327345)
              ·
                refine ⟨142551358233581593745509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190068477644775458327345 142551358233581593745509)
                ·
                  refine ⟨26728379668796548827283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142551358233581593745509 26728379668796548827283)
                  ·
                    rfl

theorem cell20_58560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 2, 4].length) (baseStart_58560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58560 prefixEnd_58560 := by exact prefixLift 58560
  have htrace : WordTrace (prefixWord ++ tailWord_58560) baseStart_58560 baseEnd_58560 := by
    simpa [prefixWord, tailWord_58560, baseEnd_58560] using wordTrace_append hprefix tailTrace_58560
  have hstable : (prefixWord ++ tailWord_58560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58560).length < 2 ^ (prefixWord ++ tailWord_58560).sum := by decide
  have hdescent : baseEnd_58560 < baseStart_58560 := by decide
  rcases family_descends (prefixWord ++ tailWord_58560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58622 : List Nat := [4, 2, 2, 1, 1, 2, 4, 4]
def baseStart_58622 : Nat := 118140960795 + 58622 * 2 ^ 59
def prefixEnd_58622 : Nat := 4983230072969 + 3 ^ 40 * 58622 * 2
def baseEnd_58622 : Nat := 8918892719399962920121

theorem tailTrace_58622 : CollatzResearch.WordTrace tailWord_58622 prefixEnd_58622 8918892719399962920121 := by
  unfold tailWord_58622
  simp only [CollatzResearch.WordTrace]
  refine ⟨267264999203747585703265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1425413329086653790417413 267264999203747585703265)
  ·
    refine ⟨200448749402810689277449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267264999203747585703265 200448749402810689277449)
    ·
      refine ⟨150336562052108016958087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200448749402810689277449 150336562052108016958087)
      ·
        refine ⟨225504843078162025437131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150336562052108016958087 225504843078162025437131)
        ·
          refine ⟨338257264617243038155697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225504843078162025437131 338257264617243038155697)
          ·
            refine ⟨253692948462932278616773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338257264617243038155697 253692948462932278616773)
            ·
              refine ⟨47567427836799802240645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253692948462932278616773 47567427836799802240645)
              ·
                refine ⟨8918892719399962920121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47567427836799802240645 8918892719399962920121)
                ·
                  rfl

theorem cell20_58622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_58622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58622 prefixEnd_58622 := by exact prefixLift 58622
  have htrace : WordTrace (prefixWord ++ tailWord_58622) baseStart_58622 baseEnd_58622 := by
    simpa [prefixWord, tailWord_58622, baseEnd_58622] using wordTrace_append hprefix tailTrace_58622
  have hstable : (prefixWord ++ tailWord_58622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58622).length < 2 ^ (prefixWord ++ tailWord_58622).sum := by decide
  have hdescent : baseEnd_58622 < baseStart_58622 := by decide
  rcases family_descends (prefixWord ++ tailWord_58622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58632 : List Nat := [2, 1, 3, 2, 4, 2, 1, 3, 2]
def baseStart_58632 : Nat := 118140960795 + 58632 * 2 ^ 59
def prefixEnd_58632 : Nat := 4983230072969 + 3 ^ 40 * 58632 * 2
def baseEnd_58632 : Nat := 26761242430684298426989

theorem tailTrace_58632 : CollatzResearch.WordTrace tailWord_58632 prefixEnd_58632 26761242430684298426989 := by
  unfold tailWord_58632
  simp only [CollatzResearch.WordTrace]
  refine ⟨1069242361796876196745075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1425656482395834928993433 1069242361796876196745075)
  ·
    refine ⟨1603863542695314295117613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1069242361796876196745075 1603863542695314295117613)
    ·
      refine ⟨601448828510742860669105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1603863542695314295117613 601448828510742860669105)
      ·
        refine ⟨451086621383057145501829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601448828510742860669105 451086621383057145501829)
        ·
          refine ⟨84578741509323214781593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 451086621383057145501829 84578741509323214781593)
          ·
            refine ⟨63434056131992411086195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84578741509323214781593 63434056131992411086195)
            ·
              refine ⟨95151084197988616629293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63434056131992411086195 95151084197988616629293)
              ·
                refine ⟨35681656574245731235985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95151084197988616629293 35681656574245731235985)
                ·
                  refine ⟨26761242430684298426989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35681656574245731235985 26761242430684298426989)
                  ·
                    rfl

theorem cell20_58632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 2].length) (baseStart_58632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58632 prefixEnd_58632 := by exact prefixLift 58632
  have htrace : WordTrace (prefixWord ++ tailWord_58632) baseStart_58632 baseEnd_58632 := by
    simpa [prefixWord, tailWord_58632, baseEnd_58632] using wordTrace_append hprefix tailTrace_58632
  have hstable : (prefixWord ++ tailWord_58632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58632).length < 2 ^ (prefixWord ++ tailWord_58632).sum := by decide
  have hdescent : baseEnd_58632 < baseStart_58632 := by decide
  rcases family_descends (prefixWord ++ tailWord_58632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58633 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 7]
def baseStart_58633 : Nat := 118140960795 + 58633 * 2 ^ 59
def prefixEnd_58633 : Nat := 4983230072969 + 3 ^ 40 * 58633 * 2
def baseEnd_58633 : Nat := 26761698857932739393651

theorem tailTrace_58633 : CollatzResearch.WordTrace tailWord_58633 prefixEnd_58633 26761698857932739393651 := by
  unfold tailWord_58633
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138521196590129564276553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1425680797726753042851035 2138521196590129564276553)
  ·
    refine ⟨1603890897442597173207415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2138521196590129564276553 1603890897442597173207415)
    ·
      refine ⟨2405836346163895759811123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603890897442597173207415 2405836346163895759811123)
      ·
        refine ⟨3608754519245843639716685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405836346163895759811123 3608754519245843639716685)
        ·
          refine ⟨1353282944717191364893757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3608754519245843639716685 1353282944717191364893757)
          ·
            refine ⟨507481104268946761835159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1353282944717191364893757 507481104268946761835159)
            ·
              refine ⟨761221656403420142752739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507481104268946761835159 761221656403420142752739)
              ·
                refine ⟨1141832484605130214129109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761221656403420142752739 1141832484605130214129109)
                ·
                  refine ⟨26761698857932739393651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1141832484605130214129109 26761698857932739393651)
                  ·
                    rfl

theorem cell20_58633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_58633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58633 prefixEnd_58633 := by exact prefixLift 58633
  have htrace : WordTrace (prefixWord ++ tailWord_58633) baseStart_58633 baseEnd_58633 := by
    simpa [prefixWord, tailWord_58633, baseEnd_58633] using wordTrace_append hprefix tailTrace_58633
  have hstable : (prefixWord ++ tailWord_58633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58633).length < 2 ^ (prefixWord ++ tailWord_58633).sum := by decide
  have hdescent : baseEnd_58633 < baseStart_58633 := by decide
  rcases family_descends (prefixWord ++ tailWord_58633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58650 : List Nat := [3, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_58650 : Nat := 118140960795 + 58650 * 2 ^ 59
def prefixEnd_58650 : Nat := 4983230072969 + 3 ^ 40 * 58650 * 2
def baseEnd_58650 : Nat := 26769458121156235826915

theorem tailTrace_58650 : CollatzResearch.WordTrace tailWord_58650 prefixEnd_58650 26769458121156235826915 := by
  unfold tailWord_58650
  simp only [CollatzResearch.WordTrace]
  refine ⟨534785309382135366911351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1426094158352360978430269 534785309382135366911351)
  ·
    refine ⟨802177964073203050367027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 534785309382135366911351 802177964073203050367027)
    ·
      refine ⟨1203266946109804575550541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802177964073203050367027 1203266946109804575550541)
      ·
        refine ⟨451225104791176715831453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1203266946109804575550541 451225104791176715831453)
        ·
          refine ⟨169209414296691268436795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451225104791176715831453 169209414296691268436795)
          ·
            refine ⟨253814121445036902655193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169209414296691268436795 253814121445036902655193)
            ·
              refine ⟨190360591083777676991395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253814121445036902655193 190360591083777676991395)
              ·
                refine ⟨285540886625666515487093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190360591083777676991395 285540886625666515487093)
                ·
                  refine ⟨26769458121156235826915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285540886625666515487093 26769458121156235826915)
                  ·
                    rfl

theorem cell20_58650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_58650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58650 prefixEnd_58650 := by exact prefixLift 58650
  have htrace : WordTrace (prefixWord ++ tailWord_58650) baseStart_58650 baseEnd_58650 := by
    simpa [prefixWord, tailWord_58650, baseEnd_58650] using wordTrace_append hprefix tailTrace_58650
  have hstable : (prefixWord ++ tailWord_58650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58650).length < 2 ^ (prefixWord ++ tailWord_58650).sum := by decide
  have hdescent : baseEnd_58650 < baseStart_58650 := by decide
  rcases family_descends (prefixWord ++ tailWord_58650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58653 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 4]
def baseStart_58653 : Nat := 118140960795 + 58653 * 2 ^ 59
def prefixEnd_58653 : Nat := 4983230072969 + 3 ^ 40 * 58653 * 2
def baseEnd_58653 : Nat := 26770827402901558726903

theorem tailTrace_58653 : CollatzResearch.WordTrace tailWord_58653 prefixEnd_58653 26770827402901558726903 := by
  unfold tailWord_58653
  simp only [CollatzResearch.WordTrace]
  refine ⟨2139250656517672980004613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1426167104345115320003075 2139250656517672980004613)
  ·
    refine ⟨401109498097063683750865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2139250656517672980004613 401109498097063683750865)
    ·
      refine ⟨300832123572797762813149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401109498097063683750865 300832123572797762813149)
      ·
        refine ⟨112812046339799161054931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300832123572797762813149 112812046339799161054931)
        ·
          refine ⟨169218069509698741582397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112812046339799161054931 169218069509698741582397)
          ·
            refine ⟨63456776066137028093399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169218069509698741582397 63456776066137028093399)
            ·
              refine ⟨95185164099205542140099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63456776066137028093399 95185164099205542140099)
              ·
                refine ⟨142777746148808313210149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95185164099205542140099 142777746148808313210149)
                ·
                  refine ⟨26770827402901558726903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142777746148808313210149 26770827402901558726903)
                  ·
                    rfl

theorem cell20_58653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_58653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58653 prefixEnd_58653 := by exact prefixLift 58653
  have htrace : WordTrace (prefixWord ++ tailWord_58653) baseStart_58653 baseEnd_58653 := by
    simpa [prefixWord, tailWord_58653, baseEnd_58653] using wordTrace_append hprefix tailTrace_58653
  have hstable : (prefixWord ++ tailWord_58653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58653).length < 2 ^ (prefixWord ++ tailWord_58653).sum := by decide
  have hdescent : baseEnd_58653 < baseStart_58653 := by decide
  rcases family_descends (prefixWord ++ tailWord_58653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58701 : List Nat := [1, 6, 1, 3, 1, 1, 2, 2, 3]
def baseStart_58701 : Nat := 118140960795 + 58701 * 2 ^ 59
def prefixEnd_58701 : Nat := 4983230072969 + 3 ^ 40 * 58701 * 2
def baseEnd_58701 : Nat := 26792735910826725126707

theorem tailTrace_58701 : CollatzResearch.WordTrace tailWord_58701 prefixEnd_58701 26792735910826725126707 := by
  unfold tailWord_58701
  simp only [CollatzResearch.WordTrace]
  refine ⟨2141001360343777177751957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1427334240229184785167971 2141001360343777177751957)
  ·
    refine ⟨100359438766114555207123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2141001360343777177751957 100359438766114555207123)
    ·
      refine ⟨150539158149171832810685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100359438766114555207123 150539158149171832810685)
      ·
        refine ⟨56452184305939437304007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150539158149171832810685 56452184305939437304007)
        ·
          refine ⟨84678276458909155956011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56452184305939437304007 84678276458909155956011)
          ·
            refine ⟨127017414688363733934017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84678276458909155956011 127017414688363733934017)
            ·
              refine ⟨95263061016272800450513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127017414688363733934017 95263061016272800450513)
              ·
                refine ⟨71447295762204600337885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95263061016272800450513 71447295762204600337885)
                ·
                  refine ⟨26792735910826725126707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71447295762204600337885 26792735910826725126707)
                  ·
                    rfl

theorem cell20_58701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_58701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58701 prefixEnd_58701 := by exact prefixLift 58701
  have htrace : WordTrace (prefixWord ++ tailWord_58701) baseStart_58701 baseEnd_58701 := by
    simpa [prefixWord, tailWord_58701, baseEnd_58701] using wordTrace_append hprefix tailTrace_58701
  have hstable : (prefixWord ++ tailWord_58701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58701).length < 2 ^ (prefixWord ++ tailWord_58701).sum := by decide
  have hdescent : baseEnd_58701 < baseStart_58701 := by decide
  rcases family_descends (prefixWord ++ tailWord_58701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58712 : List Nat := [2, 1, 2, 2, 1, 1, 5, 4, 2]
def baseStart_58712 : Nat := 118140960795 + 58712 * 2 ^ 59
def prefixEnd_58712 : Nat := 4983230072969 + 3 ^ 40 * 58712 * 2
def baseEnd_58712 : Nat := 26797756610559575759995

theorem tailTrace_58712 : CollatzResearch.WordTrace tailWord_58712 prefixEnd_58712 26797756610559575759995 := by
  unfold tailWord_58712
  simp only [CollatzResearch.WordTrace]
  refine ⟨1070701281651963028201195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1427601708869284037601593 1070701281651963028201195)
  ·
    refine ⟨1606051922477944542301793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1070701281651963028201195 1606051922477944542301793)
    ·
      refine ⟨1204538941858458406726345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1606051922477944542301793 1204538941858458406726345)
      ·
        refine ⟨903404206393843805044759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1204538941858458406726345 903404206393843805044759)
        ·
          refine ⟨1355106309590765707567139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903404206393843805044759 1355106309590765707567139)
          ·
            refine ⟨2032659464386148561350709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355106309590765707567139 2032659464386148561350709)
            ·
              refine ⟨190561824786201427626629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2032659464386148561350709 190561824786201427626629)
              ·
                refine ⟨35730342147412767679993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190561824786201427626629 35730342147412767679993)
                ·
                  refine ⟨26797756610559575759995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35730342147412767679993 26797756610559575759995)
                  ·
                    rfl

theorem cell20_58712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 2].length) (baseStart_58712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58712 prefixEnd_58712 := by exact prefixLift 58712
  have htrace : WordTrace (prefixWord ++ tailWord_58712) baseStart_58712 baseEnd_58712 := by
    simpa [prefixWord, tailWord_58712, baseEnd_58712] using wordTrace_append hprefix tailTrace_58712
  have hstable : (prefixWord ++ tailWord_58712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58712).length < 2 ^ (prefixWord ++ tailWord_58712).sum := by decide
  have hdescent : baseEnd_58712 < baseStart_58712 := by decide
  rcases family_descends (prefixWord ++ tailWord_58712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58733 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 6]
def baseStart_58733 : Nat := 118140960795 + 58733 * 2 ^ 59
def prefixEnd_58733 : Nat := 4983230072969 + 3 ^ 40 * 58733 * 2
def baseEnd_58733 : Nat := 26807341582776836059909

theorem tailTrace_58733 : CollatzResearch.WordTrace tailWord_58733 prefixEnd_58733 26807341582776836059909 := by
  unfold tailWord_58733
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142168496227846642916853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1428112330818564428611235 2142168496227846642916853)
  ·
    refine ⟨200828296521360622773455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2142168496227846642916853 200828296521360622773455)
    ·
      refine ⟨301242444782040934160183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200828296521360622773455 301242444782040934160183)
      ·
        refine ⟨451863667173061401240275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301242444782040934160183 451863667173061401240275)
        ·
          refine ⟨677795500759592101860413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451863667173061401240275 677795500759592101860413)
          ·
            refine ⟨254173312784847038197655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 677795500759592101860413 254173312784847038197655)
            ·
              refine ⟨381259969177270557296483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254173312784847038197655 381259969177270557296483)
              ·
                refine ⟨571889953765905835944725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381259969177270557296483 571889953765905835944725)
                ·
                  refine ⟨26807341582776836059909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 571889953765905835944725 26807341582776836059909)
                  ·
                    rfl

theorem cell20_58733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_58733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58733 prefixEnd_58733 := by exact prefixLift 58733
  have htrace : WordTrace (prefixWord ++ tailWord_58733) baseStart_58733 baseEnd_58733 := by
    simpa [prefixWord, tailWord_58733, baseEnd_58733] using wordTrace_append hprefix tailTrace_58733
  have hstable : (prefixWord ++ tailWord_58733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58733).length < 2 ^ (prefixWord ++ tailWord_58733).sum := by decide
  have hdescent : baseEnd_58733 < baseStart_58733 := by decide
  rcases family_descends (prefixWord ++ tailWord_58733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58747 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_58747 : Nat := 118140960795 + 58747 * 2 ^ 59
def prefixEnd_58747 : Nat := 4983230072969 + 3 ^ 40 * 58747 * 2
def baseEnd_58747 : Nat := 26813731564255009593185

theorem tailTrace_58747 : CollatzResearch.WordTrace tailWord_58747 prefixEnd_58747 26813731564255009593185 := by
  unfold tailWord_58747
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142679118177127033926495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1428452745451418022617663 2142679118177127033926495)
  ·
    refine ⟨3214018677265690550889743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2142679118177127033926495 3214018677265690550889743)
    ·
      refine ⟨4821028015898535826334615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3214018677265690550889743 4821028015898535826334615)
      ·
        refine ⟨7231542023847803739501923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821028015898535826334615 7231542023847803739501923)
        ·
          refine ⟨10847313035771705609252885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7231542023847803739501923 10847313035771705609252885)
          ·
            refine ⟨508467798551798700433729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10847313035771705609252885 508467798551798700433729)
            ·
              refine ⟨381350848913849025325297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508467798551798700433729 381350848913849025325297)
              ·
                refine ⟨286013136685386768993973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381350848913849025325297 286013136685386768993973)
                ·
                  refine ⟨26813731564255009593185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286013136685386768993973 26813731564255009593185)
                  ·
                    rfl

theorem cell20_58747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_58747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58747 prefixEnd_58747 := by exact prefixLift 58747
  have htrace : WordTrace (prefixWord ++ tailWord_58747) baseStart_58747 baseEnd_58747 := by
    simpa [prefixWord, tailWord_58747, baseEnd_58747] using wordTrace_append hprefix tailTrace_58747
  have hstable : (prefixWord ++ tailWord_58747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58747).length < 2 ^ (prefixWord ++ tailWord_58747).sum := by decide
  have hdescent : baseEnd_58747 < baseStart_58747 := by decide
  rcases family_descends (prefixWord ++ tailWord_58747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58778 : List Nat := [3, 1, 1, 4, 1, 1, 2, 7]
def baseStart_58778 : Nat := 118140960795 + 58778 * 2 ^ 59
def prefixEnd_58778 : Nat := 4983230072969 + 3 ^ 40 * 58778 * 2
def baseEnd_58778 : Nat := 8942626936318893186575

theorem tailTrace_58778 : CollatzResearch.WordTrace tailWord_58778 prefixEnd_58778 8942626936318893186575 := by
  unfold tailWord_58778
  simp only [CollatzResearch.WordTrace]
  refine ⟨535952445266204832076247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1429206520709879552203325 535952445266204832076247)
  ·
    refine ⟨803928667899307248114371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 535952445266204832076247 803928667899307248114371)
    ·
      refine ⟨1205893001848960872171557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803928667899307248114371 1205893001848960872171557)
      ·
        refine ⟨226104937846680163532167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1205893001848960872171557 226104937846680163532167)
        ·
          refine ⟨339157406770020245298251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226104937846680163532167 339157406770020245298251)
          ·
            refine ⟨508736110155030367947377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339157406770020245298251 508736110155030367947377)
            ·
              refine ⟨381552082616272775960533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508736110155030367947377 381552082616272775960533)
              ·
                refine ⟨8942626936318893186575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 381552082616272775960533 8942626936318893186575)
                ·
                  rfl

theorem cell20_58778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_58778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58778 prefixEnd_58778 := by exact prefixLift 58778
  have htrace : WordTrace (prefixWord ++ tailWord_58778) baseStart_58778 baseEnd_58778 := by
    simpa [prefixWord, tailWord_58778, baseEnd_58778] using wordTrace_append hprefix tailTrace_58778
  have hstable : (prefixWord ++ tailWord_58778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58778).length < 2 ^ (prefixWord ++ tailWord_58778).sum := by decide
  have hdescent : baseEnd_58778 < baseStart_58778 := by decide
  rcases family_descends (prefixWord ++ tailWord_58778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58805 : List Nat := [1, 3, 3, 2, 2, 1, 3, 3, 2]
def baseStart_58805 : Nat := 118140960795 + 58805 * 2 ^ 59
def prefixEnd_58805 : Nat := 4983230072969 + 3 ^ 40 * 58805 * 2
def baseEnd_58805 : Nat := 26840204344664585659615

theorem tailTrace_58805 : CollatzResearch.WordTrace tailWord_58805 prefixEnd_58805 26840204344664585659615 := by
  unfold tailWord_58805
  simp only [CollatzResearch.WordTrace]
  refine ⟨2144794551967002939537869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1429863034644668626358579 2144794551967002939537869)
  ·
    refine ⟨804297956987626102326701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2144794551967002939537869 804297956987626102326701)
    ·
      refine ⟨301611733870359788372513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 804297956987626102326701 301611733870359788372513)
      ·
        refine ⟨226208800402769841279385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301611733870359788372513 226208800402769841279385)
        ·
          refine ⟨169656600302077380959539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226208800402769841279385 169656600302077380959539)
          ·
            refine ⟨254484900453116071439309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169656600302077380959539 254484900453116071439309)
            ·
              refine ⟨95431837669918526789741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254484900453116071439309 95431837669918526789741)
              ·
                refine ⟨35786939126219447546153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95431837669918526789741 35786939126219447546153)
                ·
                  refine ⟨26840204344664585659615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35786939126219447546153 26840204344664585659615)
                  ·
                    rfl

theorem cell20_58805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_58805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58805 prefixEnd_58805 := by exact prefixLift 58805
  have htrace : WordTrace (prefixWord ++ tailWord_58805) baseStart_58805 baseEnd_58805 := by
    simpa [prefixWord, tailWord_58805, baseEnd_58805] using wordTrace_append hprefix tailTrace_58805
  have hstable : (prefixWord ++ tailWord_58805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58805).length < 2 ^ (prefixWord ++ tailWord_58805).sum := by decide
  have hdescent : baseEnd_58805 < baseStart_58805 := by decide
  rcases family_descends (prefixWord ++ tailWord_58805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58812 : List Nat := [2, 2, 2, 4, 3, 1, 6]
def baseStart_58812 : Nat := 118140960795 + 58812 * 2 ^ 59
def prefixEnd_58812 : Nat := 4983230072969 + 3 ^ 40 * 58812 * 2
def baseEnd_58812 : Nat := 2982599926155963602917

theorem tailTrace_58812 : CollatzResearch.WordTrace tailWord_58812 prefixEnd_58812 2982599926155963602917 := by
  unfold tailWord_58812
  simp only [CollatzResearch.WordTrace]
  refine ⟨1072524931470821567521345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1430033241961095423361793 1072524931470821567521345)
  ·
    refine ⟨804393698603116175641009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1072524931470821567521345 804393698603116175641009)
    ·
      refine ⟨603295273952337131730757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 804393698603116175641009 603295273952337131730757)
      ·
        refine ⟨113117863866063212199517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 603295273952337131730757 113117863866063212199517)
        ·
          refine ⟨42419198949773704574819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113117863866063212199517 42419198949773704574819)
          ·
            refine ⟨63628798424660556862229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42419198949773704574819 63628798424660556862229)
            ·
              refine ⟨2982599926155963602917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63628798424660556862229 2982599926155963602917)
              ·
                rfl

theorem cell20_58812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 6].length) (baseStart_58812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58812 prefixEnd_58812 := by exact prefixLift 58812
  have htrace : WordTrace (prefixWord ++ tailWord_58812) baseStart_58812 baseEnd_58812 := by
    simpa [prefixWord, tailWord_58812, baseEnd_58812] using wordTrace_append hprefix tailTrace_58812
  have hstable : (prefixWord ++ tailWord_58812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58812).length < 2 ^ (prefixWord ++ tailWord_58812).sum := by decide
  have hdescent : baseEnd_58812 < baseStart_58812 := by decide
  rcases family_descends (prefixWord ++ tailWord_58812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58818 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 4]
def baseStart_58818 : Nat := 118140960795 + 58818 * 2 ^ 59
def prefixEnd_58818 : Nat := 4983230072969 + 3 ^ 40 * 58818 * 2
def baseEnd_58818 : Nat := 26846137898894318226229

theorem tailTrace_58818 : CollatzResearch.WordTrace tailWord_58818 prefixEnd_58818 26846137898894318226229 := by
  unfold tailWord_58818
  simp only [CollatzResearch.WordTrace]
  refine ⟨536317175229976539940277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1430179133946604106507405 536317175229976539940277)
  ·
    refine ⟨50279735177810300619401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 536317175229976539940277 50279735177810300619401)
    ·
      refine ⟨37709801383357725464551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50279735177810300619401 37709801383357725464551)
      ·
        refine ⟨56564702075036588196827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37709801383357725464551 56564702075036588196827)
        ·
          refine ⟨84847053112554882295241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56564702075036588196827 84847053112554882295241)
          ·
            refine ⟨63635289834416161721431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84847053112554882295241 63635289834416161721431)
            ·
              refine ⟨95452934751624242582147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63635289834416161721431 95452934751624242582147)
              ·
                refine ⟨143179402127436363873221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95452934751624242582147 143179402127436363873221)
                ·
                  refine ⟨26846137898894318226229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143179402127436363873221 26846137898894318226229)
                  ·
                    rfl

theorem cell20_58818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_58818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58818 prefixEnd_58818 := by exact prefixLift 58818
  have htrace : WordTrace (prefixWord ++ tailWord_58818) baseStart_58818 baseEnd_58818 := by
    simpa [prefixWord, tailWord_58818, baseEnd_58818] using wordTrace_append hprefix tailTrace_58818
  have hstable : (prefixWord ++ tailWord_58818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58818).length < 2 ^ (prefixWord ++ tailWord_58818).sum := by decide
  have hdescent : baseEnd_58818 < baseStart_58818 := by decide
  rcases family_descends (prefixWord ++ tailWord_58818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58823 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_58823 : Nat := 118140960795 + 58823 * 2 ^ 59
def prefixEnd_58823 : Nat := 4983230072969 + 3 ^ 40 * 58823 * 2
def baseEnd_58823 : Nat := 26848420035136523059541

theorem tailTrace_58823 : CollatzResearch.WordTrace tailWord_58823 prefixEnd_58823 26848420035136523059541 := by
  unfold tailWord_58823
  simp only [CollatzResearch.WordTrace]
  refine ⟨2145451065901792013693123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1430300710601194675795415 2145451065901792013693123)
  ·
    refine ⟨3218176598852688020539685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2145451065901792013693123 3218176598852688020539685)
    ·
      refine ⟨603408112284879003851191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3218176598852688020539685 603408112284879003851191)
      ·
        refine ⟨905112168427318505776787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603408112284879003851191 905112168427318505776787)
        ·
          refine ⟨1357668252640977758665181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905112168427318505776787 1357668252640977758665181)
          ·
            refine ⟨509125594740366659499443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1357668252640977758665181 509125594740366659499443)
            ·
              refine ⟨763688392110549989249165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 509125594740366659499443 763688392110549989249165)
              ·
                refine ⟨286383147041456245968437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 763688392110549989249165 286383147041456245968437)
                ·
                  refine ⟨26848420035136523059541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286383147041456245968437 26848420035136523059541)
                  ·
                    rfl

theorem cell20_58823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_58823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58823 prefixEnd_58823 := by exact prefixLift 58823
  have htrace : WordTrace (prefixWord ++ tailWord_58823) baseStart_58823 baseEnd_58823 := by
    simpa [prefixWord, tailWord_58823, baseEnd_58823] using wordTrace_append hprefix tailTrace_58823
  have hstable : (prefixWord ++ tailWord_58823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58823).length < 2 ^ (prefixWord ++ tailWord_58823).sum := by decide
  have hdescent : baseEnd_58823 < baseStart_58823 := by decide
  rcases family_descends (prefixWord ++ tailWord_58823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58826 : List Nat := [3, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_58826 : Nat := 118140960795 + 58826 * 2 ^ 59
def prefixEnd_58826 : Nat := 4983230072969 + 3 ^ 40 * 58826 * 2
def baseEnd_58826 : Nat := 26849789316881845959529

theorem tailTrace_58826 : CollatzResearch.WordTrace tailWord_58826 prefixEnd_58826 26849789316881845959529 := by
  unfold tailWord_58826
  simp only [CollatzResearch.WordTrace]
  refine ⟨536390121222730881513083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1430373656593949017368221 536390121222730881513083)
  ·
    refine ⟨804585181834096322269625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536390121222730881513083 804585181834096322269625)
    ·
      refine ⟨603438886375572241702219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 804585181834096322269625 603438886375572241702219)
      ·
        refine ⟨905158329563358362553329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603438886375572241702219 905158329563358362553329)
        ·
          refine ⟨678868747172518771914997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 905158329563358362553329 678868747172518771914997)
          ·
            refine ⟨63643945047423634867031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 678868747172518771914997 63643945047423634867031)
            ·
              refine ⟨95465917571135452300547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63643945047423634867031 95465917571135452300547)
              ·
                refine ⟨143198876356703178450821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95465917571135452300547 143198876356703178450821)
                ·
                  refine ⟨26849789316881845959529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143198876356703178450821 26849789316881845959529)
                  ·
                    rfl

theorem cell20_58826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_58826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58826 prefixEnd_58826 := by exact prefixLift 58826
  have htrace : WordTrace (prefixWord ++ tailWord_58826) baseStart_58826 baseEnd_58826 := by
    simpa [prefixWord, tailWord_58826, baseEnd_58826] using wordTrace_append hprefix tailTrace_58826
  have hstable : (prefixWord ++ tailWord_58826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58826).length < 2 ^ (prefixWord ++ tailWord_58826).sum := by decide
  have hdescent : baseEnd_58826 < baseStart_58826 := by decide
  rcases family_descends (prefixWord ++ tailWord_58826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58881 : List Nat := [1, 2, 4, 1, 4, 1, 1, 4, 2]
def baseStart_58881 : Nat := 118140960795 + 58881 * 2 ^ 59
def prefixEnd_58881 : Nat := 4983230072969 + 3 ^ 40 * 58881 * 2
def baseEnd_58881 : Nat := 26874892815546099125971

theorem tailTrace_58881 : CollatzResearch.WordTrace tailWord_58881 prefixEnd_58881 26874892815546099125971 := by
  unfold tailWord_58881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2147566499691667919304497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1431710999794445279536331 2147566499691667919304497)
  ·
    refine ⟨1610674874768750939478373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2147566499691667919304497 1610674874768750939478373)
    ·
      refine ⟨302001539019140801152195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1610674874768750939478373 302001539019140801152195)
      ·
        refine ⟨453002308528711201728293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302001539019140801152195 453002308528711201728293)
        ·
          refine ⟨84937932849133350324055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 453002308528711201728293 84937932849133350324055)
          ·
            refine ⟨127406899273700025486083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84937932849133350324055 127406899273700025486083)
            ·
              refine ⟨191110348910550038229125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127406899273700025486083 191110348910550038229125)
              ·
                refine ⟨35833190420728132167961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191110348910550038229125 35833190420728132167961)
                ·
                  refine ⟨26874892815546099125971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35833190420728132167961 26874892815546099125971)
                  ·
                    rfl

theorem cell20_58881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 4, 2].length) (baseStart_58881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58881 prefixEnd_58881 := by exact prefixLift 58881
  have htrace : WordTrace (prefixWord ++ tailWord_58881) baseStart_58881 baseEnd_58881 := by
    simpa [prefixWord, tailWord_58881, baseEnd_58881] using wordTrace_append hprefix tailTrace_58881
  have hstable : (prefixWord ++ tailWord_58881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58881).length < 2 ^ (prefixWord ++ tailWord_58881).sum := by decide
  have hdescent : baseEnd_58881 < baseStart_58881 := by decide
  rcases family_descends (prefixWord ++ tailWord_58881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58909 : List Nat := [1, 4, 2, 2, 1, 1, 5, 4]
def baseStart_58909 : Nat := 118140960795 + 58909 * 2 ^ 59
def prefixEnd_58909 : Nat := 4983230072969 + 3 ^ 40 * 58909 * 2
def baseEnd_58909 : Nat := 8962557592834148730841

theorem tailTrace_58909 : CollatzResearch.WordTrace tailWord_58909 prefixEnd_58909 8962557592834148730841 := by
  unfold tailWord_58909
  simp only [CollatzResearch.WordTrace]
  refine ⟨2148587743590228701323781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1432391829060152467549187 2148587743590228701323781)
  ·
    refine ⟨402860201923167881498209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2148587743590228701323781 402860201923167881498209)
    ·
      refine ⟨302145151442375911123657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402860201923167881498209 302145151442375911123657)
      ·
        refine ⟨226608863581781933342743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302145151442375911123657 226608863581781933342743)
        ·
          refine ⟨339913295372672900014115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226608863581781933342743 339913295372672900014115)
          ·
            refine ⟨509869943059009350021173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339913295372672900014115 509869943059009350021173)
            ·
              refine ⟨47800307161782126564485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 509869943059009350021173 47800307161782126564485)
              ·
                refine ⟨8962557592834148730841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47800307161782126564485 8962557592834148730841)
                ·
                  rfl

theorem cell20_58909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 4].length) (baseStart_58909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58909 prefixEnd_58909 := by exact prefixLift 58909
  have htrace : WordTrace (prefixWord ++ tailWord_58909) baseStart_58909 baseEnd_58909 := by
    simpa [prefixWord, tailWord_58909, baseEnd_58909] using wordTrace_append hprefix tailTrace_58909
  have hstable : (prefixWord ++ tailWord_58909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58909).length < 2 ^ (prefixWord ++ tailWord_58909).sum := by decide
  have hdescent : baseEnd_58909 < baseStart_58909 := by decide
  rcases family_descends (prefixWord ++ tailWord_58909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58933 : List Nat := [1, 3, 3, 1, 1, 5, 1, 2, 3]
def baseStart_58933 : Nat := 118140960795 + 58933 * 2 ^ 59
def prefixEnd_58933 : Nat := 4983230072969 + 3 ^ 40 * 58933 * 2
def baseEnd_58933 : Nat := 26898627032465029392425

theorem tailTrace_58933 : CollatzResearch.WordTrace tailWord_58933 prefixEnd_58933 26898627032465029392425 := by
  unfold tailWord_58933
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149463095503280800197453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1432975397002187200131635 2149463095503280800197453)
  ·
    refine ⟨806048660813730300074045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2149463095503280800197453 806048660813730300074045)
    ·
      refine ⟨302268247805148862527767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 806048660813730300074045 302268247805148862527767)
      ·
        refine ⟨453402371707723293791651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302268247805148862527767 453402371707723293791651)
        ·
          refine ⟨680103557561584940687477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453402371707723293791651 680103557561584940687477)
          ·
            refine ⟨63759708521398588189451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 680103557561584940687477 63759708521398588189451)
            ·
              refine ⟨95639562782097882284177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63759708521398588189451 95639562782097882284177)
              ·
                refine ⟨71729672086573411713133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95639562782097882284177 71729672086573411713133)
                ·
                  refine ⟨26898627032465029392425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71729672086573411713133 26898627032465029392425)
                  ·
                    rfl

theorem cell20_58933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_58933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58933 prefixEnd_58933 := by exact prefixLift 58933
  have htrace : WordTrace (prefixWord ++ tailWord_58933) baseStart_58933 baseEnd_58933 := by
    simpa [prefixWord, tailWord_58933, baseEnd_58933] using wordTrace_append hprefix tailTrace_58933
  have hstable : (prefixWord ++ tailWord_58933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58933).length < 2 ^ (prefixWord ++ tailWord_58933).sum := by decide
  have hdescent : baseEnd_58933 < baseStart_58933 := by decide
  rcases family_descends (prefixWord ++ tailWord_58933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_58940 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 4]
def baseStart_58940 : Nat := 118140960795 + 58940 * 2 ^ 59
def prefixEnd_58940 : Nat := 4983230072969 + 3 ^ 40 * 58940 * 2
def baseEnd_58940 : Nat := 26901822023204116159063

theorem tailTrace_58940 : CollatzResearch.WordTrace tailWord_58940 prefixEnd_58940 26901822023204116159063 := by
  unfold tailWord_58940
  simp only [CollatzResearch.WordTrace]
  refine ⟨1074859203238960497851137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1433145604318613997134849 1074859203238960497851137)
  ·
    refine ⟨806144402429220373388353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1074859203238960497851137 806144402429220373388353)
    ·
      refine ⟨604608301821915280041265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 806144402429220373388353 604608301821915280041265)
      ·
        refine ⟨453456226366436460030949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 604608301821915280041265 453456226366436460030949)
        ·
          refine ⟨85023042443706836255803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 453456226366436460030949 85023042443706836255803)
          ·
            refine ⟨127534563665560254383705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85023042443706836255803 127534563665560254383705)
            ·
              refine ⟨95650922749170190787779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127534563665560254383705 95650922749170190787779)
              ·
                refine ⟨143476384123755286181669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95650922749170190787779 143476384123755286181669)
                ·
                  refine ⟨26901822023204116159063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143476384123755286181669 26901822023204116159063)
                  ·
                    rfl

theorem cell20_58940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_58940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_58940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_58940 prefixEnd_58940 := by exact prefixLift 58940
  have htrace : WordTrace (prefixWord ++ tailWord_58940) baseStart_58940 baseEnd_58940 := by
    simpa [prefixWord, tailWord_58940, baseEnd_58940] using wordTrace_append hprefix tailTrace_58940
  have hstable : (prefixWord ++ tailWord_58940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_58940).length < 2 ^ (prefixWord ++ tailWord_58940).sum := by decide
  have hdescent : baseEnd_58940 < baseStart_58940 := by decide
  rcases family_descends (prefixWord ++ tailWord_58940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59009 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 3]
def baseStart_59009 : Nat := 118140960795 + 59009 * 2 ^ 59
def prefixEnd_59009 : Nat := 4983230072969 + 3 ^ 40 * 59009 * 2
def baseEnd_59009 : Nat := 26933315503346542858781

theorem tailTrace_59009 : CollatzResearch.WordTrace tailWord_59009 prefixEnd_59009 26933315503346542858781 := by
  unfold tailWord_59009
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152235043227945779964081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1434823362151963853309387 2152235043227945779964081)
  ·
    refine ⟨1614176282420959334973061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2152235043227945779964081 1614176282420959334973061)
    ·
      refine ⟨302658052953929875307449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1614176282420959334973061 302658052953929875307449)
      ·
        refine ⟨226993539715447406480587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302658052953929875307449 226993539715447406480587)
        ·
          refine ⟨340490309573171109720881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226993539715447406480587 340490309573171109720881)
          ·
            refine ⟨255367732179878332290661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340490309573171109720881 255367732179878332290661)
            ·
              refine ⟨47881449783727187304499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255367732179878332290661 47881449783727187304499)
              ·
                refine ⟨71822174675590780956749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47881449783727187304499 71822174675590780956749)
                ·
                  refine ⟨26933315503346542858781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71822174675590780956749 26933315503346542858781)
                  ·
                    rfl

theorem cell20_59009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_59009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59009 prefixEnd_59009 := by exact prefixLift 59009
  have htrace : WordTrace (prefixWord ++ tailWord_59009) baseStart_59009 baseEnd_59009 := by
    simpa [prefixWord, tailWord_59009, baseEnd_59009] using wordTrace_append hprefix tailTrace_59009
  have hstable : (prefixWord ++ tailWord_59009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59009).length < 2 ^ (prefixWord ++ tailWord_59009).sum := by decide
  have hdescent : baseEnd_59009 < baseStart_59009 := by decide
  rcases family_descends (prefixWord ++ tailWord_59009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59020 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 6]
def baseStart_59020 : Nat := 118140960795 + 59020 * 2 ^ 59
def prefixEnd_59020 : Nat := 4983230072969 + 3 ^ 40 * 59020 * 2
def baseEnd_59020 : Nat := 26938336203079393492069

theorem tailTrace_59020 : CollatzResearch.WordTrace tailWord_59020 prefixEnd_59020 26938336203079393492069 := by
  unfold tailWord_59020
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076318123094047329307257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1435090830792063105743009 1076318123094047329307257)
  ·
    refine ⟨807238592320535496980443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1076318123094047329307257 807238592320535496980443)
    ·
      refine ⟨1210857888480803245470665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807238592320535496980443 1210857888480803245470665)
      ·
        refine ⟨908143416360602434102999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1210857888480803245470665 908143416360602434102999)
        ·
          refine ⟨1362215124540903651154499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908143416360602434102999 1362215124540903651154499)
          ·
            refine ⟨2043322686811355476731749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1362215124540903651154499 2043322686811355476731749)
            ·
              refine ⟨383123003777129151887203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2043322686811355476731749 383123003777129151887203)
              ·
                refine ⟨574684505665693727830805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383123003777129151887203 574684505665693727830805)
                ·
                  refine ⟨26938336203079393492069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 574684505665693727830805 26938336203079393492069)
                  ·
                    rfl

theorem cell20_59020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_59020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59020 prefixEnd_59020 := by exact prefixLift 59020
  have htrace : WordTrace (prefixWord ++ tailWord_59020) baseStart_59020 baseEnd_59020 := by
    simpa [prefixWord, tailWord_59020, baseEnd_59020] using wordTrace_append hprefix tailTrace_59020
  have hstable : (prefixWord ++ tailWord_59020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59020).length < 2 ^ (prefixWord ++ tailWord_59020).sum := by decide
  have hdescent : baseEnd_59020 < baseStart_59020 := by decide
  rcases family_descends (prefixWord ++ tailWord_59020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59068 : List Nat := [2, 2, 2, 3, 1, 2, 2, 3, 3]
def baseStart_59068 : Nat := 118140960795 + 59068 * 2 ^ 59
def prefixEnd_59068 : Nat := 4983230072969 + 3 ^ 40 * 59068 * 2
def baseEnd_59068 : Nat := 26960244711004559891873

theorem tailTrace_59068 : CollatzResearch.WordTrace tailWord_59068 prefixEnd_59068 26960244711004559891873 := by
  unfold tailWord_59068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1077193475007099428180929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1436257966676132570907905 1077193475007099428180929)
  ·
    refine ⟨807895106255324571135697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1077193475007099428180929 807895106255324571135697)
    ·
      refine ⟨605921329691493428351773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 807895106255324571135697 605921329691493428351773)
      ·
        refine ⟨227220498634310035631915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 605921329691493428351773 227220498634310035631915)
        ·
          refine ⟨340830747951465053447873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227220498634310035631915 340830747951465053447873)
          ·
            refine ⟨255623060963598790085905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340830747951465053447873 255623060963598790085905)
            ·
              refine ⟨191717295722699092564429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255623060963598790085905 191717295722699092564429)
              ·
                refine ⟨71893985896012159711661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191717295722699092564429 71893985896012159711661)
                ·
                  refine ⟨26960244711004559891873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71893985896012159711661 26960244711004559891873)
                  ·
                    rfl

theorem cell20_59068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_59068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59068 prefixEnd_59068 := by exact prefixLift 59068
  have htrace : WordTrace (prefixWord ++ tailWord_59068) baseStart_59068 baseEnd_59068 := by
    simpa [prefixWord, tailWord_59068, baseEnd_59068] using wordTrace_append hprefix tailTrace_59068
  have hstable : (prefixWord ++ tailWord_59068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59068).length < 2 ^ (prefixWord ++ tailWord_59068).sum := by decide
  have hdescent : baseEnd_59068 < baseStart_59068 := by decide
  rcases family_descends (prefixWord ++ tailWord_59068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59074 : List Nat := [3, 5, 1, 2, 1, 1, 3, 4]
def baseStart_59074 : Nat := 118140960795 + 59074 * 2 ^ 59
def prefixEnd_59074 : Nat := 4983230072969 + 3 ^ 40 * 59074 * 2
def baseEnd_59074 : Nat := 8987661091498401897283

theorem tailTrace_59074 : CollatzResearch.WordTrace tailWord_59074 prefixEnd_59074 8987661091498401897283 := by
  unfold tailWord_59074
  simp only [CollatzResearch.WordTrace]
  refine ⟨538651446998115470270069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1436403858661641254053517 538651446998115470270069)
  ·
    refine ⟨50498573156073325337819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 538651446998115470270069 50498573156073325337819)
    ·
      refine ⟨75747859734109988006729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50498573156073325337819 75747859734109988006729)
      ·
        refine ⟨56810894800582491005047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75747859734109988006729 56810894800582491005047)
        ·
          refine ⟨85216342200873736507571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56810894800582491005047 85216342200873736507571)
          ·
            refine ⟨127824513301310604761357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85216342200873736507571 127824513301310604761357)
            ·
              refine ⟨47934192487991476785509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127824513301310604761357 47934192487991476785509)
              ·
                refine ⟨8987661091498401897283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47934192487991476785509 8987661091498401897283)
                ·
                  rfl

theorem cell20_59074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_59074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59074 prefixEnd_59074 := by exact prefixLift 59074
  have htrace : WordTrace (prefixWord ++ tailWord_59074) baseStart_59074 baseEnd_59074 := by
    simpa [prefixWord, tailWord_59074, baseEnd_59074] using wordTrace_append hprefix tailTrace_59074
  have hstable : (prefixWord ++ tailWord_59074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59074).length < 2 ^ (prefixWord ++ tailWord_59074).sum := by decide
  have hdescent : baseEnd_59074 < baseStart_59074 := by decide
  rcases family_descends (prefixWord ++ tailWord_59074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59096 : List Nat := [2, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_59096 : Nat := 118140960795 + 59096 * 2 ^ 59
def prefixEnd_59096 : Nat := 4983230072969 + 3 ^ 40 * 59096 * 2
def baseEnd_59096 : Nat := 26973024673960906958425

theorem tailTrace_59096 : CollatzResearch.WordTrace tailWord_59096 prefixEnd_59096 26973024673960906958425 := by
  unfold tailWord_59096
  simp only [CollatzResearch.WordTrace]
  refine ⟨1077704096956379819190571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1436938795941839758920761 1077704096956379819190571)
  ·
    refine ⟨1616556145434569728785857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1077704096956379819190571 1616556145434569728785857)
    ·
      refine ⟨1212417109075927296589393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1616556145434569728785857 1212417109075927296589393)
      ·
        refine ⟨909312831806945472442045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1212417109075927296589393 909312831806945472442045)
        ·
          refine ⟨340992311927604552165767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 909312831806945472442045 340992311927604552165767)
          ·
            refine ⟨511488467891406828248651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340992311927604552165767 511488467891406828248651)
            ·
              refine ⟨767232701837110242372977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 511488467891406828248651 767232701837110242372977)
              ·
                refine ⟨575424526377832681779733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 767232701837110242372977 575424526377832681779733)
                ·
                  refine ⟨26973024673960906958425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 575424526377832681779733 26973024673960906958425)
                  ·
                    rfl

theorem cell20_59096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_59096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59096 prefixEnd_59096 := by exact prefixLift 59096
  have htrace : WordTrace (prefixWord ++ tailWord_59096) baseStart_59096 baseEnd_59096 := by
    simpa [prefixWord, tailWord_59096, baseEnd_59096] using wordTrace_append hprefix tailTrace_59096
  have hstable : (prefixWord ++ tailWord_59096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59096).length < 2 ^ (prefixWord ++ tailWord_59096).sum := by decide
  have hdescent : baseEnd_59096 < baseStart_59096 := by decide
  rcases family_descends (prefixWord ++ tailWord_59096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59103 : List Nat := [1, 1, 2, 3, 2, 2, 9]
def baseStart_59103 : Nat := 118140960795 + 59103 * 2 ^ 59
def prefixEnd_59103 : Nat := 4983230072969 + 3 ^ 40 * 59103 * 2
def baseEnd_59103 : Nat := 2997357740522221525007

theorem tailTrace_59103 : CollatzResearch.WordTrace tailWord_59103 prefixEnd_59103 2997357740522221525007 := by
  unfold tailWord_59103
  simp only [CollatzResearch.WordTrace]
  refine ⟨2155663504887399833885963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1437109003258266555923975 2155663504887399833885963)
  ·
    refine ⟨3233495257331099750828945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2155663504887399833885963 3233495257331099750828945)
    ·
      refine ⟨2425121442998324813121709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3233495257331099750828945 2425121442998324813121709)
      ·
        refine ⟨909420541124371804920641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2425121442998324813121709 909420541124371804920641)
        ·
          refine ⟨682065405843278853690481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 909420541124371804920641 682065405843278853690481)
          ·
            refine ⟨511549054382459140267861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 682065405843278853690481 511549054382459140267861)
            ·
              refine ⟨2997357740522221525007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 511549054382459140267861 2997357740522221525007)
              ·
                rfl

theorem cell20_59103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 9].length) (baseStart_59103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59103 prefixEnd_59103 := by exact prefixLift 59103
  have htrace : WordTrace (prefixWord ++ tailWord_59103) baseStart_59103 baseEnd_59103 := by
    simpa [prefixWord, tailWord_59103, baseEnd_59103] using wordTrace_append hprefix tailTrace_59103
  have hstable : (prefixWord ++ tailWord_59103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59103).length < 2 ^ (prefixWord ++ tailWord_59103).sum := by decide
  have hdescent : baseEnd_59103 < baseStart_59103 := by decide
  rcases family_descends (prefixWord ++ tailWord_59103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59127 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 3]
def baseStart_59127 : Nat := 118140960795 + 59127 * 2 ^ 59
def prefixEnd_59127 : Nat := 4983230072969 + 3 ^ 40 * 59127 * 2
def baseEnd_59127 : Nat := 26987173918662576924965

theorem tailTrace_59127 : CollatzResearch.WordTrace tailWord_59127 prefixEnd_59127 26987173918662576924965 := by
  unfold tailWord_59127
  simp only [CollatzResearch.WordTrace]
  refine ⟨2156538856800451932759635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1437692571200301288506423 2156538856800451932759635)
  ·
    refine ⟨3234808285200677899139453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2156538856800451932759635 3234808285200677899139453)
    ·
      refine ⟨1213053106950254212177295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3234808285200677899139453 1213053106950254212177295)
      ·
        refine ⟨1819579660425381318265943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1213053106950254212177295 1819579660425381318265943)
        ·
          refine ⟨2729369490638071977398915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1819579660425381318265943 2729369490638071977398915)
          ·
            refine ⟨4094054235957107966098373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2729369490638071977398915 4094054235957107966098373)
            ·
              refine ⟨767635169241957743643445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4094054235957107966098373 767635169241957743643445)
              ·
                refine ⟨71965797116433538466573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 767635169241957743643445 71965797116433538466573)
                ·
                  refine ⟨26987173918662576924965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71965797116433538466573 26987173918662576924965)
                  ·
                    rfl

theorem cell20_59127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 3].length) (baseStart_59127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59127 prefixEnd_59127 := by exact prefixLift 59127
  have htrace : WordTrace (prefixWord ++ tailWord_59127) baseStart_59127 baseEnd_59127 := by
    simpa [prefixWord, tailWord_59127, baseEnd_59127] using wordTrace_append hprefix tailTrace_59127
  have hstable : (prefixWord ++ tailWord_59127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59127).length < 2 ^ (prefixWord ++ tailWord_59127).sum := by decide
  have hdescent : baseEnd_59127 < baseStart_59127 := by decide
  rcases family_descends (prefixWord ++ tailWord_59127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59151 : List Nat := [1, 1, 2, 1, 1, 1, 4, 7, 2]
def baseStart_59151 : Nat := 118140960795 + 59151 * 2 ^ 59
def prefixEnd_59151 : Nat := 4983230072969 + 3 ^ 40 * 59151 * 2
def baseEnd_59151 : Nat := 26998128172625160124867

theorem tailTrace_59151 : CollatzResearch.WordTrace tailWord_59151 prefixEnd_59151 26998128172625160124867 := by
  unfold tailWord_59151
  simp only [CollatzResearch.WordTrace]
  refine ⟨2157414208713504031633307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1438276139142336021088871 2157414208713504031633307)
  ·
    refine ⟨3236121313070256047449961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2157414208713504031633307 3236121313070256047449961)
    ·
      refine ⟨2427090984802692035587471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3236121313070256047449961 2427090984802692035587471)
      ·
        refine ⟨3640636477204038053381207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427090984802692035587471 3640636477204038053381207)
        ·
          refine ⟨5460954715806057080071811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3640636477204038053381207 5460954715806057080071811)
          ·
            refine ⟨8191432073709085620107717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5460954715806057080071811 8191432073709085620107717)
            ·
              refine ⟨1535893513820453553770197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8191432073709085620107717 1535893513820453553770197)
              ·
                refine ⟨35997504230166880166489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1535893513820453553770197 35997504230166880166489)
                ·
                  refine ⟨26998128172625160124867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35997504230166880166489 26998128172625160124867)
                  ·
                    rfl

theorem cell20_59151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 2].length) (baseStart_59151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59151 prefixEnd_59151 := by exact prefixLift 59151
  have htrace : WordTrace (prefixWord ++ tailWord_59151) baseStart_59151 baseEnd_59151 := by
    simpa [prefixWord, tailWord_59151, baseEnd_59151] using wordTrace_append hprefix tailTrace_59151
  have hstable : (prefixWord ++ tailWord_59151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59151).length < 2 ^ (prefixWord ++ tailWord_59151).sum := by decide
  have hdescent : baseEnd_59151 < baseStart_59151 := by decide
  rcases family_descends (prefixWord ++ tailWord_59151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59217 : List Nat := [1, 2, 2, 1, 5, 9]
def baseStart_59217 : Nat := 118140960795 + 59217 * 2 ^ 59
def prefixEnd_59217 : Nat := 4983230072969 + 3 ^ 40 * 59217 * 2
def baseEnd_59217 : Nat := 1001046384111935700911

theorem tailTrace_59217 : CollatzResearch.WordTrace tailWord_59217 prefixEnd_59217 1001046384111935700911 := by
  unfold tailWord_59217
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159821426474397303535905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1439880950982931535690603 2159821426474397303535905)
  ·
    refine ⟨1619866069855797977651929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2159821426474397303535905 1619866069855797977651929)
    ·
      refine ⟨1214899552391848483238947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1619866069855797977651929 1214899552391848483238947)
      ·
        refine ⟨1822349328587772724858421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1214899552391848483238947 1822349328587772724858421)
        ·
          refine ⟨170845249555103692955477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1822349328587772724858421 170845249555103692955477)
          ·
            refine ⟨1001046384111935700911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 170845249555103692955477 1001046384111935700911)
            ·
              rfl

theorem cell20_59217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 9].length) (baseStart_59217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59217 prefixEnd_59217 := by exact prefixLift 59217
  have htrace : WordTrace (prefixWord ++ tailWord_59217) baseStart_59217 baseEnd_59217 := by
    simpa [prefixWord, tailWord_59217, baseEnd_59217] using wordTrace_append hprefix tailTrace_59217
  have hstable : (prefixWord ++ tailWord_59217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59217).length < 2 ^ (prefixWord ++ tailWord_59217).sum := by decide
  have hdescent : baseEnd_59217 < baseStart_59217 := by decide
  rcases family_descends (prefixWord ++ tailWord_59217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59220 : List Nat := [2, 4, 1, 1, 3, 1, 1, 4, 3]
def baseStart_59220 : Nat := 118140960795 + 59220 * 2 ^ 59
def prefixEnd_59220 : Nat := 4983230072969 + 3 ^ 40 * 59220 * 2
def baseEnd_59220 : Nat := 27029621652767586824585

theorem tailTrace_59220 : CollatzResearch.WordTrace tailWord_59220 prefixEnd_59220 27029621652767586824585 := by
  unfold tailWord_59220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1079965422731764407947557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1439953896975685877263409 1079965422731764407947557)
  ·
    refine ⟨202493516762205826490167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1079965422731764407947557 202493516762205826490167)
    ·
      refine ⟨303740275143308739735251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202493516762205826490167 303740275143308739735251)
      ·
        refine ⟨455610412714963109602877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 303740275143308739735251 455610412714963109602877)
        ·
          refine ⟨170853904768111166101079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 455610412714963109602877 170853904768111166101079)
          ·
            refine ⟨256280857152166749151619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170853904768111166101079 256280857152166749151619)
            ·
              refine ⟨384421285728250123727429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256280857152166749151619 384421285728250123727429)
              ·
                refine ⟨72078991074046898198893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 384421285728250123727429 72078991074046898198893)
                ·
                  refine ⟨27029621652767586824585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72078991074046898198893 27029621652767586824585)
                  ·
                    rfl

theorem cell20_59220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_59220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59220 prefixEnd_59220 := by exact prefixLift 59220
  have htrace : WordTrace (prefixWord ++ tailWord_59220) baseStart_59220 baseEnd_59220 := by
    simpa [prefixWord, tailWord_59220, baseEnd_59220] using wordTrace_append hprefix tailTrace_59220
  have hstable : (prefixWord ++ tailWord_59220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59220).length < 2 ^ (prefixWord ++ tailWord_59220).sum := by decide
  have hdescent : baseEnd_59220 < baseStart_59220 := by decide
  rcases family_descends (prefixWord ++ tailWord_59220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59272 : List Nat := [2, 1, 3, 3, 3, 1, 7]
def baseStart_59272 : Nat := 118140960795 + 59272 * 2 ^ 59
def prefixEnd_59272 : Nat := 4983230072969 + 3 ^ 40 * 59272 * 2
def baseEnd_59272 : Nat := 3005928429965168565671

theorem tailTrace_59272 : CollatzResearch.WordTrace tailWord_59272 prefixEnd_59272 3005928429965168565671 := by
  unfold tailWord_59272
  simp only [CollatzResearch.WordTrace]
  refine ⟨1080913720637570848394035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1441218294183427797858713 1080913720637570848394035)
  ·
    refine ⟨1621370580956356272591053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1080913720637570848394035 1621370580956356272591053)
    ·
      refine ⟨608013967858633602221645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1621370580956356272591053 608013967858633602221645)
      ·
        refine ⟨228005237946987600833117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 608013967858633602221645 228005237946987600833117)
        ·
          refine ⟨85501964230120350312419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228005237946987600833117 85501964230120350312419)
          ·
            refine ⟨128252946345180525468629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85501964230120350312419 128252946345180525468629)
            ·
              refine ⟨3005928429965168565671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 128252946345180525468629 3005928429965168565671)
              ·
                rfl

theorem cell20_59272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 7].length) (baseStart_59272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59272 prefixEnd_59272 := by exact prefixLift 59272
  have htrace : WordTrace (prefixWord ++ tailWord_59272) baseStart_59272 baseEnd_59272 := by
    simpa [prefixWord, tailWord_59272, baseEnd_59272] using wordTrace_append hprefix tailTrace_59272
  have hstable : (prefixWord ++ tailWord_59272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59272).length < 2 ^ (prefixWord ++ tailWord_59272).sum := by decide
  have hdescent : baseEnd_59272 < baseStart_59272 := by decide
  rcases family_descends (prefixWord ++ tailWord_59272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59282 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_59282 : Nat := 118140960795 + 59282 * 2 ^ 59
def prefixEnd_59282 : Nat := 4983230072969 + 3 ^ 40 * 59282 * 2
def baseEnd_59282 : Nat := 27057920142170926757665

theorem tailTrace_59282 : CollatzResearch.WordTrace tailWord_59282 prefixEnd_59282 27057920142170926757665 := by
  unfold tailWord_59282
  simp only [CollatzResearch.WordTrace]
  refine ⟨540548042809728351163025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1441461447492608936434733 540548042809728351163025)
  ·
    refine ⟨405411032107296263372269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 540548042809728351163025 405411032107296263372269)
    ·
      refine ⟨152029137040236098764601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405411032107296263372269 152029137040236098764601)
      ·
        refine ⟨114021852780177074073451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152029137040236098764601 114021852780177074073451)
        ·
          refine ⟨171032779170265611110177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114021852780177074073451 171032779170265611110177)
          ·
            refine ⟨128274584377699208332633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171032779170265611110177 128274584377699208332633)
            ·
              refine ⟨96205938283274406249475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128274584377699208332633 96205938283274406249475)
              ·
                refine ⟨144308907424911609374213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96205938283274406249475 144308907424911609374213)
                ·
                  refine ⟨27057920142170926757665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144308907424911609374213 27057920142170926757665)
                  ·
                    rfl

theorem cell20_59282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_59282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59282 prefixEnd_59282 := by exact prefixLift 59282
  have htrace : WordTrace (prefixWord ++ tailWord_59282) baseStart_59282 baseEnd_59282 := by
    simpa [prefixWord, tailWord_59282, baseEnd_59282] using wordTrace_append hprefix tailTrace_59282
  have hstable : (prefixWord ++ tailWord_59282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59282).length < 2 ^ (prefixWord ++ tailWord_59282).sum := by decide
  have hdescent : baseEnd_59282 < baseStart_59282 := by decide
  rcases family_descends (prefixWord ++ tailWord_59282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59303 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 4]
def baseStart_59303 : Nat := 118140960795 + 59303 * 2 ^ 59
def prefixEnd_59303 : Nat := 4983230072969 + 3 ^ 40 * 59303 * 2
def baseEnd_59303 : Nat := 27067505114388187057579

theorem tailTrace_59303 : CollatzResearch.WordTrace tailWord_59303 prefixEnd_59303 27067505114388187057579 := by
  unfold tailWord_59303
  simp only [CollatzResearch.WordTrace]
  refine ⟨2162958104162833991166563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1441972069441889327444375 2162958104162833991166563)
  ·
    refine ⟨3244437156244250986749845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2162958104162833991166563 3244437156244250986749845)
    ·
      refine ⟨152082991698949265003899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3244437156244250986749845 152082991698949265003899)
      ·
        refine ⟨228124487548423897505849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152082991698949265003899 228124487548423897505849)
        ·
          refine ⟨171093365661317923129387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228124487548423897505849 171093365661317923129387)
          ·
            refine ⟨256640048491976884694081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171093365661317923129387 256640048491976884694081)
            ·
              refine ⟨192480036368982663520561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256640048491976884694081 192480036368982663520561)
              ·
                refine ⟨144360027276736997640421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192480036368982663520561 144360027276736997640421)
                ·
                  refine ⟨27067505114388187057579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144360027276736997640421 27067505114388187057579)
                  ·
                    rfl

theorem cell20_59303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_59303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59303 prefixEnd_59303 := by exact prefixLift 59303
  have htrace : WordTrace (prefixWord ++ tailWord_59303) baseStart_59303 baseEnd_59303 := by
    simpa [prefixWord, tailWord_59303, baseEnd_59303] using wordTrace_append hprefix tailTrace_59303
  have hstable : (prefixWord ++ tailWord_59303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59303).length < 2 ^ (prefixWord ++ tailWord_59303).sum := by decide
  have hdescent : baseEnd_59303 < baseStart_59303 := by decide
  rcases family_descends (prefixWord ++ tailWord_59303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59317 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 5]
def baseStart_59317 : Nat := 118140960795 + 59317 * 2 ^ 59
def prefixEnd_59317 : Nat := 4983230072969 + 3 ^ 40 * 59317 * 2
def baseEnd_59317 : Nat := 27073895095866360590855

theorem tailTrace_59317 : CollatzResearch.WordTrace tailWord_59317 prefixEnd_59317 27073895095866360590855 := by
  unfold tailWord_59317
  simp only [CollatzResearch.WordTrace]
  refine ⟨2163468726112114382176205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1442312484074742921450803 2163468726112114382176205)
  ·
    refine ⟨811300772292042893316077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2163468726112114382176205 811300772292042893316077)
    ·
      refine ⟨304237789609516084993529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 811300772292042893316077 304237789609516084993529)
      ·
        refine ⟨228178342207137063745147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304237789609516084993529 228178342207137063745147)
        ·
          refine ⟨342267513310705595617721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228178342207137063745147 342267513310705595617721)
          ·
            refine ⟨256700634983029196713291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342267513310705595617721 256700634983029196713291)
            ·
              refine ⟨385050952474543795069937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256700634983029196713291 385050952474543795069937)
              ·
                refine ⟨288788214355907846302453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385050952474543795069937 288788214355907846302453)
                ·
                  refine ⟨27073895095866360590855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 288788214355907846302453 27073895095866360590855)
                  ·
                    rfl

theorem cell20_59317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_59317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59317 prefixEnd_59317 := by exact prefixLift 59317
  have htrace : WordTrace (prefixWord ++ tailWord_59317) baseStart_59317 baseEnd_59317 := by
    simpa [prefixWord, tailWord_59317, baseEnd_59317] using wordTrace_append hprefix tailTrace_59317
  have hstable : (prefixWord ++ tailWord_59317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59317).length < 2 ^ (prefixWord ++ tailWord_59317).sum := by decide
  have hdescent : baseEnd_59317 < baseStart_59317 := by decide
  rcases family_descends (prefixWord ++ tailWord_59317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59348 : List Nat := [2, 4, 1, 2, 1, 1, 4, 5]
def baseStart_59348 : Nat := 118140960795 + 59348 * 2 ^ 59
def prefixEnd_59348 : Nat := 4983230072969 + 3 ^ 40 * 59348 * 2
def baseEnd_59348 : Nat := 9029348113522676852465

theorem tailTrace_59348 : CollatzResearch.WordTrace tailWord_59348 prefixEnd_59348 9029348113522676852465 := by
  unfold tailWord_59348
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082299694499903338277349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1443066259333204451036465 1082299694499903338277349)
  ·
    refine ⟨202931192718731875927003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1082299694499903338277349 202931192718731875927003)
    ·
      refine ⟨304396789078097813890505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 202931192718731875927003 304396789078097813890505)
      ·
        refine ⟨228297591808573360417879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304396789078097813890505 228297591808573360417879)
        ·
          refine ⟨342446387712860040626819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228297591808573360417879 342446387712860040626819)
          ·
            refine ⟨513669581569290060940229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342446387712860040626819 513669581569290060940229)
            ·
              refine ⟨96313046544241886426293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 513669581569290060940229 96313046544241886426293)
              ·
                refine ⟨9029348113522676852465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96313046544241886426293 9029348113522676852465)
                ·
                  rfl

theorem cell20_59348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_59348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59348 prefixEnd_59348 := by exact prefixLift 59348
  have htrace : WordTrace (prefixWord ++ tailWord_59348) baseStart_59348 baseEnd_59348 := by
    simpa [prefixWord, tailWord_59348, baseEnd_59348] using wordTrace_append hprefix tailTrace_59348
  have hstable : (prefixWord ++ tailWord_59348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59348).length < 2 ^ (prefixWord ++ tailWord_59348).sum := by decide
  have hdescent : baseEnd_59348 < baseStart_59348 := by decide
  rcases family_descends (prefixWord ++ tailWord_59348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59376 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_59376 : Nat := 118140960795 + 59376 * 2 ^ 59
def prefixEnd_59376 : Nat := 4983230072969 + 3 ^ 40 * 59376 * 2
def baseEnd_59376 : Nat := 27100824303524377623947

theorem tailTrace_59376 : CollatzResearch.WordTrace tailWord_59376 prefixEnd_59376 27100824303524377623947 := by
  unfold tailWord_59376
  simp only [CollatzResearch.WordTrace]
  refine ⟨1082810316449183729286991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1443747088598911639049321 1082810316449183729286991)
  ·
    refine ⟨1624215474673775593930487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1082810316449183729286991 1624215474673775593930487)
    ·
      refine ⟨2436323212010663390895731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1624215474673775593930487 2436323212010663390895731)
      ·
        refine ⟨3654484818015995086343597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2436323212010663390895731 3654484818015995086343597)
        ·
          refine ⟨1370431806755998157378849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3654484818015995086343597 1370431806755998157378849)
          ·
            refine ⟨1027823855066998618034137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1370431806755998157378849 1027823855066998618034137)
            ·
              refine ⟨770867891300248963525603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1027823855066998618034137 770867891300248963525603)
              ·
                refine ⟨1156301836950373445288405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 770867891300248963525603 1156301836950373445288405)
                ·
                  refine ⟨27100824303524377623947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1156301836950373445288405 27100824303524377623947)
                  ·
                    rfl

theorem cell20_59376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_59376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59376 prefixEnd_59376 := by exact prefixLift 59376
  have htrace : WordTrace (prefixWord ++ tailWord_59376) baseStart_59376 baseEnd_59376 := by
    simpa [prefixWord, tailWord_59376, baseEnd_59376] using wordTrace_append hprefix tailTrace_59376
  have hstable : (prefixWord ++ tailWord_59376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59376).length < 2 ^ (prefixWord ++ tailWord_59376).sum := by decide
  have hdescent : baseEnd_59376 < baseStart_59376 := by decide
  rcases family_descends (prefixWord ++ tailWord_59376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59400 : List Nat := [2, 1, 3, 2, 1, 2, 2, 3, 4]
def baseStart_59400 : Nat := 118140960795 + 59400 * 2 ^ 59
def prefixEnd_59400 : Nat := 4983230072969 + 3 ^ 40 * 59400 * 2
def baseEnd_59400 : Nat := 27111778557486960823849

theorem tailTrace_59400 : CollatzResearch.WordTrace tailWord_59400 prefixEnd_59400 27111778557486960823849 := by
  unfold tailWord_59400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1083247992405709778723827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1444330656540946371631769 1083247992405709778723827)
  ·
    refine ⟨1624871988608564668085741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1083247992405709778723827 1624871988608564668085741)
    ·
      refine ⟨609326995728211750532153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1624871988608564668085741 609326995728211750532153)
      ·
        refine ⟨456995246796158812899115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609326995728211750532153 456995246796158812899115)
        ·
          refine ⟨685492870194238219348673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456995246796158812899115 685492870194238219348673)
          ·
            refine ⟨514119652645678664511505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 685492870194238219348673 514119652645678664511505)
            ·
              refine ⟨385589739484258998383629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514119652645678664511505 385589739484258998383629)
              ·
                refine ⟨144596152306597124393861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385589739484258998383629 144596152306597124393861)
                ·
                  refine ⟨27111778557486960823849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144596152306597124393861 27111778557486960823849)
                  ·
                    rfl

theorem cell20_59400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_59400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59400 prefixEnd_59400 := by exact prefixLift 59400
  have htrace : WordTrace (prefixWord ++ tailWord_59400) baseStart_59400 baseEnd_59400 := by
    simpa [prefixWord, tailWord_59400, baseEnd_59400] using wordTrace_append hprefix tailTrace_59400
  have hstable : (prefixWord ++ tailWord_59400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59400).length < 2 ^ (prefixWord ++ tailWord_59400).sum := by decide
  have hdescent : baseEnd_59400 < baseStart_59400 := by decide
  rcases family_descends (prefixWord ++ tailWord_59400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59434 : List Nat := [3, 1, 4, 1, 2, 1, 1, 5, 2]
def baseStart_59434 : Nat := 118140960795 + 59434 * 2 ^ 59
def prefixEnd_59434 : Nat := 4983230072969 + 3 ^ 40 * 59434 * 2
def baseEnd_59434 : Nat := 27127297083933953690377

theorem tailTrace_59434 : CollatzResearch.WordTrace tailWord_59434 prefixEnd_59434 27127297083933953690377 := by
  unfold tailWord_59434
  simp only [CollatzResearch.WordTrace]
  refine ⟨541934016672060841046339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1445157377792162242790237 541934016672060841046339)
  ·
    refine ⟨812901025008091261569509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 541934016672060841046339 812901025008091261569509)
    ·
      refine ⟨152418942189017111544283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 812901025008091261569509 152418942189017111544283)
      ·
        refine ⟨228628413283525667316425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152418942189017111544283 228628413283525667316425)
        ·
          refine ⟨171471309962644250487319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228628413283525667316425 171471309962644250487319)
          ·
            refine ⟨257206964943966375730979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171471309962644250487319 257206964943966375730979)
            ·
              refine ⟨385810447415949563596469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257206964943966375730979 385810447415949563596469)
              ·
                refine ⟨36169729445245271587169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 385810447415949563596469 36169729445245271587169)
                ·
                  refine ⟨27127297083933953690377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36169729445245271587169 27127297083933953690377)
                  ·
                    rfl

theorem cell20_59434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_59434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59434 prefixEnd_59434 := by exact prefixLift 59434
  have htrace : WordTrace (prefixWord ++ tailWord_59434) baseStart_59434 baseEnd_59434 := by
    simpa [prefixWord, tailWord_59434, baseEnd_59434] using wordTrace_append hprefix tailTrace_59434
  have hstable : (prefixWord ++ tailWord_59434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59434).length < 2 ^ (prefixWord ++ tailWord_59434).sum := by decide
  have hdescent : baseEnd_59434 < baseStart_59434 := by decide
  rcases family_descends (prefixWord ++ tailWord_59434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59444 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 3]
def baseStart_59444 : Nat := 118140960795 + 59444 * 2 ^ 59
def prefixEnd_59444 : Nat := 4983230072969 + 3 ^ 40 * 59444 * 2
def baseEnd_59444 : Nat := 27131861356418363357003

theorem tailTrace_59444 : CollatzResearch.WordTrace tailWord_59444 prefixEnd_59444 27131861356418363357003 := by
  unfold tailWord_59444
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084050398326007536024693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1445400531101343381366257 1084050398326007536024693)
  ·
    refine ⟨101629724843063206502315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1084050398326007536024693 101629724843063206502315)
    ·
      refine ⟨152444587264594809753473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101629724843063206502315 152444587264594809753473)
      ·
        refine ⟨114333440448446107315105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152444587264594809753473 114333440448446107315105)
        ·
          refine ⟨85750080336334580486329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114333440448446107315105 85750080336334580486329)
          ·
            refine ⟨64312560252250935364747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85750080336334580486329 64312560252250935364747)
            ·
              refine ⟨96468840378376403047121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64312560252250935364747 96468840378376403047121)
              ·
                refine ⟨72351630283782302285341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96468840378376403047121 72351630283782302285341)
                ·
                  refine ⟨27131861356418363357003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72351630283782302285341 27131861356418363357003)
                  ·
                    rfl

theorem cell20_59444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_59444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59444 prefixEnd_59444 := by exact prefixLift 59444
  have htrace : WordTrace (prefixWord ++ tailWord_59444) baseStart_59444 baseEnd_59444 := by
    simpa [prefixWord, tailWord_59444, baseEnd_59444] using wordTrace_append hprefix tailTrace_59444
  have hstable : (prefixWord ++ tailWord_59444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59444).length < 2 ^ (prefixWord ++ tailWord_59444).sum := by decide
  have hdescent : baseEnd_59444 < baseStart_59444 := by decide
  rcases family_descends (prefixWord ++ tailWord_59444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59455 : List Nat := [1, 1, 2, 2, 3, 1, 4, 4, 2]
def baseStart_59455 : Nat := 118140960795 + 59455 * 2 ^ 59
def prefixEnd_59455 : Nat := 4983230072969 + 3 ^ 40 * 59455 * 2
def baseEnd_59455 : Nat := 27136882056151213990291

theorem tailTrace_59455 : CollatzResearch.WordTrace tailWord_59455 prefixEnd_59455 27136882056151213990291 := by
  unfold tailWord_59455
  simp only [CollatzResearch.WordTrace]
  refine ⟨2168501999612163950699819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1445667999741442633799879 2168501999612163950699819)
  ·
    refine ⟨3252752999418245926049729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2168501999612163950699819 3252752999418245926049729)
    ·
      refine ⟨2439564749563684444537297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3252752999418245926049729 2439564749563684444537297)
      ·
        refine ⟨1829673562172763333402973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2439564749563684444537297 1829673562172763333402973)
        ·
          refine ⟨686127585814786250026115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1829673562172763333402973 686127585814786250026115)
          ·
            refine ⟨1029191378722179375039173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686127585814786250026115 1029191378722179375039173)
            ·
              refine ⟨192973383510408632819845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1029191378722179375039173 192973383510408632819845)
              ·
                refine ⟨36182509408201618653721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192973383510408632819845 36182509408201618653721)
                ·
                  refine ⟨27136882056151213990291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36182509408201618653721 27136882056151213990291)
                  ·
                    rfl

theorem cell20_59455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 2].length) (baseStart_59455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59455 prefixEnd_59455 := by exact prefixLift 59455
  have htrace : WordTrace (prefixWord ++ tailWord_59455) baseStart_59455 baseEnd_59455 := by
    simpa [prefixWord, tailWord_59455, baseEnd_59455] using wordTrace_append hprefix tailTrace_59455
  have hstable : (prefixWord ++ tailWord_59455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59455).length < 2 ^ (prefixWord ++ tailWord_59455).sum := by decide
  have hdescent : baseEnd_59455 < baseStart_59455 := by decide
  rcases family_descends (prefixWord ++ tailWord_59455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59510 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_59510 : Nat := 118140960795 + 59510 * 2 ^ 59
def prefixEnd_59510 : Nat := 4983230072969 + 3 ^ 40 * 59510 * 2
def baseEnd_59510 : Nat := 27161985554815467156733

theorem tailTrace_59510 : CollatzResearch.WordTrace tailWord_59510 prefixEnd_59510 27161985554815467156733 := by
  unfold tailWord_59510
  simp only [CollatzResearch.WordTrace]
  refine ⟨135656750900806771496999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1447005342941938895967989 135656750900806771496999)
  ·
    refine ⟨203485126351210157245499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135656750900806771496999 203485126351210157245499)
    ·
      refine ⟨305227689526815235868249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203485126351210157245499 305227689526815235868249)
      ·
        refine ⟨228920767145111426901187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305227689526815235868249 228920767145111426901187)
        ·
          refine ⟨343381150717667140351781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228920767145111426901187 343381150717667140351781)
          ·
            refine ⟨64383965759562588815959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 343381150717667140351781 64383965759562588815959)
            ·
              refine ⟨96575948639343883223939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64383965759562588815959 96575948639343883223939)
              ·
                refine ⟨144863922959015824835909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96575948639343883223939 144863922959015824835909)
                ·
                  refine ⟨27161985554815467156733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144863922959015824835909 27161985554815467156733)
                  ·
                    rfl

theorem cell20_59510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_59510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59510 prefixEnd_59510 := by exact prefixLift 59510
  have htrace : WordTrace (prefixWord ++ tailWord_59510) baseStart_59510 baseEnd_59510 := by
    simpa [prefixWord, tailWord_59510, baseEnd_59510] using wordTrace_append hprefix tailTrace_59510
  have hstable : (prefixWord ++ tailWord_59510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59510).length < 2 ^ (prefixWord ++ tailWord_59510).sum := by decide
  have hdescent : baseEnd_59510 < baseStart_59510 := by decide
  rcases family_descends (prefixWord ++ tailWord_59510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59559 : List Nat := [1, 1, 6, 2, 10]
def baseStart_59559 : Nat := 118140960795 + 59559 * 2 ^ 59
def prefixEnd_59559 : Nat := 4983230072969 + 3 ^ 40 * 59559 * 2
def baseEnd_59559 : Nat := 335609265308507092879

theorem tailTrace_59559 : CollatzResearch.WordTrace tailWord_59559 prefixEnd_59559 335609265308507092879 := by
  unfold tailWord_59559
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172295191235389712485731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1448196794156926474990487 2172295191235389712485731)
  ·
    refine ⟨3258442786853084568728597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2172295191235389712485731 3258442786853084568728597)
    ·
      refine ⟨152739505633738339159153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3258442786853084568728597 152739505633738339159153)
      ·
        refine ⟨114554629225303754369365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152739505633738339159153 114554629225303754369365)
        ·
          refine ⟨335609265308507092879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 114554629225303754369365 335609265308507092879)
          ·
            rfl

theorem cell20_59559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 10].length) (baseStart_59559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59559 prefixEnd_59559 := by exact prefixLift 59559
  have htrace : WordTrace (prefixWord ++ tailWord_59559) baseStart_59559 baseEnd_59559 := by
    simpa [prefixWord, tailWord_59559, baseEnd_59559] using wordTrace_append hprefix tailTrace_59559
  have hstable : (prefixWord ++ tailWord_59559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59559).length < 2 ^ (prefixWord ++ tailWord_59559).sum := by decide
  have hdescent : baseEnd_59559 < baseStart_59559 := by decide
  rcases family_descends (prefixWord ++ tailWord_59559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59565 : List Nat := [1, 5, 2, 1, 2, 1, 4, 2, 2]
def baseStart_59565 : Nat := 118140960795 + 59565 * 2 ^ 59
def prefixEnd_59565 : Nat := 4983230072969 + 3 ^ 40 * 59565 * 2
def baseEnd_59565 : Nat := 27187089053479720323175

theorem tailTrace_59565 : CollatzResearch.WordTrace tailWord_59565 prefixEnd_59565 27187089053479720323175 := by
  unfold tailWord_59565
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172514029213652737204149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1448342686142435158136099 2172514029213652737204149)
  ·
    refine ⟨203673190238779944112889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2172514029213652737204149 203673190238779944112889)
    ·
      refine ⟨152754892679084958084667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203673190238779944112889 152754892679084958084667)
      ·
        refine ⟨229132339018627437127001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152754892679084958084667 229132339018627437127001)
        ·
          refine ⟨171849254263970577845251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229132339018627437127001 171849254263970577845251)
          ·
            refine ⟨257773881395955866767877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171849254263970577845251 257773881395955866767877)
            ·
              refine ⟨48332602761741725018977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 257773881395955866767877 48332602761741725018977)
              ·
                refine ⟨36249452071306293764233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48332602761741725018977 36249452071306293764233)
                ·
                  refine ⟨27187089053479720323175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36249452071306293764233 27187089053479720323175)
                  ·
                    rfl

theorem cell20_59565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_59565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59565 prefixEnd_59565 := by exact prefixLift 59565
  have htrace : WordTrace (prefixWord ++ tailWord_59565) baseStart_59565 baseEnd_59565 := by
    simpa [prefixWord, tailWord_59565, baseEnd_59565] using wordTrace_append hprefix tailTrace_59565
  have hstable : (prefixWord ++ tailWord_59565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59565).length < 2 ^ (prefixWord ++ tailWord_59565).sum := by decide
  have hdescent : baseEnd_59565 < baseStart_59565 := by decide
  rcases family_descends (prefixWord ++ tailWord_59565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59586 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 6]
def baseStart_59586 : Nat := 118140960795 + 59586 * 2 ^ 59
def prefixEnd_59586 : Nat := 4983230072969 + 3 ^ 40 * 59586 * 2
def baseEnd_59586 : Nat := 27196674025696980623089

theorem tailTrace_59586 : CollatzResearch.WordTrace tailWord_59586 prefixEnd_59586 27196674025696980623089 := by
  unfold tailWord_59586
  simp only [CollatzResearch.WordTrace]
  refine ⟨543319990534393330929653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1448853308091715549145741 543319990534393330929653)
  ·
    refine ⟨50936249112599374774655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 543319990534393330929653 50936249112599374774655)
    ·
      refine ⟨76404373668899062161983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50936249112599374774655 76404373668899062161983)
      ·
        refine ⟨114606560503348593242975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76404373668899062161983 114606560503348593242975)
        ·
          refine ⟨171909840755022889864463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114606560503348593242975 171909840755022889864463)
          ·
            refine ⟨257864761132534334796695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171909840755022889864463 257864761132534334796695)
            ·
              refine ⟨386797141698801502195043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257864761132534334796695 386797141698801502195043)
              ·
                refine ⟨580195712548202253292565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386797141698801502195043 580195712548202253292565)
                ·
                  refine ⟨27196674025696980623089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 580195712548202253292565 27196674025696980623089)
                  ·
                    rfl

theorem cell20_59586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_59586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59586 prefixEnd_59586 := by exact prefixLift 59586
  have htrace : WordTrace (prefixWord ++ tailWord_59586) baseStart_59586 baseEnd_59586 := by
    simpa [prefixWord, tailWord_59586, baseEnd_59586] using wordTrace_append hprefix tailTrace_59586
  have hstable : (prefixWord ++ tailWord_59586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59586).length < 2 ^ (prefixWord ++ tailWord_59586).sum := by decide
  have hdescent : baseEnd_59586 < baseStart_59586 := by decide
  rcases family_descends (prefixWord ++ tailWord_59586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59621 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 5]
def baseStart_59621 : Nat := 118140960795 + 59621 * 2 ^ 59
def prefixEnd_59621 : Nat := 4983230072969 + 3 ^ 40 * 59621 * 2
def baseEnd_59621 : Nat := 27212648979392414456279

theorem tailTrace_59621 : CollatzResearch.WordTrace tailWord_59621 prefixEnd_59621 27212648979392414456279 := by
  unfold tailWord_59621
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174556517010774301242717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1449704344673849534161811 2174556517010774301242717)
  ·
    refine ⟨815458693879040362966019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2174556517010774301242717 815458693879040362966019)
    ·
      refine ⟨1223188040818560544449029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815458693879040362966019 1223188040818560544449029)
      ·
        refine ⟨229347757653480102084193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1223188040818560544449029 229347757653480102084193)
        ·
          refine ⟨172010818240110076563145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229347757653480102084193 172010818240110076563145)
          ·
            refine ⟨129008113680082557422359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172010818240110076563145 129008113680082557422359)
            ·
              refine ⟨193512170520123836133539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129008113680082557422359 193512170520123836133539)
              ·
                refine ⟨290268255780185754200309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193512170520123836133539 290268255780185754200309)
                ·
                  refine ⟨27212648979392414456279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290268255780185754200309 27212648979392414456279)
                  ·
                    rfl

theorem cell20_59621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_59621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59621 prefixEnd_59621 := by exact prefixLift 59621
  have htrace : WordTrace (prefixWord ++ tailWord_59621) baseStart_59621 baseEnd_59621 := by
    simpa [prefixWord, tailWord_59621, baseEnd_59621] using wordTrace_append hprefix tailTrace_59621
  have hstable : (prefixWord ++ tailWord_59621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59621).length < 2 ^ (prefixWord ++ tailWord_59621).sum := by decide
  have hdescent : baseEnd_59621 < baseStart_59621 := by decide
  rcases family_descends (prefixWord ++ tailWord_59621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59628 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_59628 : Nat := 118140960795 + 59628 * 2 ^ 59
def prefixEnd_59628 : Nat := 4983230072969 + 3 ^ 40 * 59628 * 2
def baseEnd_59628 : Nat := 27215843970131501222917

theorem tailTrace_59628 : CollatzResearch.WordTrace tailWord_59628 prefixEnd_59628 27215843970131501222917 := by
  unfold tailWord_59628
  simp only [CollatzResearch.WordTrace]
  refine ⟨1087405913992707248373769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1449874551990276331165025 1087405913992707248373769)
  ·
    refine ⟨815554435494530436280327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1087405913992707248373769 815554435494530436280327)
    ·
      refine ⟨1223331653241795654420491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815554435494530436280327 1223331653241795654420491)
      ·
        refine ⟨1834997479862693481630737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1223331653241795654420491 1834997479862693481630737)
        ·
          refine ⟨1376248109897020111223053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1834997479862693481630737 1376248109897020111223053)
          ·
            refine ⟨516093041211382541708645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1376248109897020111223053 516093041211382541708645)
            ·
              refine ⟨96767445227134226570371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 516093041211382541708645 96767445227134226570371)
              ·
                refine ⟨145151167840701339855557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96767445227134226570371 145151167840701339855557)
                ·
                  refine ⟨27215843970131501222917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145151167840701339855557 27215843970131501222917)
                  ·
                    rfl

theorem cell20_59628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_59628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59628 prefixEnd_59628 := by exact prefixLift 59628
  have htrace : WordTrace (prefixWord ++ tailWord_59628) baseStart_59628 baseEnd_59628 := by
    simpa [prefixWord, tailWord_59628, baseEnd_59628] using wordTrace_append hprefix tailTrace_59628
  have hstable : (prefixWord ++ tailWord_59628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59628).length < 2 ^ (prefixWord ++ tailWord_59628).sum := by decide
  have hdescent : baseEnd_59628 < baseStart_59628 := by decide
  rcases family_descends (prefixWord ++ tailWord_59628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59652 : List Nat := [2, 3, 2, 2, 3, 1, 1, 6]
def baseStart_59652 : Nat := 118140960795 + 59652 * 2 ^ 59
def prefixEnd_59652 : Nat := 4983230072969 + 3 ^ 40 * 59652 * 2
def baseEnd_59652 : Nat := 9075599408031361474273

theorem tailTrace_59652 : CollatzResearch.WordTrace tailWord_59652 prefixEnd_59652 9075599408031361474273 := by
  unfold tailWord_59652
  simp only [CollatzResearch.WordTrace]
  refine ⟨1087843589949233297810605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1450458119932311063747473 1087843589949233297810605)
  ·
    refine ⟨407941346230962486678977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1087843589949233297810605 407941346230962486678977)
    ·
      refine ⟨305956009673221865009233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407941346230962486678977 305956009673221865009233)
      ·
        refine ⟨229467007254916398756925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 305956009673221865009233 229467007254916398756925)
        ·
          refine ⟨86050127720593649533847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 229467007254916398756925 86050127720593649533847)
          ·
            refine ⟨129075191580890474300771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86050127720593649533847 129075191580890474300771)
            ·
              refine ⟨193612787371335711451157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129075191580890474300771 193612787371335711451157)
              ·
                refine ⟨9075599408031361474273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 193612787371335711451157 9075599408031361474273)
                ·
                  rfl

theorem cell20_59652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_59652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59652 prefixEnd_59652 := by exact prefixLift 59652
  have htrace : WordTrace (prefixWord ++ tailWord_59652) baseStart_59652 baseEnd_59652 := by
    simpa [prefixWord, tailWord_59652, baseEnd_59652] using wordTrace_append hprefix tailTrace_59652
  have hstable : (prefixWord ++ tailWord_59652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59652).length < 2 ^ (prefixWord ++ tailWord_59652).sum := by decide
  have hdescent : baseEnd_59652 < baseStart_59652 := by decide
  rcases family_descends (prefixWord ++ tailWord_59652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59693 : List Nat := [1, 5, 3, 1, 2, 1, 1, 3, 3]
def baseStart_59693 : Nat := 118140960795 + 59693 * 2 ^ 59
def prefixEnd_59693 : Nat := 4983230072969 + 3 ^ 40 * 59693 * 2
def baseEnd_59693 : Nat := 27245511741280164055985

theorem tailTrace_59693 : CollatzResearch.WordTrace tailWord_59693 prefixEnd_59693 27245511741280164055985 := by
  unfold tailWord_59693
  simp only [CollatzResearch.WordTrace]
  refine ⟨2177182572749930597863733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1451455048499953731909155 2177182572749930597863733)
  ·
    refine ⟨204110866195305993549725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2177182572749930597863733 204110866195305993549725)
    ·
      refine ⟨76541574823239747581147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204110866195305993549725 76541574823239747581147)
      ·
        refine ⟨114812362234859621371721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76541574823239747581147 114812362234859621371721)
        ·
          refine ⟨86109271676144716028791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114812362234859621371721 86109271676144716028791)
          ·
            refine ⟨129163907514217074043187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86109271676144716028791 129163907514217074043187)
            ·
              refine ⟨193745861271325611064781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129163907514217074043187 193745861271325611064781)
              ·
                refine ⟨72654697976747104149293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193745861271325611064781 72654697976747104149293)
                ·
                  refine ⟨27245511741280164055985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72654697976747104149293 27245511741280164055985)
                  ·
                    rfl

theorem cell20_59693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_59693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59693 prefixEnd_59693 := by exact prefixLift 59693
  have htrace : WordTrace (prefixWord ++ tailWord_59693) baseStart_59693 baseEnd_59693 := by
    simpa [prefixWord, tailWord_59693, baseEnd_59693] using wordTrace_append hprefix tailTrace_59693
  have hstable : (prefixWord ++ tailWord_59693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59693).length < 2 ^ (prefixWord ++ tailWord_59693).sum := by decide
  have hdescent : baseEnd_59693 < baseStart_59693 := by decide
  rcases family_descends (prefixWord ++ tailWord_59693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59735 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 3]
def baseStart_59735 : Nat := 118140960795 + 59735 * 2 ^ 59
def prefixEnd_59735 : Nat := 4983230072969 + 3 ^ 40 * 59735 * 2
def baseEnd_59735 : Nat := 27264681685714684655813

theorem tailTrace_59735 : CollatzResearch.WordTrace tailWord_59735 prefixEnd_59735 27264681685714684655813 := by
  unfold tailWord_59735
  simp only [CollatzResearch.WordTrace]
  refine ⟨2178714438597771770892659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1452476292398514513928439 2178714438597771770892659)
  ·
    refine ⟨3268071657896657656338989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2178714438597771770892659 3268071657896657656338989)
    ·
      refine ⟨1225526871711246621127121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3268071657896657656338989 1225526871711246621127121)
      ·
        refine ⟨919145153783434965845341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1225526871711246621127121 919145153783434965845341)
        ·
          refine ⟨344679432668788112192003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 919145153783434965845341 344679432668788112192003)
          ·
            refine ⟨517019149003182168288005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344679432668788112192003 517019149003182168288005)
            ·
              refine ⟨96941090438096656554001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 517019149003182168288005 96941090438096656554001)
              ·
                refine ⟨72705817828572492415501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96941090438096656554001 72705817828572492415501)
                ·
                  refine ⟨27264681685714684655813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72705817828572492415501 27264681685714684655813)
                  ·
                    rfl

theorem cell20_59735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 3].length) (baseStart_59735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59735 prefixEnd_59735 := by exact prefixLift 59735
  have htrace : WordTrace (prefixWord ++ tailWord_59735) baseStart_59735 baseEnd_59735 := by
    simpa [prefixWord, tailWord_59735, baseEnd_59735] using wordTrace_append hprefix tailTrace_59735
  have hstable : (prefixWord ++ tailWord_59735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59735).length < 2 ^ (prefixWord ++ tailWord_59735).sum := by decide
  have hdescent : baseEnd_59735 < baseStart_59735 := by decide
  rcases family_descends (prefixWord ++ tailWord_59735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59749 : List Nat := [1, 3, 1, 3, 1, 3, 3, 5]
def baseStart_59749 : Nat := 118140960795 + 59749 * 2 ^ 59
def prefixEnd_59749 : Nat := 4983230072969 + 3 ^ 40 * 59749 * 2
def baseEnd_59749 : Nat := 9090357222397619396363

theorem tailTrace_59749 : CollatzResearch.WordTrace tailWord_59749 prefixEnd_59749 9090357222397619396363 := by
  unfold tailWord_59749
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179225060547052161902301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1452816707031368107934867 2179225060547052161902301)
  ·
    refine ⟨817209397705144560713363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2179225060547052161902301 817209397705144560713363)
    ·
      refine ⟨1225814096557716841070045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 817209397705144560713363 1225814096557716841070045)
      ·
        refine ⟨459680286209143815401267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1225814096557716841070045 459680286209143815401267)
        ·
          refine ⟨689520429313715723101901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459680286209143815401267 689520429313715723101901)
          ·
            refine ⟨258570160992643396163213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 689520429313715723101901 258570160992643396163213)
            ·
              refine ⟨96963810372241273561205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258570160992643396163213 96963810372241273561205)
              ·
                refine ⟨9090357222397619396363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96963810372241273561205 9090357222397619396363)
                ·
                  rfl

theorem cell20_59749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 5].length) (baseStart_59749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59749 prefixEnd_59749 := by exact prefixLift 59749
  have htrace : WordTrace (prefixWord ++ tailWord_59749) baseStart_59749 baseEnd_59749 := by
    simpa [prefixWord, tailWord_59749, baseEnd_59749] using wordTrace_append hprefix tailTrace_59749
  have hstable : (prefixWord ++ tailWord_59749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59749).length < 2 ^ (prefixWord ++ tailWord_59749).sum := by decide
  have hdescent : baseEnd_59749 < baseStart_59749 := by decide
  rcases family_descends (prefixWord ++ tailWord_59749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59763 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 4]
def baseStart_59763 : Nat := 118140960795 + 59763 * 2 ^ 59
def prefixEnd_59763 : Nat := 4983230072969 + 3 ^ 40 * 59763 * 2
def baseEnd_59763 : Nat := 27277461648671031722365

theorem tailTrace_59763 : CollatzResearch.WordTrace tailWord_59763 prefixEnd_59763 27277461648671031722365 := by
  unfold tailWord_59763
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179735682496332552911943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1453157121664221701941295 2179735682496332552911943)
  ·
    refine ⟨3269603523744498829367915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2179735682496332552911943 3269603523744498829367915)
    ·
      refine ⟨4904405285616748244051873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3269603523744498829367915 4904405285616748244051873)
      ·
        refine ⟨3678303964212561183038905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4904405285616748244051873 3678303964212561183038905)
        ·
          refine ⟨2758727973159420887279179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3678303964212561183038905 2758727973159420887279179)
          ·
            refine ⟨4138091959739131330918769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758727973159420887279179 4138091959739131330918769)
            ·
              refine ⟨3103568969804348498189077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4138091959739131330918769 3103568969804348498189077)
              ·
                refine ⟨145479795459578835852613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3103568969804348498189077 145479795459578835852613)
                ·
                  refine ⟨27277461648671031722365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145479795459578835852613 27277461648671031722365)
                  ·
                    rfl

theorem cell20_59763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_59763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59763 prefixEnd_59763 := by exact prefixLift 59763
  have htrace : WordTrace (prefixWord ++ tailWord_59763) baseStart_59763 baseEnd_59763 := by
    simpa [prefixWord, tailWord_59763, baseEnd_59763] using wordTrace_append hprefix tailTrace_59763
  have hstable : (prefixWord ++ tailWord_59763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59763).length < 2 ^ (prefixWord ++ tailWord_59763).sum := by decide
  have hdescent : baseEnd_59763 < baseStart_59763 := by decide
  rcases family_descends (prefixWord ++ tailWord_59763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59786 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 3]
def baseStart_59786 : Nat := 118140960795 + 59786 * 2 ^ 59
def prefixEnd_59786 : Nat := 4983230072969 + 3 ^ 40 * 59786 * 2
def baseEnd_59786 : Nat := 27287959475385173955605

theorem tailTrace_59786 : CollatzResearch.WordTrace tailWord_59786 prefixEnd_59786 27287959475385173955605 := by
  unfold tailWord_59786
  simp only [CollatzResearch.WordTrace]
  refine ⟨545143640353251870249803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1453716374275338320666141 545143640353251870249803)
  ·
    refine ⟨817715460529877805374705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 545143640353251870249803 817715460529877805374705)
    ·
      refine ⟨613286595397408354031029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 817715460529877805374705 613286595397408354031029)
      ·
        refine ⟨57495618318507033190409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 613286595397408354031029 57495618318507033190409)
        ·
          refine ⟨43121713738880274892807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57495618318507033190409 43121713738880274892807)
          ·
            refine ⟨64682570608320412339211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43121713738880274892807 64682570608320412339211)
            ·
              refine ⟨97023855912480618508817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64682570608320412339211 97023855912480618508817)
              ·
                refine ⟨72767891934360463881613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97023855912480618508817 72767891934360463881613)
                ·
                  refine ⟨27287959475385173955605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72767891934360463881613 27287959475385173955605)
                  ·
                    rfl

theorem cell20_59786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_59786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59786 prefixEnd_59786 := by exact prefixLift 59786
  have htrace : WordTrace (prefixWord ++ tailWord_59786) baseStart_59786 baseEnd_59786 := by
    simpa [prefixWord, tailWord_59786, baseEnd_59786] using wordTrace_append hprefix tailTrace_59786
  have hstable : (prefixWord ++ tailWord_59786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59786).length < 2 ^ (prefixWord ++ tailWord_59786).sum := by decide
  have hdescent : baseEnd_59786 < baseStart_59786 := by decide
  rcases family_descends (prefixWord ++ tailWord_59786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59790 : List Nat := [4, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_59790 : Nat := 118140960795 + 59790 * 2 ^ 59
def prefixEnd_59790 : Nat := 4983230072969 + 3 ^ 40 * 59790 * 2
def baseEnd_59790 : Nat := 27289785184378937822255

theorem tailTrace_59790 : CollatzResearch.WordTrace tailWord_59790 prefixEnd_59790 27289785184378937822255 := by
  unfold tailWord_59790
  simp only [CollatzResearch.WordTrace]
  refine ⟨272590056674814520518103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1453813635599010776096549 272590056674814520518103)
  ·
    refine ⟨408885085012221780777155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 272590056674814520518103 408885085012221780777155)
    ·
      refine ⟨613327627518332671165733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 408885085012221780777155 613327627518332671165733)
      ·
        refine ⟨114998930159687375843575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 613327627518332671165733 114998930159687375843575)
        ·
          refine ⟨172498395239531063765363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114998930159687375843575 172498395239531063765363)
          ·
            refine ⟨258747592859296595648045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172498395239531063765363 258747592859296595648045)
            ·
              refine ⟨97030347322236223368017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258747592859296595648045 97030347322236223368017)
              ·
                refine ⟨72772760491677167526013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97030347322236223368017 72772760491677167526013)
                ·
                  refine ⟨27289785184378937822255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72772760491677167526013 27289785184378937822255)
                  ·
                    rfl

theorem cell20_59790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_59790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59790 prefixEnd_59790 := by exact prefixLift 59790
  have htrace : WordTrace (prefixWord ++ tailWord_59790) baseStart_59790 baseEnd_59790 := by
    simpa [prefixWord, tailWord_59790, baseEnd_59790] using wordTrace_append hprefix tailTrace_59790
  have hstable : (prefixWord ++ tailWord_59790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59790).length < 2 ^ (prefixWord ++ tailWord_59790).sum := by decide
  have hdescent : baseEnd_59790 < baseStart_59790 := by decide
  rcases family_descends (prefixWord ++ tailWord_59790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59825 : List Nat := [1, 2, 2, 4, 1, 3, 1, 6]
def baseStart_59825 : Nat := 118140960795 + 59825 * 2 ^ 59
def prefixEnd_59825 : Nat := 4983230072969 + 3 ^ 40 * 59825 * 2
def baseEnd_59825 : Nat := 9101920046024790551815

theorem tailTrace_59825 : CollatzResearch.WordTrace tailWord_59825 prefixEnd_59825 9101920046024790551815 := by
  unfold tailWord_59825
  simp only [CollatzResearch.WordTrace]
  refine ⟨2181997008271717141668929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1454664672181144761112619 2181997008271717141668929)
  ·
    refine ⟨1636497756203787856251697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2181997008271717141668929 1636497756203787856251697)
    ·
      refine ⟨1227373317152840892188773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1636497756203787856251697 1227373317152840892188773)
      ·
        refine ⟨230132496966157667285395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1227373317152840892188773 230132496966157667285395)
        ·
          refine ⟨345198745449236500928093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230132496966157667285395 345198745449236500928093)
          ·
            refine ⟨129449529543463687848035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345198745449236500928093 129449529543463687848035)
            ·
              refine ⟨194174294315195531772053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129449529543463687848035 194174294315195531772053)
              ·
                refine ⟨9101920046024790551815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194174294315195531772053 9101920046024790551815)
                ·
                  rfl

theorem cell20_59825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 6].length) (baseStart_59825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59825 prefixEnd_59825 := by exact prefixLift 59825
  have htrace : WordTrace (prefixWord ++ tailWord_59825) baseStart_59825 baseEnd_59825 := by
    simpa [prefixWord, tailWord_59825, baseEnd_59825] using wordTrace_append hprefix tailTrace_59825
  have hstable : (prefixWord ++ tailWord_59825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59825).length < 2 ^ (prefixWord ++ tailWord_59825).sum := by decide
  have hdescent : baseEnd_59825 < baseStart_59825 := by decide
  rcases family_descends (prefixWord ++ tailWord_59825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59852 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 4]
def baseStart_59852 : Nat := 118140960795 + 59852 * 2 ^ 59
def prefixEnd_59852 : Nat := 4983230072969 + 3 ^ 40 * 59852 * 2
def baseEnd_59852 : Nat := 27318083673782277755335

theorem tailTrace_59852 : CollatzResearch.WordTrace tailWord_59852 prefixEnd_59852 27318083673782277755335 := by
  unfold tailWord_59852
  simp only [CollatzResearch.WordTrace]
  refine ⟨1091490889586950376450905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1455321186115933835267873 1091490889586950376450905)
  ·
    refine ⟨818618167190212782338179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1091490889586950376450905 818618167190212782338179)
    ·
      refine ⟨1227927250785319173507269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 818618167190212782338179 1227927250785319173507269)
      ·
        refine ⟨230236359522247345032613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1227927250785319173507269 230236359522247345032613)
        ·
          refine ⟨43169317410421377193615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230236359522247345032613 43169317410421377193615)
          ·
            refine ⟨64753976115632065790423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43169317410421377193615 64753976115632065790423)
            ·
              refine ⟨97130964173448098685635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64753976115632065790423 97130964173448098685635)
              ·
                refine ⟨145696446260172148028453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97130964173448098685635 145696446260172148028453)
                ·
                  refine ⟨27318083673782277755335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145696446260172148028453 27318083673782277755335)
                  ·
                    rfl

theorem cell20_59852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_59852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59852 prefixEnd_59852 := by exact prefixLift 59852
  have htrace : WordTrace (prefixWord ++ tailWord_59852) baseStart_59852 baseEnd_59852 := by
    simpa [prefixWord, tailWord_59852, baseEnd_59852] using wordTrace_append hprefix tailTrace_59852
  have hstable : (prefixWord ++ tailWord_59852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59852).length < 2 ^ (prefixWord ++ tailWord_59852).sum := by decide
  have hdescent : baseEnd_59852 < baseStart_59852 := by decide
  rcases family_descends (prefixWord ++ tailWord_59852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59884 : List Nat := [2, 2, 1, 1, 2, 1, 3, 8]
def baseStart_59884 : Nat := 118140960795 + 59884 * 2 ^ 59
def prefixEnd_59884 : Nat := 4983230072969 + 3 ^ 40 * 59884 * 2
def baseEnd_59884 : Nat := 9110896448577462896179

theorem tailTrace_59884 : CollatzResearch.WordTrace tailWord_59884 prefixEnd_59884 9110896448577462896179 := by
  unfold tailWord_59884
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092074457528985109033353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1456099276705313478711137 1092074457528985109033353)
  ·
    refine ⟨819055843146738831775015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1092074457528985109033353 819055843146738831775015)
    ·
      refine ⟨1228583764720108247662523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819055843146738831775015 1228583764720108247662523)
      ·
        refine ⟨1842875647080162371493785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1228583764720108247662523 1842875647080162371493785)
        ·
          refine ⟨1382156735310121778620339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1842875647080162371493785 1382156735310121778620339)
          ·
            refine ⟨2073235102965182667930509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382156735310121778620339 2073235102965182667930509)
            ·
              refine ⟨777463163611943500473941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2073235102965182667930509 777463163611943500473941)
              ·
                refine ⟨9110896448577462896179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 777463163611943500473941 9110896448577462896179)
                ·
                  rfl

theorem cell20_59884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_59884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59884 prefixEnd_59884 := by exact prefixLift 59884
  have htrace : WordTrace (prefixWord ++ tailWord_59884) baseStart_59884 baseEnd_59884 := by
    simpa [prefixWord, tailWord_59884, baseEnd_59884] using wordTrace_append hprefix tailTrace_59884
  have hstable : (prefixWord ++ tailWord_59884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59884).length < 2 ^ (prefixWord ++ tailWord_59884).sum := by decide
  have hdescent : baseEnd_59884 < baseStart_59884 := by decide
  rcases family_descends (prefixWord ++ tailWord_59884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59918 : List Nat := [4, 1, 1, 2, 3, 3, 1, 5]
def baseStart_59918 : Nat := 118140960795 + 59918 * 2 ^ 59
def prefixEnd_59918 : Nat := 4983230072969 + 3 ^ 40 * 59918 * 2
def baseEnd_59918 : Nat := 9116069290726460518355

theorem tailTrace_59918 : CollatzResearch.WordTrace tailWord_59918 prefixEnd_59918 9116069290726460518355 := by
  unfold tailWord_59918
  simp only [CollatzResearch.WordTrace]
  refine ⟨273173624616849253100551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1456925997956529349869605 273173624616849253100551)
  ·
    refine ⟨409760436925273879650827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 273173624616849253100551 409760436925273879650827)
    ·
      refine ⟨614640655387910819476241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 409760436925273879650827 614640655387910819476241)
      ·
        refine ⟨460980491540933114607181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 614640655387910819476241 460980491540933114607181)
        ·
          refine ⟨172867684327849917977693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460980491540933114607181 172867684327849917977693)
          ·
            refine ⟨64825381622943719241635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172867684327849917977693 64825381622943719241635)
            ·
              refine ⟨97238072434415578862453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64825381622943719241635 97238072434415578862453)
              ·
                refine ⟨9116069290726460518355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97238072434415578862453 9116069290726460518355)
                ·
                  rfl

theorem cell20_59918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_59918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59918 prefixEnd_59918 := by exact prefixLift 59918
  have htrace : WordTrace (prefixWord ++ tailWord_59918) baseStart_59918 baseEnd_59918 := by
    simpa [prefixWord, tailWord_59918, baseEnd_59918] using wordTrace_append hprefix tailTrace_59918
  have hstable : (prefixWord ++ tailWord_59918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59918).length < 2 ^ (prefixWord ++ tailWord_59918).sum := by decide
  have hdescent : baseEnd_59918 < baseStart_59918 := by decide
  rcases family_descends (prefixWord ++ tailWord_59918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59932 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_59932 : Nat := 118140960795 + 59932 * 2 ^ 59
def prefixEnd_59932 : Nat := 4983230072969 + 3 ^ 40 * 59932 * 2
def baseEnd_59932 : Nat := 27354597853657555088341

theorem tailTrace_59932 : CollatzResearch.WordTrace tailWord_59932 prefixEnd_59932 27354597853657555088341 := by
  unfold tailWord_59932
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092949809442037207907025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1457266412589382943876033 1092949809442037207907025)
  ·
    refine ⟨819712357081527905930269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1092949809442037207907025 819712357081527905930269)
    ·
      refine ⟨307392133905572964723851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 819712357081527905930269 307392133905572964723851)
      ·
        refine ⟨461088200858359447085777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307392133905572964723851 461088200858359447085777)
        ·
          refine ⟨345816150643769585314333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461088200858359447085777 345816150643769585314333)
          ·
            refine ⟨129681056491413594492875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345816150643769585314333 129681056491413594492875)
            ·
              refine ⟨194521584737120391739313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129681056491413594492875 194521584737120391739313)
              ·
                refine ⟨145891188552840293804485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194521584737120391739313 145891188552840293804485)
                ·
                  refine ⟨27354597853657555088341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145891188552840293804485 27354597853657555088341)
                  ·
                    rfl

theorem cell20_59932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_59932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59932 prefixEnd_59932 := by exact prefixLift 59932
  have htrace : WordTrace (prefixWord ++ tailWord_59932) baseStart_59932 baseEnd_59932 := by
    simpa [prefixWord, tailWord_59932, baseEnd_59932] using wordTrace_append hprefix tailTrace_59932
  have hstable : (prefixWord ++ tailWord_59932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59932).length < 2 ^ (prefixWord ++ tailWord_59932).sum := by decide
  have hdescent : baseEnd_59932 < baseStart_59932 := by decide
  rcases family_descends (prefixWord ++ tailWord_59932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59960 : List Nat := [2, 1, 2, 1, 4, 1, 9]
def baseStart_59960 : Nat := 118140960795 + 59960 * 2 ^ 59
def prefixEnd_59960 : Nat := 4983230072969 + 3 ^ 40 * 59960 * 2
def baseEnd_59960 : Nat := 3040819757401544683877

theorem tailTrace_59960 : CollatzResearch.WordTrace tailWord_59960 prefixEnd_59960 3040819757401544683877 := by
  unfold tailWord_59960
  simp only [CollatzResearch.WordTrace]
  refine ⟨1093460431391317598916667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1457947241855090131888889 1093460431391317598916667)
  ·
    refine ⟨1640190647086976398375001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1093460431391317598916667 1640190647086976398375001)
    ·
      refine ⟨1230142985315232298781251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1640190647086976398375001 1230142985315232298781251)
      ·
        refine ⟨1845214477972848448171877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1230142985315232298781251 1845214477972848448171877)
        ·
          refine ⟨345977714619909084032227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1845214477972848448171877 345977714619909084032227)
          ·
            refine ⟨518966571929863626048341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345977714619909084032227 518966571929863626048341)
            ·
              refine ⟨3040819757401544683877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 518966571929863626048341 3040819757401544683877)
              ·
                rfl

theorem cell20_59960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 9].length) (baseStart_59960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59960 prefixEnd_59960 := by exact prefixLift 59960
  have htrace : WordTrace (prefixWord ++ tailWord_59960) baseStart_59960 baseEnd_59960 := by
    simpa [prefixWord, tailWord_59960, baseEnd_59960] using wordTrace_append hprefix tailTrace_59960
  have hstable : (prefixWord ++ tailWord_59960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59960).length < 2 ^ (prefixWord ++ tailWord_59960).sum := by decide
  have hdescent : baseEnd_59960 < baseStart_59960 := by decide
  rcases family_descends (prefixWord ++ tailWord_59960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59966 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_59966 : Nat := 118140960795 + 59966 * 2 ^ 59
def prefixEnd_59966 : Nat := 4983230072969 + 3 ^ 40 * 59966 * 2
def baseEnd_59966 : Nat := 27370116380104547954869

theorem tailTrace_59966 : CollatzResearch.WordTrace tailWord_59966 prefixEnd_59966 27370116380104547954869 := by
  unfold tailWord_59966
  simp only [CollatzResearch.WordTrace]
  refine ⟨273392462595112277818969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1458093133840598815034501 273392462595112277818969)
  ·
    refine ⟨205044346946334208364227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 273392462595112277818969 205044346946334208364227)
    ·
      refine ⟨307566520419501312546341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205044346946334208364227 307566520419501312546341)
      ·
        refine ⟨57668722578656496102439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307566520419501312546341 57668722578656496102439)
        ·
          refine ⟨86503083867984744153659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57668722578656496102439 86503083867984744153659)
          ·
            refine ⟨129754625801977116230489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86503083867984744153659 129754625801977116230489)
            ·
              refine ⟨97315969351482837172867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129754625801977116230489 97315969351482837172867)
              ·
                refine ⟨145973954027224255759301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97315969351482837172867 145973954027224255759301)
                ·
                  refine ⟨27370116380104547954869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145973954027224255759301 27370116380104547954869)
                  ·
                    rfl

theorem cell20_59966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_59966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59966 prefixEnd_59966 := by exact prefixLift 59966
  have htrace : WordTrace (prefixWord ++ tailWord_59966) baseStart_59966 baseEnd_59966 := by
    simpa [prefixWord, tailWord_59966, baseEnd_59966] using wordTrace_append hprefix tailTrace_59966
  have hstable : (prefixWord ++ tailWord_59966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59966).length < 2 ^ (prefixWord ++ tailWord_59966).sum := by decide
  have hdescent : baseEnd_59966 < baseStart_59966 := by decide
  rcases family_descends (prefixWord ++ tailWord_59966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_59991 : List Nat := [1, 1, 3, 2, 2, 2, 1, 4, 4]
def baseStart_59991 : Nat := 118140960795 + 59991 * 2 ^ 59
def prefixEnd_59991 : Nat := 4983230072969 + 3 ^ 40 * 59991 * 2
def baseEnd_59991 : Nat := 27381527061315572121433

theorem tailTrace_59991 : CollatzResearch.WordTrace tailWord_59991 prefixEnd_59991 27381527061315572121433 := by
  unfold tailWord_59991
  simp only [CollatzResearch.WordTrace]
  refine ⟨2188051525670327492211827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1458701017113551661474551 2188051525670327492211827)
  ·
    refine ⟨3282077288505491238317741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2188051525670327492211827 3282077288505491238317741)
    ·
      refine ⟨1230778983189559214369153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3282077288505491238317741 1230778983189559214369153)
      ·
        refine ⟨923084237392169410776865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1230778983189559214369153 923084237392169410776865)
        ·
          refine ⟨692313178044127058082649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 923084237392169410776865 692313178044127058082649)
          ·
            refine ⟨519234883533095293561987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 692313178044127058082649 519234883533095293561987)
            ·
              refine ⟨778852325299642940342981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519234883533095293561987 778852325299642940342981)
              ·
                refine ⟨146034810993683051314309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778852325299642940342981 146034810993683051314309)
                ·
                  refine ⟨27381527061315572121433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146034810993683051314309 27381527061315572121433)
                  ·
                    rfl

theorem cell20_59991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_59991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_59991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_59991 prefixEnd_59991 := by exact prefixLift 59991
  have htrace : WordTrace (prefixWord ++ tailWord_59991) baseStart_59991 baseEnd_59991 := by
    simpa [prefixWord, tailWord_59991, baseEnd_59991] using wordTrace_append hprefix tailTrace_59991
  have hstable : (prefixWord ++ tailWord_59991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_59991).length < 2 ^ (prefixWord ++ tailWord_59991).sum := by decide
  have hdescent : baseEnd_59991 < baseStart_59991 := by decide
  rcases family_descends (prefixWord ++ tailWord_59991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60021 : List Nat := [1, 3, 4, 2, 2, 1, 3, 2, 2]
def baseStart_60021 : Nat := 118140960795 + 60021 * 2 ^ 59
def prefixEnd_60021 : Nat := 4983230072969 + 3 ^ 40 * 60021 * 2
def baseEnd_60021 : Nat := 27395219878768801121311

theorem tailTrace_60021 : CollatzResearch.WordTrace tailWord_60021 prefixEnd_60021 27395219878768801121311 := by
  unfold tailWord_60021
  simp only [CollatzResearch.WordTrace]
  refine ⟨2189145715561642615803917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1459430477041095077202611 2189145715561642615803917)
  ·
    refine ⟨820929643335615980926469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2189145715561642615803917 820929643335615980926469)
    ·
      refine ⟨153924308125427996423713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 820929643335615980926469 153924308125427996423713)
      ·
        refine ⟨115443231094070997317785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153924308125427996423713 115443231094070997317785)
        ·
          refine ⟨86582423320553247988339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115443231094070997317785 86582423320553247988339)
          ·
            refine ⟨129873634980829871982509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86582423320553247988339 129873634980829871982509)
            ·
              refine ⟨48702613117811201993441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129873634980829871982509 48702613117811201993441)
              ·
                refine ⟨36526959838358401495081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48702613117811201993441 36526959838358401495081)
                ·
                  refine ⟨27395219878768801121311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36526959838358401495081 27395219878768801121311)
                  ·
                    rfl

theorem cell20_60021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_60021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60021 prefixEnd_60021 := by exact prefixLift 60021
  have htrace : WordTrace (prefixWord ++ tailWord_60021) baseStart_60021 baseEnd_60021 := by
    simpa [prefixWord, tailWord_60021, baseEnd_60021] using wordTrace_append hprefix tailTrace_60021
  have hstable : (prefixWord ++ tailWord_60021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60021).length < 2 ^ (prefixWord ++ tailWord_60021).sum := by decide
  have hdescent : baseEnd_60021 < baseStart_60021 := by decide
  rcases family_descends (prefixWord ++ tailWord_60021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60043 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_60043 : Nat := 118140960795 + 60043 * 2 ^ 59
def prefixEnd_60043 : Nat := 4983230072969 + 3 ^ 40 * 60043 * 2
def baseEnd_60043 : Nat := 27405261278234502387887

theorem tailTrace_60043 : CollatzResearch.WordTrace tailWord_60043 prefixEnd_60043 27405261278234502387887 := by
  unfold tailWord_60043
  simp only [CollatzResearch.WordTrace]
  refine ⟨2189948121481940373104783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1459965414321293582069855 2189948121481940373104783)
  ·
    refine ⟨3284922182222910559657175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2189948121481940373104783 3284922182222910559657175)
    ·
      refine ⟨4927383273334365839485763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284922182222910559657175 4927383273334365839485763)
      ·
        refine ⟨7391074910001548759228645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927383273334365839485763 7391074910001548759228645)
        ·
          refine ⟨1385826545625290392355371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7391074910001548759228645 1385826545625290392355371)
          ·
            refine ⟨2078739818437935588533057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1385826545625290392355371 2078739818437935588533057)
            ·
              refine ⟨1559054863828451691399793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2078739818437935588533057 1559054863828451691399793)
              ·
                refine ⟨1169291147871338768549845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1559054863828451691399793 1169291147871338768549845)
                ·
                  refine ⟨27405261278234502387887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1169291147871338768549845 27405261278234502387887)
                  ·
                    rfl

theorem cell20_60043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_60043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60043 prefixEnd_60043 := by exact prefixLift 60043
  have htrace : WordTrace (prefixWord ++ tailWord_60043) baseStart_60043 baseEnd_60043 := by
    simpa [prefixWord, tailWord_60043, baseEnd_60043] using wordTrace_append hprefix tailTrace_60043
  have hstable : (prefixWord ++ tailWord_60043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60043).length < 2 ^ (prefixWord ++ tailWord_60043).sum := by decide
  have hdescent : baseEnd_60043 < baseStart_60043 := by decide
  rcases family_descends (prefixWord ++ tailWord_60043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60077 : List Nat := [1, 5, 2, 1, 1, 2, 1, 4, 3]
def baseStart_60077 : Nat := 118140960795 + 60077 * 2 ^ 59
def prefixEnd_60077 : Nat := 4983230072969 + 3 ^ 40 * 60077 * 2
def baseEnd_60077 : Nat := 27420779804681495254415

theorem tailTrace_60077 : CollatzResearch.WordTrace tailWord_60077 prefixEnd_60077 27420779804681495254415 := by
  unfold tailWord_60077
  simp only [CollatzResearch.WordTrace]
  refine ⟨2191188203358764179842485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1460792135572509453228323 2191188203358764179842485)
  ·
    refine ⟨205423894064884141860233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2191188203358764179842485 205423894064884141860233)
    ·
      refine ⟨154067920548663106395175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205423894064884141860233 154067920548663106395175)
      ·
        refine ⟨231101880822994659592763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154067920548663106395175 231101880822994659592763)
        ·
          refine ⟨346652821234491989389145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231101880822994659592763 346652821234491989389145)
          ·
            refine ⟨259989615925868992041859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346652821234491989389145 259989615925868992041859)
            ·
              refine ⟨389984423888803488062789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259989615925868992041859 389984423888803488062789)
              ·
                refine ⟨73122079479150654011773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 389984423888803488062789 73122079479150654011773)
                ·
                  refine ⟨27420779804681495254415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73122079479150654011773 27420779804681495254415)
                  ·
                    rfl

theorem cell20_60077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_60077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60077 prefixEnd_60077 := by exact prefixLift 60077
  have htrace : WordTrace (prefixWord ++ tailWord_60077) baseStart_60077 baseEnd_60077 := by
    simpa [prefixWord, tailWord_60077, baseEnd_60077] using wordTrace_append hprefix tailTrace_60077
  have hstable : (prefixWord ++ tailWord_60077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60077).length < 2 ^ (prefixWord ++ tailWord_60077).sum := by decide
  have hdescent : baseEnd_60077 < baseStart_60077 := by decide
  rcases family_descends (prefixWord ++ tailWord_60077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60108 : List Nat := [2, 2, 1, 5, 1, 2, 3, 4]
def baseStart_60108 : Nat := 118140960795 + 60108 * 2 ^ 59
def prefixEnd_60108 : Nat := 4983230072969 + 3 ^ 40 * 60108 * 2
def baseEnd_60108 : Nat := 9144976349794388406985

theorem tailTrace_60108 : CollatzResearch.WordTrace tailWord_60108 prefixEnd_60108 9144976349794388406985 := by
  unfold tailWord_60108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1096159433123228237110489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1461545910830970982813985 1096159433123228237110489)
  ·
    refine ⟨822119574842421177832867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1096159433123228237110489 822119574842421177832867)
    ·
      refine ⟨1233179362263631766749301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 822119574842421177832867 1233179362263631766749301)
      ·
        refine ⟨115610565212215478132747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1233179362263631766749301 115610565212215478132747)
        ·
          refine ⟨173415847818323217199121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115610565212215478132747 173415847818323217199121)
          ·
            refine ⟨130061885863742412899341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173415847818323217199121 130061885863742412899341)
            ·
              refine ⟨48773207198903404837253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130061885863742412899341 48773207198903404837253)
              ·
                refine ⟨9144976349794388406985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48773207198903404837253 9144976349794388406985)
                ·
                  rfl

theorem cell20_60108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_60108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60108 prefixEnd_60108 := by exact prefixLift 60108
  have htrace : WordTrace (prefixWord ++ tailWord_60108) baseStart_60108 baseEnd_60108 := by
    simpa [prefixWord, tailWord_60108, baseEnd_60108] using wordTrace_append hprefix tailTrace_60108
  have hstable : (prefixWord ++ tailWord_60108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60108).length < 2 ^ (prefixWord ++ tailWord_60108).sum := by decide
  have hdescent : baseEnd_60108 < baseStart_60108 := by decide
  rcases family_descends (prefixWord ++ tailWord_60108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60143 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 4]
def baseStart_60143 : Nat := 118140960795 + 60143 * 2 ^ 59
def prefixEnd_60143 : Nat := 4983230072969 + 3 ^ 40 * 60143 * 2
def baseEnd_60143 : Nat := 27450904003078599054145

theorem tailTrace_60143 : CollatzResearch.WordTrace tailWord_60143 prefixEnd_60143 27450904003078599054145 := by
  unfold tailWord_60143
  simp only [CollatzResearch.WordTrace]
  refine ⟨2193595421119657451745083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1462396947413104967830055 2193595421119657451745083)
  ·
    refine ⟨3290393131679486177617625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2193595421119657451745083 3290393131679486177617625)
    ·
      refine ⟨2467794848759614633213219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3290393131679486177617625 2467794848759614633213219)
      ·
        refine ⟨3701692273139421949819829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2467794848759614633213219 3701692273139421949819829)
        ·
          refine ⟨347033650606820807795609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3701692273139421949819829 347033650606820807795609)
          ·
            refine ⟨260275237955115605846707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347033650606820807795609 260275237955115605846707)
            ·
              refine ⟨390412856932673408770061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260275237955115605846707 390412856932673408770061)
              ·
                refine ⟨146404821349752528288773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 390412856932673408770061 146404821349752528288773)
                ·
                  refine ⟨27450904003078599054145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146404821349752528288773 27450904003078599054145)
                  ·
                    rfl

theorem cell20_60143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_60143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60143 prefixEnd_60143 := by exact prefixLift 60143
  have htrace : WordTrace (prefixWord ++ tailWord_60143) baseStart_60143 baseEnd_60143 := by
    simpa [prefixWord, tailWord_60143, baseEnd_60143] using wordTrace_append hprefix tailTrace_60143
  have hstable : (prefixWord ++ tailWord_60143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60143).length < 2 ^ (prefixWord ++ tailWord_60143).sum := by decide
  have hdescent : baseEnd_60143 < baseStart_60143 := by decide
  rcases family_descends (prefixWord ++ tailWord_60143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60167 : List Nat := [1, 1, 4, 4, 1, 2, 1, 6]
def baseStart_60167 : Nat := 118140960795 + 60167 * 2 ^ 59
def prefixEnd_60167 : Nat := 4983230072969 + 3 ^ 40 * 60167 * 2
def baseEnd_60167 : Nat := 9153952752347060751349

theorem tailTrace_60167 : CollatzResearch.WordTrace tailWord_60167 prefixEnd_60167 9153952752347060751349 := by
  unfold tailWord_60167
  simp only [CollatzResearch.WordTrace]
  refine ⟨2194470773032709550618755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1462980515355139700412503 2194470773032709550618755)
  ·
    refine ⟨3291706159549064325928133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2194470773032709550618755 3291706159549064325928133)
    ·
      refine ⟨617194904915449561111525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3291706159549064325928133 617194904915449561111525)
      ·
        refine ⟨115724044671646792708411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 617194904915449561111525 115724044671646792708411)
        ·
          refine ⟨173586067007470189062617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115724044671646792708411 173586067007470189062617)
          ·
            refine ⟨130189550255602641796963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173586067007470189062617 130189550255602641796963)
            ·
              refine ⟨195284325383403962695445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130189550255602641796963 195284325383403962695445)
              ·
                refine ⟨9153952752347060751349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195284325383403962695445 9153952752347060751349)
                ·
                  rfl

theorem cell20_60167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 6].length) (baseStart_60167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60167 prefixEnd_60167 := by exact prefixLift 60167
  have htrace : WordTrace (prefixWord ++ tailWord_60167) baseStart_60167 baseEnd_60167 := by
    simpa [prefixWord, tailWord_60167, baseEnd_60167] using wordTrace_append hprefix tailTrace_60167
  have hstable : (prefixWord ++ tailWord_60167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60167).length < 2 ^ (prefixWord ++ tailWord_60167).sum := by decide
  have hdescent : baseEnd_60167 < baseStart_60167 := by decide
  rcases family_descends (prefixWord ++ tailWord_60167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60188 : List Nat := [2, 2, 3, 1, 1, 3, 8]
def baseStart_60188 : Nat := 118140960795 + 60188 * 2 ^ 59
def prefixEnd_60188 : Nat := 4983230072969 + 3 ^ 40 * 60188 * 2
def baseEnd_60188 : Nat := 3052382581028715839329

theorem tailTrace_60188 : CollatzResearch.WordTrace tailWord_60188 prefixEnd_60188 3052382581028715839329 := by
  unfold tailWord_60188
  simp only [CollatzResearch.WordTrace]
  refine ⟨1097618352978315068566609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1463491137304420091422145 1097618352978315068566609)
  ·
    refine ⟨823213764733736301424957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1097618352978315068566609 823213764733736301424957)
    ·
      refine ⟨308705161775151113034359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 823213764733736301424957 308705161775151113034359)
      ·
        refine ⟨463057742662726669551539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308705161775151113034359 463057742662726669551539)
        ·
          refine ⟨694586613994090004327309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463057742662726669551539 694586613994090004327309)
          ·
            refine ⟨260469980247783751622741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 694586613994090004327309 260469980247783751622741)
            ·
              refine ⟨3052382581028715839329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 260469980247783751622741 3052382581028715839329)
              ·
                rfl

theorem cell20_60188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 8].length) (baseStart_60188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60188 prefixEnd_60188 := by exact prefixLift 60188
  have htrace : WordTrace (prefixWord ++ tailWord_60188) baseStart_60188 baseEnd_60188 := by
    simpa [prefixWord, tailWord_60188, baseEnd_60188] using wordTrace_append hprefix tailTrace_60188
  have hstable : (prefixWord ++ tailWord_60188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60188).length < 2 ^ (prefixWord ++ tailWord_60188).sum := by decide
  have hdescent : baseEnd_60188 < baseStart_60188 := by decide
  rcases family_descends (prefixWord ++ tailWord_60188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60194 : List Nat := [3, 3, 1, 1, 2, 3, 3, 2, 2]
def baseStart_60194 : Nat := 118140960795 + 60194 * 2 ^ 59
def prefixEnd_60194 : Nat := 4983230072969 + 3 ^ 40 * 60194 * 2
def baseEnd_60194 : Nat := 27474181792749088353937

theorem tailTrace_60194 : CollatzResearch.WordTrace tailWord_60194 prefixEnd_60194 27474181792749088353937 := by
  unfold tailWord_60194
  simp only [CollatzResearch.WordTrace]
  refine ⟨548863885983723290462909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1463637029289928774567757 548863885983723290462909)
  ·
    refine ⟨205823957243896233923591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 548863885983723290462909 205823957243896233923591)
    ·
      refine ⟨308735935865844350885387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205823957243896233923591 308735935865844350885387)
      ·
        refine ⟨463103903798766526328081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308735935865844350885387 463103903798766526328081)
        ·
          refine ⟨347327927849074894746061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463103903798766526328081 347327927849074894746061)
          ·
            refine ⟨130247972943403085529773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347327927849074894746061 130247972943403085529773)
            ·
              refine ⟨48842989853776157073665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130247972943403085529773 48842989853776157073665)
              ·
                refine ⟨36632242390332117805249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48842989853776157073665 36632242390332117805249)
                ·
                  refine ⟨27474181792749088353937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36632242390332117805249 27474181792749088353937)
                  ·
                    rfl

theorem cell20_60194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_60194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60194 prefixEnd_60194 := by exact prefixLift 60194
  have htrace : WordTrace (prefixWord ++ tailWord_60194) baseStart_60194 baseEnd_60194 := by
    simpa [prefixWord, tailWord_60194, baseEnd_60194] using wordTrace_append hprefix tailTrace_60194
  have hstable : (prefixWord ++ tailWord_60194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60194).length < 2 ^ (prefixWord ++ tailWord_60194).sum := by decide
  have hdescent : baseEnd_60194 < baseStart_60194 := by decide
  rcases family_descends (prefixWord ++ tailWord_60194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60250 : List Nat := [3, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_60250 : Nat := 118140960795 + 60250 * 2 ^ 59
def prefixEnd_60250 : Nat := 4983230072969 + 3 ^ 40 * 60250 * 2
def baseEnd_60250 : Nat := 27499741718661782487041

theorem tailTrace_60250 : CollatzResearch.WordTrace tailWord_60250 prefixEnd_60250 27499741718661782487041 := by
  unfold tailWord_60250
  simp only [CollatzResearch.WordTrace]
  refine ⟨549374507933003681472551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1464998687821343150593469 549374507933003681472551)
  ·
    refine ⟨824061761899505522208827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 549374507933003681472551 824061761899505522208827)
    ·
      refine ⟨1236092642849258283313241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 824061761899505522208827 1236092642849258283313241)
      ·
        refine ⟨927069482136943712484931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1236092642849258283313241 927069482136943712484931)
        ·
          refine ⟨1390604223205415568727397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 927069482136943712484931 1390604223205415568727397)
          ·
            refine ⟨260738291851015419136387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1390604223205415568727397 260738291851015419136387)
            ·
              refine ⟨391107437776523128704581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260738291851015419136387 391107437776523128704581)
              ·
                refine ⟨73332644583098086632109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391107437776523128704581 73332644583098086632109)
                ·
                  refine ⟨27499741718661782487041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73332644583098086632109 27499741718661782487041)
                  ·
                    rfl

theorem cell20_60250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_60250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60250 prefixEnd_60250 := by exact prefixLift 60250
  have htrace : WordTrace (prefixWord ++ tailWord_60250) baseStart_60250 baseEnd_60250 := by
    simpa [prefixWord, tailWord_60250, baseEnd_60250] using wordTrace_append hprefix tailTrace_60250
  have hstable : (prefixWord ++ tailWord_60250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60250).length < 2 ^ (prefixWord ++ tailWord_60250).sum := by decide
  have hdescent : baseEnd_60250 < baseStart_60250 := by decide
  rcases family_descends (prefixWord ++ tailWord_60250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60281 : List Nat := [1, 2, 1, 3, 2, 4, 3, 4]
def baseStart_60281 : Nat := 118140960795 + 60281 * 2 ^ 59
def prefixEnd_60281 : Nat := 4983230072969 + 3 ^ 40 * 60281 * 2
def baseEnd_60281 : Nat := 9171296987787817484527

theorem tailTrace_60281 : CollatzResearch.WordTrace tailWord_60281 prefixEnd_60281 9171296987787817484527 := by
  unfold tailWord_60281
  simp only [CollatzResearch.WordTrace]
  refine ⟨2198628694619707020268697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1465752463079804680179131 2198628694619707020268697)
  ·
    refine ⟨1648971520964780265201523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2198628694619707020268697 1648971520964780265201523)
    ·
      refine ⟨2473457281447170397802285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1648971520964780265201523 2473457281447170397802285)
      ·
        refine ⟨927546480542688899175857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2473457281447170397802285 927546480542688899175857)
        ·
          refine ⟨695659860407016674381893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 927546480542688899175857 695659860407016674381893)
          ·
            refine ⟨130436223826315626446605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 695659860407016674381893 130436223826315626446605)
            ·
              refine ⟨48913583934868359917477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130436223826315626446605 48913583934868359917477)
              ·
                refine ⟨9171296987787817484527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48913583934868359917477 9171296987787817484527)
                ·
                  rfl

theorem cell20_60281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 4].length) (baseStart_60281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60281 prefixEnd_60281 := by exact prefixLift 60281
  have htrace : WordTrace (prefixWord ++ tailWord_60281) baseStart_60281 baseEnd_60281 := by
    simpa [prefixWord, tailWord_60281, baseEnd_60281] using wordTrace_append hprefix tailTrace_60281
  have hstable : (prefixWord ++ tailWord_60281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60281).length < 2 ^ (prefixWord ++ tailWord_60281).sum := by decide
  have hdescent : baseEnd_60281 < baseStart_60281 := by decide
  rcases family_descends (prefixWord ++ tailWord_60281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60322 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_60322 : Nat := 118140960795 + 60322 * 2 ^ 59
def prefixEnd_60322 : Nat := 4983230072969 + 3 ^ 40 * 60322 * 2
def baseEnd_60322 : Nat := 27532604480549532086747

theorem tailTrace_60322 : CollatzResearch.WordTrace tailWord_60322 prefixEnd_60322 27532604480549532086747 := by
  unfold tailWord_60322
  simp only [CollatzResearch.WordTrace]
  refine ⟨550031021867792755627805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1466749391647447348340813 550031021867792755627805)
  ·
    refine ⟨206261633200422283360427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 550031021867792755627805 206261633200422283360427)
    ·
      refine ⟨309392449800633425040641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206261633200422283360427 309392449800633425040641)
      ·
        refine ⟨232044337350475068780481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309392449800633425040641 232044337350475068780481)
        ·
          refine ⟨174033253012856301585361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232044337350475068780481 174033253012856301585361)
          ·
            refine ⟨130524939759642226189021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174033253012856301585361 130524939759642226189021)
            ·
              refine ⟨48946852409865834820883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130524939759642226189021 48946852409865834820883)
              ·
                refine ⟨73420278614798752231325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48946852409865834820883 73420278614798752231325)
                ·
                  refine ⟨27532604480549532086747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73420278614798752231325 27532604480549532086747)
                  ·
                    rfl

theorem cell20_60322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_60322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60322 prefixEnd_60322 := by exact prefixLift 60322
  have htrace : WordTrace (prefixWord ++ tailWord_60322) baseStart_60322 baseEnd_60322 := by
    simpa [prefixWord, tailWord_60322, baseEnd_60322] using wordTrace_append hprefix tailTrace_60322
  have hstable : (prefixWord ++ tailWord_60322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60322).length < 2 ^ (prefixWord ++ tailWord_60322).sum := by decide
  have hdescent : baseEnd_60322 < baseStart_60322 := by decide
  rcases family_descends (prefixWord ++ tailWord_60322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60364 : List Nat := [2, 2, 1, 4, 1, 1, 2, 4, 3]
def baseStart_60364 : Nat := 118140960795 + 60364 * 2 ^ 59
def prefixEnd_60364 : Nat := 4983230072969 + 3 ^ 40 * 60364 * 2
def baseEnd_60364 : Nat := 27551774424984052686575

theorem tailTrace_60364 : CollatzResearch.WordTrace tailWord_60364 prefixEnd_60364 27551774424984052686575 := by
  unfold tailWord_60364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1100827976659506097770073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1467770635546008130360097 1100827976659506097770073)
  ·
    refine ⟨825620982494629573327555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1100827976659506097770073 825620982494629573327555)
    ·
      refine ⟨1238431473741944359991333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 825620982494629573327555 1238431473741944359991333)
      ·
        refine ⟨232205901326614567498375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1238431473741944359991333 232205901326614567498375)
        ·
          refine ⟨348308851989921851247563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232205901326614567498375 348308851989921851247563)
          ·
            refine ⟨522463277984882776871345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 348308851989921851247563 522463277984882776871345)
            ·
              refine ⟨391847458488662082653509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 522463277984882776871345 391847458488662082653509)
              ·
                refine ⟨73471398466624140497533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391847458488662082653509 73471398466624140497533)
                ·
                  refine ⟨27551774424984052686575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73471398466624140497533 27551774424984052686575)
                  ·
                    rfl

theorem cell20_60364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_60364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60364 prefixEnd_60364 := by exact prefixLift 60364
  have htrace : WordTrace (prefixWord ++ tailWord_60364) baseStart_60364 baseEnd_60364 := by
    simpa [prefixWord, tailWord_60364, baseEnd_60364] using wordTrace_append hprefix tailTrace_60364
  have hstable : (prefixWord ++ tailWord_60364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60364).length < 2 ^ (prefixWord ++ tailWord_60364).sum := by decide
  have hdescent : baseEnd_60364 < baseStart_60364 := by decide
  rcases family_descends (prefixWord ++ tailWord_60364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60367 : List Nat := [1, 1, 2, 1, 1, 7, 3, 2, 2]
def baseStart_60367 : Nat := 118140960795 + 60367 * 2 ^ 59
def prefixEnd_60367 : Nat := 4983230072969 + 3 ^ 40 * 60367 * 2
def baseEnd_60367 : Nat := 27553143706729375586563

theorem tailTrace_60367 : CollatzResearch.WordTrace tailWord_60367 prefixEnd_60367 27553143706729375586563 := by
  unfold tailWord_60367
  simp only [CollatzResearch.WordTrace]
  refine ⟨2201765372308143707899355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1467843581538762471932903 2201765372308143707899355)
  ·
    refine ⟨3302648058462215561849033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2201765372308143707899355 3302648058462215561849033)
    ·
      refine ⟨2476986043846661671386775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3302648058462215561849033 2476986043846661671386775)
      ·
        refine ⟨3715479065769992507080163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2476986043846661671386775 3715479065769992507080163)
        ·
          refine ⟨5573218598654988760620245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3715479065769992507080163 5573218598654988760620245)
          ·
            refine ⟨130622310905976299077037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5573218598654988760620245 130622310905976299077037)
            ·
              refine ⟨48983366589741112153889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130622310905976299077037 48983366589741112153889)
              ·
                refine ⟨36737524942305834115417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48983366589741112153889 36737524942305834115417)
                ·
                  refine ⟨27553143706729375586563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36737524942305834115417 27553143706729375586563)
                  ·
                    rfl

theorem cell20_60367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 2].length) (baseStart_60367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60367 prefixEnd_60367 := by exact prefixLift 60367
  have htrace : WordTrace (prefixWord ++ tailWord_60367) baseStart_60367 baseEnd_60367 := by
    simpa [prefixWord, tailWord_60367, baseEnd_60367] using wordTrace_append hprefix tailTrace_60367
  have hstable : (prefixWord ++ tailWord_60367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60367).length < 2 ^ (prefixWord ++ tailWord_60367).sum := by decide
  have hdescent : baseEnd_60367 < baseStart_60367 := by decide
  rcases family_descends (prefixWord ++ tailWord_60367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60374 : List Nat := [5, 2, 1, 1, 2, 2, 2, 5]
def baseStart_60374 : Nat := 118140960795 + 60374 * 2 ^ 59
def prefixEnd_60374 : Nat := 4983230072969 + 3 ^ 40 * 60374 * 2
def baseEnd_60374 : Nat := 9185446232489487451067

theorem tailTrace_60374 : CollatzResearch.WordTrace tailWord_60374 prefixEnd_60374 9185446232489487451067 := by
  unfold tailWord_60374
  simp only [CollatzResearch.WordTrace]
  refine ⟨137626292705173993962761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1468013788855189268936117 137626292705173993962761)
  ·
    refine ⟨103219719528880495472071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137626292705173993962761 103219719528880495472071)
    ·
      refine ⟨154829579293320743208107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103219719528880495472071 154829579293320743208107)
      ·
        refine ⟨232244368939981114812161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154829579293320743208107 232244368939981114812161)
        ·
          refine ⟨174183276704985836109121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232244368939981114812161 174183276704985836109121)
          ·
            refine ⟨130637457528739377081841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174183276704985836109121 130637457528739377081841)
            ·
              refine ⟨97978093146554532811381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130637457528739377081841 97978093146554532811381)
              ·
                refine ⟨9185446232489487451067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97978093146554532811381 9185446232489487451067)
                ·
                  rfl

theorem cell20_60374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_60374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60374 prefixEnd_60374 := by exact prefixLift 60374
  have htrace : WordTrace (prefixWord ++ tailWord_60374) baseStart_60374 baseEnd_60374 := by
    simpa [prefixWord, tailWord_60374, baseEnd_60374] using wordTrace_append hprefix tailTrace_60374
  have hstable : (prefixWord ++ tailWord_60374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60374).length < 2 ^ (prefixWord ++ tailWord_60374).sum := by decide
  have hdescent : baseEnd_60374 < baseStart_60374 := by decide
  rcases family_descends (prefixWord ++ tailWord_60374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60378 : List Nat := [3, 1, 1, 2, 4, 1, 1, 7]
def baseStart_60378 : Nat := 118140960795 + 60378 * 2 ^ 59
def prefixEnd_60378 : Nat := 4983230072969 + 3 ^ 40 * 60378 * 2
def baseEnd_60378 : Nat := 9186054802154075406617

theorem tailTrace_60378 : CollatzResearch.WordTrace tailWord_60378 prefixEnd_60378 9186054802154075406617 := by
  unfold tailWord_60378
  simp only [CollatzResearch.WordTrace]
  refine ⟨550541643817073146637447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1468111050178861724366525 550541643817073146637447)
  ·
    refine ⟨825812465725609719956171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 550541643817073146637447 825812465725609719956171)
    ·
      refine ⟨1238718698588414579934257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 825812465725609719956171 1238718698588414579934257)
      ·
        refine ⟨929039023941310934950693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1238718698588414579934257 929039023941310934950693)
        ·
          refine ⟨174194816988995800303255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 929039023941310934950693 174194816988995800303255)
          ·
            refine ⟨261292225483493700454883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174194816988995800303255 261292225483493700454883)
            ·
              refine ⟨391938338225240550682325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261292225483493700454883 391938338225240550682325)
              ·
                refine ⟨9186054802154075406617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 391938338225240550682325 9186054802154075406617)
                ·
                  rfl

theorem cell20_60378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_60378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60378 prefixEnd_60378 := by exact prefixLift 60378
  have htrace : WordTrace (prefixWord ++ tailWord_60378) baseStart_60378 baseEnd_60378 := by
    simpa [prefixWord, tailWord_60378, baseEnd_60378] using wordTrace_append hprefix tailTrace_60378
  have hstable : (prefixWord ++ tailWord_60378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60378).length < 2 ^ (prefixWord ++ tailWord_60378).sum := by decide
  have hdescent : baseEnd_60378 < baseStart_60378 := by decide
  rcases family_descends (prefixWord ++ tailWord_60378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60381 : List Nat := [1, 4, 3, 1, 2, 2, 1, 3, 3]
def baseStart_60381 : Nat := 118140960795 + 60381 * 2 ^ 59
def prefixEnd_60381 : Nat := 4983230072969 + 3 ^ 40 * 60381 * 2
def baseEnd_60381 : Nat := 27559533688207549119839

theorem tailTrace_60381 : CollatzResearch.WordTrace tailWord_60381 prefixEnd_60381 27559533688207549119839 := by
  unfold tailWord_60381
  simp only [CollatzResearch.WordTrace]
  refine ⟨2202275994257424098908997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1468183996171616065939331 2202275994257424098908997)
  ·
    refine ⟨412926748923267018545437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2202275994257424098908997 412926748923267018545437)
    ·
      refine ⟨154847530846225131954539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 412926748923267018545437 154847530846225131954539)
      ·
        refine ⟨232271296269337697931809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154847530846225131954539 232271296269337697931809)
        ·
          refine ⟨174203472202003273448857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232271296269337697931809 174203472202003273448857)
          ·
            refine ⟨130652604151502455086643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174203472202003273448857 130652604151502455086643)
            ·
              refine ⟨195978906227253682629965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130652604151502455086643 195978906227253682629965)
              ·
                refine ⟨73492089835220130986237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195978906227253682629965 73492089835220130986237)
                ·
                  refine ⟨27559533688207549119839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73492089835220130986237 27559533688207549119839)
                  ·
                    rfl

theorem cell20_60381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_60381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60381 prefixEnd_60381 := by exact prefixLift 60381
  have htrace : WordTrace (prefixWord ++ tailWord_60381) baseStart_60381 baseEnd_60381 := by
    simpa [prefixWord, tailWord_60381, baseEnd_60381] using wordTrace_append hprefix tailTrace_60381
  have hstable : (prefixWord ++ tailWord_60381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60381).length < 2 ^ (prefixWord ++ tailWord_60381).sum := by decide
  have hdescent : baseEnd_60381 < baseStart_60381 := by decide
  rcases family_descends (prefixWord ++ tailWord_60381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60418 : List Nat := [3, 4, 1, 3, 1, 2, 2, 2, 2]
def baseStart_60418 : Nat := 118140960795 + 60418 * 2 ^ 59
def prefixEnd_60418 : Nat := 4983230072969 + 3 ^ 40 * 60418 * 2
def baseEnd_60418 : Nat := 27576421496399864886355

theorem tailTrace_60418 : CollatzResearch.WordTrace tailWord_60418 prefixEnd_60418 27576421496399864886355 := by
  unfold tailWord_60418
  simp only [CollatzResearch.WordTrace]
  refine ⟨550906373780844854501477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1469083663415586278670605 550906373780844854501477)
  ·
    refine ⟨103294945083908410219027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 550906373780844854501477 103294945083908410219027)
    ·
      refine ⟨154942417625862615328541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103294945083908410219027 154942417625862615328541)
      ·
        refine ⟨58103406609698480748203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154942417625862615328541 58103406609698480748203)
        ·
          refine ⟨87155109914547721122305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58103406609698480748203 87155109914547721122305)
          ·
            refine ⟨65366332435910790841729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87155109914547721122305 65366332435910790841729)
            ·
              refine ⟨49024749326933093131297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65366332435910790841729 49024749326933093131297)
              ·
                refine ⟨36768561995199819848473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49024749326933093131297 36768561995199819848473)
                ·
                  refine ⟨27576421496399864886355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36768561995199819848473 27576421496399864886355)
                  ·
                    rfl

theorem cell20_60418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_60418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60418 prefixEnd_60418 := by exact prefixLift 60418
  have htrace : WordTrace (prefixWord ++ tailWord_60418) baseStart_60418 baseEnd_60418 := by
    simpa [prefixWord, tailWord_60418, baseEnd_60418] using wordTrace_append hprefix tailTrace_60418
  have hstable : (prefixWord ++ tailWord_60418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60418).length < 2 ^ (prefixWord ++ tailWord_60418).sum := by decide
  have hdescent : baseEnd_60418 < baseStart_60418 := by decide
  rcases family_descends (prefixWord ++ tailWord_60418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60440 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 3]
def baseStart_60440 : Nat := 118140960795 + 60440 * 2 ^ 59
def prefixEnd_60440 : Nat := 4983230072969 + 3 ^ 40 * 60440 * 2
def baseEnd_60440 : Nat := 27586462895865566152931

theorem tailTrace_60440 : CollatzResearch.WordTrace tailWord_60440 prefixEnd_60440 27586462895865566152931 := by
  unfold tailWord_60440
  simp only [CollatzResearch.WordTrace]
  refine ⟨1102213950521838587653387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1469618600695784783537849 1102213950521838587653387)
  ·
    refine ⟨1653320925782757881480081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1102213950521838587653387 1653320925782757881480081)
    ·
      refine ⟨1239990694337068411110061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1653320925782757881480081 1239990694337068411110061)
      ·
        refine ⟨464996510376400654166273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1239990694337068411110061 464996510376400654166273)
        ·
          refine ⟨348747382782300490624705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464996510376400654166273 348747382782300490624705)
          ·
            refine ⟨261560537086725367968529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348747382782300490624705 261560537086725367968529)
            ·
              refine ⟨196170402815044025976397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261560537086725367968529 196170402815044025976397)
              ·
                refine ⟨73563901055641509741149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196170402815044025976397 73563901055641509741149)
                ·
                  refine ⟨27586462895865566152931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73563901055641509741149 27586462895865566152931)
                  ·
                    rfl

theorem cell20_60440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_60440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60440 prefixEnd_60440 := by exact prefixLift 60440
  have htrace : WordTrace (prefixWord ++ tailWord_60440) baseStart_60440 baseEnd_60440 := by
    simpa [prefixWord, tailWord_60440, baseEnd_60440] using wordTrace_append hprefix tailTrace_60440
  have hstable : (prefixWord ++ tailWord_60440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60440).length < 2 ^ (prefixWord ++ tailWord_60440).sum := by decide
  have hdescent : baseEnd_60440 < baseStart_60440 := by decide
  rcases family_descends (prefixWord ++ tailWord_60440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60447 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 4]
def baseStart_60447 : Nat := 118140960795 + 60447 * 2 ^ 59
def prefixEnd_60447 : Nat := 4983230072969 + 3 ^ 40 * 60447 * 2
def baseEnd_60447 : Nat := 27589657886604652919569

theorem tailTrace_60447 : CollatzResearch.WordTrace tailWord_60447 prefixEnd_60447 27589657886604652919569 := by
  unfold tailWord_60447
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204683212018317370811595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1469788808012211580541063 2204683212018317370811595)
  ·
    refine ⟨3307024818027476056217393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2204683212018317370811595 3307024818027476056217393)
    ·
      refine ⟨2480268613520607042163045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3307024818027476056217393 2480268613520607042163045)
      ·
        refine ⟨465050365035113820405571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2480268613520607042163045 465050365035113820405571)
        ·
          refine ⟨697575547552670730608357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465050365035113820405571 697575547552670730608357)
          ·
            refine ⟨130795415166125761989067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 697575547552670730608357 130795415166125761989067)
            ·
              refine ⟨196193122749188642983601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130795415166125761989067 196193122749188642983601)
              ·
                refine ⟨147144842061891482237701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 196193122749188642983601 147144842061891482237701)
                ·
                  refine ⟨27589657886604652919569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 147144842061891482237701 27589657886604652919569)
                  ·
                    rfl

theorem cell20_60447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_60447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60447 prefixEnd_60447 := by exact prefixLift 60447
  have htrace : WordTrace (prefixWord ++ tailWord_60447) baseStart_60447 baseEnd_60447 := by
    simpa [prefixWord, tailWord_60447, baseEnd_60447] using wordTrace_append hprefix tailTrace_60447
  have hstable : (prefixWord ++ tailWord_60447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60447).length < 2 ^ (prefixWord ++ tailWord_60447).sum := by decide
  have hdescent : baseEnd_60447 < baseStart_60447 := by decide
  rcases family_descends (prefixWord ++ tailWord_60447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60464 : List Nat := [2, 1, 1, 1, 2, 4, 4, 3, 2]
def baseStart_60464 : Nat := 118140960795 + 60464 * 2 ^ 59
def prefixEnd_60464 : Nat := 4983230072969 + 3 ^ 40 * 60464 * 2
def baseEnd_60464 : Nat := 27597417149828149352833

theorem tailTrace_60464 : CollatzResearch.WordTrace tailWord_60464 prefixEnd_60464 27597417149828149352833 := by
  unfold tailWord_60464
  simp only [CollatzResearch.WordTrace]
  refine ⟨1102651626478364637090223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1470202168637819516120297 1102651626478364637090223)
  ·
    refine ⟨1653977439717546955635335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1102651626478364637090223 1653977439717546955635335)
    ·
      refine ⟨2480966159576320433453003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653977439717546955635335 2480966159576320433453003)
      ·
        refine ⟨3721449239364480650179505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2480966159576320433453003 3721449239364480650179505)
        ·
          refine ⟨2791086929523360487634629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3721449239364480650179505 2791086929523360487634629)
          ·
            refine ⟨523328799285630091431493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2791086929523360487634629 523328799285630091431493)
            ·
              refine ⟨98124149866055642143405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 523328799285630091431493 98124149866055642143405)
              ·
                refine ⟨36796556199770865803777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98124149866055642143405 36796556199770865803777)
                ·
                  refine ⟨27597417149828149352833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36796556199770865803777 27597417149828149352833)
                  ·
                    rfl

theorem cell20_60464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 2].length) (baseStart_60464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60464 prefixEnd_60464 := by exact prefixLift 60464
  have htrace : WordTrace (prefixWord ++ tailWord_60464) baseStart_60464 baseEnd_60464 := by
    simpa [prefixWord, tailWord_60464, baseEnd_60464] using wordTrace_append hprefix tailTrace_60464
  have hstable : (prefixWord ++ tailWord_60464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60464).length < 2 ^ (prefixWord ++ tailWord_60464).sum := by decide
  have hdescent : baseEnd_60464 < baseStart_60464 := by decide
  rcases family_descends (prefixWord ++ tailWord_60464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60506 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_60506 : Nat := 118140960795 + 60506 * 2 ^ 59
def prefixEnd_60506 : Nat := 4983230072969 + 3 ^ 40 * 60506 * 2
def baseEnd_60506 : Nat := 27616587094262669952661

theorem tailTrace_60506 : CollatzResearch.WordTrace tailWord_60506 prefixEnd_60506 27616587094262669952661 := by
  unfold tailWord_60506
  simp only [CollatzResearch.WordTrace]
  refine ⟨551708779701142611802343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1471223412536380298139581 551708779701142611802343)
  ·
    refine ⟨827563169551713917703515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 551708779701142611802343 827563169551713917703515)
    ·
      refine ⟨1241344754327570876555273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 827563169551713917703515 1241344754327570876555273)
      ·
        refine ⟨931008565745678157416455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1241344754327570876555273 931008565745678157416455)
        ·
          refine ⟨1396512848618517236124683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 931008565745678157416455 1396512848618517236124683)
          ·
            refine ⟨2094769272927775854187025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1396512848618517236124683 2094769272927775854187025)
            ·
              refine ⟨1571076954695831890640269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2094769272927775854187025 1571076954695831890640269)
              ·
                refine ⟨589153858010936958990101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1571076954695831890640269 589153858010936958990101)
                ·
                  refine ⟨27616587094262669952661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 589153858010936958990101 27616587094262669952661)
                  ·
                    rfl

theorem cell20_60506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_60506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60506 prefixEnd_60506 := by exact prefixLift 60506
  have htrace : WordTrace (prefixWord ++ tailWord_60506) baseStart_60506 baseEnd_60506 := by
    simpa [prefixWord, tailWord_60506, baseEnd_60506] using wordTrace_append hprefix tailTrace_60506
  have hstable : (prefixWord ++ tailWord_60506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60506).length < 2 ^ (prefixWord ++ tailWord_60506).sum := by decide
  have hdescent : baseEnd_60506 < baseStart_60506 := by decide
  rcases family_descends (prefixWord ++ tailWord_60506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60519 : List Nat := [1, 1, 5, 1, 1, 5, 1, 3, 2]
def baseStart_60519 : Nat := 118140960795 + 60519 * 2 ^ 59
def prefixEnd_60519 : Nat := 4983230072969 + 3 ^ 40 * 60519 * 2
def baseEnd_60519 : Nat := 27622520648492402519275

theorem tailTrace_60519 : CollatzResearch.WordTrace tailWord_60519 prefixEnd_60519 27622520648492402519275 := by
  unfold tailWord_60519
  simp only [CollatzResearch.WordTrace]
  refine ⟨2207309267757473667432611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1471539511838315778288407 2207309267757473667432611)
  ·
    refine ⟨3310963901636210501148917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2207309267757473667432611 3310963901636210501148917)
    ·
      refine ⟨310402865778394734482711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3310963901636210501148917 310402865778394734482711)
      ·
        refine ⟨465604298667592101724067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 310402865778394734482711 465604298667592101724067)
        ·
          refine ⟨698406448001388152586101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 465604298667592101724067 698406448001388152586101)
          ·
            refine ⟨65475604500130139304947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 698406448001388152586101 65475604500130139304947)
            ·
              refine ⟨98213406750195208957421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65475604500130139304947 98213406750195208957421)
              ·
                refine ⟨36830027531323203359033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98213406750195208957421 36830027531323203359033)
                ·
                  refine ⟨27622520648492402519275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36830027531323203359033 27622520648492402519275)
                  ·
                    rfl

theorem cell20_60519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 2].length) (baseStart_60519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60519 prefixEnd_60519 := by exact prefixLift 60519
  have htrace : WordTrace (prefixWord ++ tailWord_60519) baseStart_60519 baseEnd_60519 := by
    simpa [prefixWord, tailWord_60519, baseEnd_60519] using wordTrace_append hprefix tailTrace_60519
  have hstable : (prefixWord ++ tailWord_60519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60519).length < 2 ^ (prefixWord ++ tailWord_60519).sum := by decide
  have hdescent : baseEnd_60519 < baseStart_60519 := by decide
  rcases family_descends (prefixWord ++ tailWord_60519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60554 : List Nat := [3, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_60554 : Nat := 118140960795 + 60554 * 2 ^ 59
def prefixEnd_60554 : Nat := 4983230072969 + 3 ^ 40 * 60554 * 2
def baseEnd_60554 : Nat := 27638495602187836352465

theorem tailTrace_60554 : CollatzResearch.WordTrace tailWord_60554 prefixEnd_60554 27638495602187836352465 := by
  unfold tailWord_60554
  simp only [CollatzResearch.WordTrace]
  refine ⟨552146455657668661239179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1472390548420449763304477 552146455657668661239179)
  ·
    refine ⟨828219683486502991858769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 552146455657668661239179 828219683486502991858769)
    ·
      refine ⟨621164762614877243894077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 828219683486502991858769 621164762614877243894077)
      ·
        refine ⟨232936785980578966460279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 621164762614877243894077 232936785980578966460279)
        ·
          refine ⟨349405178970868449690419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 232936785980578966460279 349405178970868449690419)
          ·
            refine ⟨524107768456302674535629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349405178970868449690419 524107768456302674535629)
            ·
              refine ⟨196540413171113502950861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 524107768456302674535629 196540413171113502950861)
              ·
                refine ⟨73702654939167563606573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196540413171113502950861 73702654939167563606573)
                ·
                  refine ⟨27638495602187836352465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73702654939167563606573 27638495602187836352465)
                  ·
                    rfl

theorem cell20_60554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_60554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60554 prefixEnd_60554 := by exact prefixLift 60554
  have htrace : WordTrace (prefixWord ++ tailWord_60554) baseStart_60554 baseEnd_60554 := by
    simpa [prefixWord, tailWord_60554, baseEnd_60554] using wordTrace_append hprefix tailTrace_60554
  have hstable : (prefixWord ++ tailWord_60554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60554).length < 2 ^ (prefixWord ++ tailWord_60554).sum := by decide
  have hdescent : baseEnd_60554 < baseStart_60554 := by decide
  rcases family_descends (prefixWord ++ tailWord_60554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60568 : List Nat := [2, 1, 2, 4, 2, 1, 2, 6]
def baseStart_60568 : Nat := 118140960795 + 60568 * 2 ^ 59
def prefixEnd_60568 : Nat := 4983230072969 + 3 ^ 40 * 60568 * 2
def baseEnd_60568 : Nat := 9214961861222003295247

theorem tailTrace_60568 : CollatzResearch.WordTrace tailWord_60568 prefixEnd_60568 9214961861222003295247 := by
  unfold tailWord_60568
  simp only [CollatzResearch.WordTrace]
  refine ⟨1104548222289977517983179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1472730963053303357310905 1104548222289977517983179)
  ·
    refine ⟨1656822333434966276974769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1104548222289977517983179 1656822333434966276974769)
    ·
      refine ⟨1242616750076224707731077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1656822333434966276974769 1242616750076224707731077)
      ·
        refine ⟨232990640639292132699577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1242616750076224707731077 232990640639292132699577)
        ·
          refine ⟨174742980479469099524683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232990640639292132699577 174742980479469099524683)
          ·
            refine ⟨262114470719203649287025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174742980479469099524683 262114470719203649287025)
            ·
              refine ⟨196585853039402736965269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262114470719203649287025 196585853039402736965269)
              ·
                refine ⟨9214961861222003295247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 196585853039402736965269 9214961861222003295247)
                ·
                  rfl

theorem cell20_60568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_60568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60568 prefixEnd_60568 := by exact prefixLift 60568
  have htrace : WordTrace (prefixWord ++ tailWord_60568) baseStart_60568 baseEnd_60568 := by
    simpa [prefixWord, tailWord_60568, baseEnd_60568] using wordTrace_append hprefix tailTrace_60568
  have hstable : (prefixWord ++ tailWord_60568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60568).length < 2 ^ (prefixWord ++ tailWord_60568).sum := by decide
  have hdescent : baseEnd_60568 < baseStart_60568 := by decide
  rcases family_descends (prefixWord ++ tailWord_60568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60598 : List Nat := [5, 1, 3, 2, 2, 1, 1, 5]
def baseStart_60598 : Nat := 118140960795 + 60598 * 2 ^ 59
def prefixEnd_60598 : Nat := 4983230072969 + 3 ^ 40 * 60598 * 2
def baseEnd_60598 : Nat := 9219526133706412961873

theorem tailTrace_60598 : CollatzResearch.WordTrace tailWord_60598 prefixEnd_60598 9219526133706412961873 := by
  unfold tailWord_60598
  simp only [CollatzResearch.WordTrace]
  refine ⟨138136914654454384972403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1473460422980846773038965 138136914654454384972403)
  ·
    refine ⟨207205371981681577458605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 138136914654454384972403 207205371981681577458605)
    ·
      refine ⟨77702014493130591546977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 207205371981681577458605 77702014493130591546977)
      ·
        refine ⟨58276510869847943660233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77702014493130591546977 58276510869847943660233)
        ·
          refine ⟨43707383152385957745175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58276510869847943660233 43707383152385957745175)
          ·
            refine ⟨65561074728578936617763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43707383152385957745175 65561074728578936617763)
            ·
              refine ⟨98341612092868404926645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65561074728578936617763 98341612092868404926645)
              ·
                refine ⟨9219526133706412961873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98341612092868404926645 9219526133706412961873)
                ·
                  rfl

theorem cell20_60598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_60598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60598 prefixEnd_60598 := by exact prefixLift 60598
  have htrace : WordTrace (prefixWord ++ tailWord_60598) baseStart_60598 baseEnd_60598 := by
    simpa [prefixWord, tailWord_60598, baseEnd_60598] using wordTrace_append hprefix tailTrace_60598
  have hstable : (prefixWord ++ tailWord_60598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60598).length < 2 ^ (prefixWord ++ tailWord_60598).sum := by decide
  have hdescent : baseEnd_60598 < baseStart_60598 := by decide
  rcases family_descends (prefixWord ++ tailWord_60598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60609 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 3]
def baseStart_60609 : Nat := 118140960795 + 60609 * 2 ^ 59
def prefixEnd_60609 : Nat := 4983230072969 + 3 ^ 40 * 60609 * 2
def baseEnd_60609 : Nat := 27663599100852089518907

theorem tailTrace_60609 : CollatzResearch.WordTrace tailWord_60609 prefixEnd_60609 27663599100852089518907 := by
  unfold tailWord_60609
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210591837431419038208881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1473727891620946025472587 2210591837431419038208881)
  ·
    refine ⟨1657943878073564278656661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2210591837431419038208881 1657943878073564278656661)
    ·
      refine ⟨77716119284698325562031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1657943878073564278656661 77716119284698325562031)
      ·
        refine ⟨116574178927047488343047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77716119284698325562031 116574178927047488343047)
        ·
          refine ⟨174861268390571232514571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116574178927047488343047 174861268390571232514571)
          ·
            refine ⟨262291902585856848771857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 174861268390571232514571 262291902585856848771857)
            ·
              refine ⟨196718926939392636578893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262291902585856848771857 196718926939392636578893)
              ·
                refine ⟨73769597602272238717085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 196718926939392636578893 73769597602272238717085)
                ·
                  refine ⟨27663599100852089518907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73769597602272238717085 27663599100852089518907)
                  ·
                    rfl

theorem cell20_60609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_60609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60609 prefixEnd_60609 := by exact prefixLift 60609
  have htrace : WordTrace (prefixWord ++ tailWord_60609) baseStart_60609 baseEnd_60609 := by
    simpa [prefixWord, tailWord_60609, baseEnd_60609] using wordTrace_append hprefix tailTrace_60609
  have hstable : (prefixWord ++ tailWord_60609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60609).length < 2 ^ (prefixWord ++ tailWord_60609).sum := by decide
  have hdescent : baseEnd_60609 < baseStart_60609 := by decide
  rcases family_descends (prefixWord ++ tailWord_60609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60651 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 5]
def baseStart_60651 : Nat := 118140960795 + 60651 * 2 ^ 59
def prefixEnd_60651 : Nat := 4983230072969 + 3 ^ 40 * 60651 * 2
def baseEnd_60651 : Nat := 27682769045286610118735

theorem tailTrace_60651 : CollatzResearch.WordTrace tailWord_60651 prefixEnd_60651 27682769045286610118735 := by
  unfold tailWord_60651
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212123703279260211237807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1474749135519506807491871 2212123703279260211237807)
  ·
    refine ⟨3318185554918890316856711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2212123703279260211237807 3318185554918890316856711)
    ·
      refine ⟨4977278332378335475285067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3318185554918890316856711 4977278332378335475285067)
      ·
        refine ⟨7465917498567503212927601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4977278332378335475285067 7465917498567503212927601)
        ·
          refine ⟨5599438123925627409695701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7465917498567503212927601 5599438123925627409695701)
          ·
            refine ⟨131236831029506892414743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5599438123925627409695701 131236831029506892414743)
            ·
              refine ⟨196855246544260338622115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131236831029506892414743 196855246544260338622115)
              ·
                refine ⟨295282869816390507933173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 196855246544260338622115 295282869816390507933173)
                ·
                  refine ⟨27682769045286610118735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 295282869816390507933173 27682769045286610118735)
                  ·
                    rfl

theorem cell20_60651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_60651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60651 prefixEnd_60651 := by exact prefixLift 60651
  have htrace : WordTrace (prefixWord ++ tailWord_60651) baseStart_60651 baseEnd_60651 := by
    simpa [prefixWord, tailWord_60651, baseEnd_60651] using wordTrace_append hprefix tailTrace_60651
  have hstable : (prefixWord ++ tailWord_60651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60651).length < 2 ^ (prefixWord ++ tailWord_60651).sum := by decide
  have hdescent : baseEnd_60651 < baseStart_60651 := by decide
  rcases family_descends (prefixWord ++ tailWord_60651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60654 : List Nat := [4, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_60654 : Nat := 118140960795 + 60654 * 2 ^ 59
def prefixEnd_60654 : Nat := 4983230072969 + 3 ^ 40 * 60654 * 2
def baseEnd_60654 : Nat := 27684138327031933018723

theorem tailTrace_60654 : CollatzResearch.WordTrace tailWord_60654 prefixEnd_60654 27684138327031933018723 := by
  unfold tailWord_60654
  simp only [CollatzResearch.WordTrace]
  refine ⟨276529140283548965449627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1474822081512261149064677 276529140283548965449627)
  ·
    refine ⟨414793710425323448174441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 276529140283548965449627 414793710425323448174441)
    ·
      refine ⟨311095282818992586130831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 414793710425323448174441 311095282818992586130831)
      ·
        refine ⟨466642924228488879196247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311095282818992586130831 466642924228488879196247)
        ·
          refine ⟨699964386342733318794371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466642924228488879196247 699964386342733318794371)
          ·
            refine ⟨1049946579514099978191557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 699964386342733318794371 1049946579514099978191557)
            ·
              refine ⟨196864983658893745910917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1049946579514099978191557 196864983658893745910917)
              ·
                refine ⟨36912184436042577358297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196864983658893745910917 36912184436042577358297)
                ·
                  refine ⟨27684138327031933018723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36912184436042577358297 27684138327031933018723)
                  ·
                    rfl

theorem cell20_60654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_60654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60654 prefixEnd_60654 := by exact prefixLift 60654
  have htrace : WordTrace (prefixWord ++ tailWord_60654) baseStart_60654 baseEnd_60654 := by
    simpa [prefixWord, tailWord_60654, baseEnd_60654] using wordTrace_append hprefix tailTrace_60654
  have hstable : (prefixWord ++ tailWord_60654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60654).length < 2 ^ (prefixWord ++ tailWord_60654).sum := by decide
  have hdescent : baseEnd_60654 < baseStart_60654 := by decide
  rcases family_descends (prefixWord ++ tailWord_60654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60660 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 3]
def baseStart_60660 : Nat := 118140960795 + 60660 * 2 ^ 59
def prefixEnd_60660 : Nat := 4983230072969 + 3 ^ 40 * 60660 * 2
def baseEnd_60660 : Nat := 27686876890522578818699

theorem tailTrace_60660 : CollatzResearch.WordTrace tailWord_60660 prefixEnd_60660 27686876890522578818699 := by
  unfold tailWord_60660
  simp only [CollatzResearch.WordTrace]
  refine ⟨1106225980123327374157717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1474967973497769832210289 1106225980123327374157717)
  ·
    refine ⟨51854342818280970663643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1106225980123327374157717 51854342818280970663643)
    ·
      refine ⟨77781514227421455995465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51854342818280970663643 77781514227421455995465)
      ·
        refine ⟨58336135670566091996599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77781514227421455995465 58336135670566091996599)
        ·
          refine ⟨87504203505849137994899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58336135670566091996599 87504203505849137994899)
          ·
            refine ⟨131256305258773706992349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87504203505849137994899 131256305258773706992349)
            ·
              refine ⟨49221114472040140122131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131256305258773706992349 49221114472040140122131)
              ·
                refine ⟨73831671708060210183197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49221114472040140122131 73831671708060210183197)
                ·
                  refine ⟨27686876890522578818699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73831671708060210183197 27686876890522578818699)
                  ·
                    rfl

theorem cell20_60660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_60660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60660 prefixEnd_60660 := by exact prefixLift 60660
  have htrace : WordTrace (prefixWord ++ tailWord_60660) baseStart_60660 baseEnd_60660 := by
    simpa [prefixWord, tailWord_60660, baseEnd_60660] using wordTrace_append hprefix tailTrace_60660
  have hstable : (prefixWord ++ tailWord_60660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60660).length < 2 ^ (prefixWord ++ tailWord_60660).sum := by decide
  have hdescent : baseEnd_60660 < baseStart_60660 := by decide
  rcases family_descends (prefixWord ++ tailWord_60660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60665 : List Nat := [1, 2, 1, 3, 1, 1, 4, 7]
def baseStart_60665 : Nat := 118140960795 + 60665 * 2 ^ 59
def prefixEnd_60665 : Nat := 4983230072969 + 3 ^ 40 * 60665 * 2
def baseEnd_60665 : Nat := 9229719675588261217337

theorem tailTrace_60665 : CollatzResearch.WordTrace tailWord_60665 prefixEnd_60665 9229719675588261217337 := by
  unfold tailWord_60665
  simp only [CollatzResearch.WordTrace]
  refine ⟨2212634325228540602247449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1475089550152360401498299 2212634325228540602247449)
  ·
    refine ⟨1659475743921405451685587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2212634325228540602247449 1659475743921405451685587)
    ·
      refine ⟨2489213615882108177528381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1659475743921405451685587 2489213615882108177528381)
      ·
        refine ⟨933455105955790566573143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2489213615882108177528381 933455105955790566573143)
        ·
          refine ⟨1400182658933685849859715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 933455105955790566573143 1400182658933685849859715)
          ·
            refine ⟨2100273988400528774789573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1400182658933685849859715 2100273988400528774789573)
            ·
              refine ⟨393801372825099145273045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2100273988400528774789573 393801372825099145273045)
              ·
                refine ⟨9229719675588261217337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 393801372825099145273045 9229719675588261217337)
                ·
                  rfl

theorem cell20_60665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_60665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60665 prefixEnd_60665 := by exact prefixLift 60665
  have htrace : WordTrace (prefixWord ++ tailWord_60665) baseStart_60665 baseEnd_60665 := by
    simpa [prefixWord, tailWord_60665, baseEnd_60665] using wordTrace_append hprefix tailTrace_60665
  have hstable : (prefixWord ++ tailWord_60665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60665).length < 2 ^ (prefixWord ++ tailWord_60665).sum := by decide
  have hdescent : baseEnd_60665 < baseStart_60665 := by decide
  rcases family_descends (prefixWord ++ tailWord_60665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60709 : List Nat := [1, 3, 1, 2, 4, 2, 3, 2, 2]
def baseStart_60709 : Nat := 118140960795 + 60709 * 2 ^ 59
def prefixEnd_60709 : Nat := 4983230072969 + 3 ^ 40 * 60709 * 2
def baseEnd_60709 : Nat := 27709241825696186185165

theorem tailTrace_60709 : CollatzResearch.WordTrace tailWord_60709 prefixEnd_60709 27709241825696186185165 := by
  unfold tailWord_60709
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214239137069136116849181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1476159424712757411232787 2214239137069136116849181)
  ·
    refine ⟨830339676400926043818443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2214239137069136116849181 830339676400926043818443)
    ·
      refine ⟨1245509514601389065727665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 830339676400926043818443 1245509514601389065727665)
      ·
        refine ⟨934132135951041799295749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1245509514601389065727665 934132135951041799295749)
        ·
          refine ⟨175149775490820337367953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 934132135951041799295749 175149775490820337367953)
          ·
            refine ⟨131362331618115253025965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175149775490820337367953 131362331618115253025965)
            ·
              refine ⟨49260874356793219884737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 131362331618115253025965 49260874356793219884737)
              ·
                refine ⟨36945655767594914913553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49260874356793219884737 36945655767594914913553)
                ·
                  refine ⟨27709241825696186185165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36945655767594914913553 27709241825696186185165)
                  ·
                    rfl

theorem cell20_60709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_60709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60709 prefixEnd_60709 := by exact prefixLift 60709
  have htrace : WordTrace (prefixWord ++ tailWord_60709) baseStart_60709 baseEnd_60709 := by
    simpa [prefixWord, tailWord_60709, baseEnd_60709] using wordTrace_append hprefix tailTrace_60709
  have hstable : (prefixWord ++ tailWord_60709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60709).length < 2 ^ (prefixWord ++ tailWord_60709).sum := by decide
  have hdescent : baseEnd_60709 < baseStart_60709 := by decide
  rcases family_descends (prefixWord ++ tailWord_60709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60723 : List Nat := [1, 1, 1, 2, 5, 4, 2, 1, 3]
def baseStart_60723 : Nat := 118140960795 + 60723 * 2 ^ 59
def prefixEnd_60723 : Nat := 4983230072969 + 3 ^ 40 * 60723 * 2
def baseEnd_60723 : Nat := 27715631807174359718441

theorem tailTrace_60723 : CollatzResearch.WordTrace tailWord_60723 prefixEnd_60723 27715631807174359718441 := by
  unfold tailWord_60723
  simp only [CollatzResearch.WordTrace]
  refine ⟨2214749759018416507858823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1476499839345611005239215 2214749759018416507858823)
  ·
    refine ⟨3322124638527624761788235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2214749759018416507858823 3322124638527624761788235)
    ·
      refine ⟨4983186957791437142682353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3322124638527624761788235 4983186957791437142682353)
      ·
        refine ⟨3737390218343577857011765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4983186957791437142682353 3737390218343577857011765)
        ·
          refine ⟨350380332969710424094853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3737390218343577857011765 350380332969710424094853)
          ·
            refine ⟨65696312431820704517785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 350380332969710424094853 65696312431820704517785)
            ·
              refine ⟨49272234323865528388339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65696312431820704517785 49272234323865528388339)
              ·
                refine ⟨73908351485798292582509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49272234323865528388339 73908351485798292582509)
                ·
                  refine ⟨27715631807174359718441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73908351485798292582509 27715631807174359718441)
                  ·
                    rfl

theorem cell20_60723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 2, 1, 3].length) (baseStart_60723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60723 prefixEnd_60723 := by exact prefixLift 60723
  have htrace : WordTrace (prefixWord ++ tailWord_60723) baseStart_60723 baseEnd_60723 := by
    simpa [prefixWord, tailWord_60723, baseEnd_60723] using wordTrace_append hprefix tailTrace_60723
  have hstable : (prefixWord ++ tailWord_60723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60723).length < 2 ^ (prefixWord ++ tailWord_60723).sum := by decide
  have hdescent : baseEnd_60723 < baseStart_60723 := by decide
  rcases family_descends (prefixWord ++ tailWord_60723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60768 : List Nat := [2, 1, 1, 3, 4, 2, 1, 4, 2]
def baseStart_60768 : Nat := 118140960795 + 60768 * 2 ^ 59
def prefixEnd_60768 : Nat := 4983230072969 + 3 ^ 40 * 60768 * 2
def baseEnd_60768 : Nat := 27736171033354203218257

theorem tailTrace_60768 : CollatzResearch.WordTrace tailWord_60768 prefixEnd_60768 27736171033354203218257 := by
  unfold tailWord_60768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1108195521927694596623479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1477594029236926128831305 1108195521927694596623479)
  ·
    refine ⟨1662293282891541894935219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1108195521927694596623479 1662293282891541894935219)
    ·
      refine ⟨2493439924337312842402829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1662293282891541894935219 2493439924337312842402829)
      ·
        refine ⟨935039971626492315901061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2493439924337312842402829 935039971626492315901061)
        ·
          refine ⟨175319994679967309231449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 935039971626492315901061 175319994679967309231449)
          ·
            refine ⟨131489996009975481923587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175319994679967309231449 131489996009975481923587)
            ·
              refine ⟨197234994014963222885381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131489996009975481923587 197234994014963222885381)
              ·
                refine ⟨36981561377805604291009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197234994014963222885381 36981561377805604291009)
                ·
                  refine ⟨27736171033354203218257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36981561377805604291009 27736171033354203218257)
                  ·
                    rfl

theorem cell20_60768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4, 2].length) (baseStart_60768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60768 prefixEnd_60768 := by exact prefixLift 60768
  have htrace : WordTrace (prefixWord ++ tailWord_60768) baseStart_60768 baseEnd_60768 := by
    simpa [prefixWord, tailWord_60768, baseEnd_60768] using wordTrace_append hprefix tailTrace_60768
  have hstable : (prefixWord ++ tailWord_60768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60768).length < 2 ^ (prefixWord ++ tailWord_60768).sum := by decide
  have hdescent : baseEnd_60768 < baseStart_60768 := by decide
  rcases family_descends (prefixWord ++ tailWord_60768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60775 : List Nat := [1, 1, 5, 1, 4, 2, 1, 5]
def baseStart_60775 : Nat := 118140960795 + 60775 * 2 ^ 59
def prefixEnd_60775 : Nat := 4983230072969 + 3 ^ 40 * 60775 * 2
def baseEnd_60775 : Nat := 9246455341364429994965

theorem tailTrace_60775 : CollatzResearch.WordTrace tailWord_60775 prefixEnd_60775 9246455341364429994965 := by
  unfold tailWord_60775
  simp only [CollatzResearch.WordTrace]
  refine ⟨2216646354830029388751779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1477764236553352925834519 2216646354830029388751779)
  ·
    refine ⟨3324969532245044083127669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2216646354830029388751779 3324969532245044083127669)
    ·
      refine ⟨311715893647972882793219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3324969532245044083127669 311715893647972882793219)
      ·
        refine ⟨467573840471959324189829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311715893647972882793219 467573840471959324189829)
        ·
          refine ⟨87670095088492373285593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 467573840471959324189829 87670095088492373285593)
          ·
            refine ⟨65752571316369279964195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87670095088492373285593 65752571316369279964195)
            ·
              refine ⟨98628856974553919946293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65752571316369279964195 98628856974553919946293)
              ·
                refine ⟨9246455341364429994965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 98628856974553919946293 9246455341364429994965)
                ·
                  rfl

theorem cell20_60775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 5].length) (baseStart_60775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60775 prefixEnd_60775 := by exact prefixLift 60775
  have htrace : WordTrace (prefixWord ++ tailWord_60775) baseStart_60775 baseEnd_60775 := by
    simpa [prefixWord, tailWord_60775, baseEnd_60775] using wordTrace_append hprefix tailTrace_60775
  have hstable : (prefixWord ++ tailWord_60775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60775).length < 2 ^ (prefixWord ++ tailWord_60775).sum := by decide
  have hdescent : baseEnd_60775 < baseStart_60775 := by decide
  rcases family_descends (prefixWord ++ tailWord_60775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60796 : List Nat := [2, 2, 2, 1, 1, 1, 7, 4]
def baseStart_60796 : Nat := 118140960795 + 60796 * 2 ^ 59
def prefixEnd_60796 : Nat := 4983230072969 + 3 ^ 40 * 60796 * 2
def baseEnd_60796 : Nat := 9249650332103516761603

theorem tailTrace_60796 : CollatzResearch.WordTrace tailWord_60796 prefixEnd_60796 9249650332103516761603 := by
  unfold tailWord_60796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1108706143876974987633121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1478274858502633316844161 1108706143876974987633121)
  ·
    refine ⟨831529607907731240724841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1108706143876974987633121 831529607907731240724841)
    ·
      refine ⟨623647205930798430543631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 831529607907731240724841 623647205930798430543631)
      ·
        refine ⟨935470808896197645815447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 623647205930798430543631 935470808896197645815447)
        ·
          refine ⟨1403206213344296468723171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 935470808896197645815447 1403206213344296468723171)
          ·
            refine ⟨2104809320016444703084757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1403206213344296468723171 2104809320016444703084757)
            ·
              refine ⟨49331468437885422728549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2104809320016444703084757 49331468437885422728549)
              ·
                refine ⟨9249650332103516761603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49331468437885422728549 9249650332103516761603)
                ·
                  rfl

theorem cell20_60796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_60796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60796 prefixEnd_60796 := by exact prefixLift 60796
  have htrace : WordTrace (prefixWord ++ tailWord_60796) baseStart_60796 baseEnd_60796 := by
    simpa [prefixWord, tailWord_60796, baseEnd_60796] using wordTrace_append hprefix tailTrace_60796
  have hstable : (prefixWord ++ tailWord_60796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60796).length < 2 ^ (prefixWord ++ tailWord_60796).sum := by decide
  have hdescent : baseEnd_60796 < baseStart_60796 := by decide
  rcases family_descends (prefixWord ++ tailWord_60796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60802 : List Nat := [3, 4, 2, 1, 1, 2, 2, 3, 2]
def baseStart_60802 : Nat := 118140960795 + 60802 * 2 ^ 59
def prefixEnd_60802 : Nat := 4983230072969 + 3 ^ 40 * 60802 * 2
def baseEnd_60802 : Nat := 27751689559801196084785

theorem tailTrace_60802 : CollatzResearch.WordTrace tailWord_60802 prefixEnd_60802 27751689559801196084785 := by
  unfold tailWord_60802
  simp only [CollatzResearch.WordTrace]
  refine ⟨554407781433053249996165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1478420750488141999989773 554407781433053249996165)
  ·
    refine ⟨103951459018697484374281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 554407781433053249996165 103951459018697484374281)
    ·
      refine ⟨77963594264023113280711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103951459018697484374281 77963594264023113280711)
      ·
        refine ⟨116945391396034669921067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77963594264023113280711 116945391396034669921067)
        ·
          refine ⟨175418087094052004881601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116945391396034669921067 175418087094052004881601)
          ·
            refine ⟨131563565320539003661201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175418087094052004881601 131563565320539003661201)
            ·
              refine ⟨98672673990404252745901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131563565320539003661201 98672673990404252745901)
              ·
                refine ⟨37002252746401594779713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98672673990404252745901 37002252746401594779713)
                ·
                  refine ⟨27751689559801196084785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37002252746401594779713 27751689559801196084785)
                  ·
                    rfl

theorem cell20_60802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_60802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60802 prefixEnd_60802 := by exact prefixLift 60802
  have htrace : WordTrace (prefixWord ++ tailWord_60802) baseStart_60802 baseEnd_60802 := by
    simpa [prefixWord, tailWord_60802, baseEnd_60802] using wordTrace_append hprefix tailTrace_60802
  have hstable : (prefixWord ++ tailWord_60802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60802).length < 2 ^ (prefixWord ++ tailWord_60802).sum := by decide
  have hdescent : baseEnd_60802 < baseStart_60802 := by decide
  rcases family_descends (prefixWord ++ tailWord_60802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60820 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 5]
def baseStart_60820 : Nat := 118140960795 + 60820 * 2 ^ 59
def prefixEnd_60820 : Nat := 4983230072969 + 3 ^ 40 * 60820 * 2
def baseEnd_60820 : Nat := 27759905250273133484711

theorem tailTrace_60820 : CollatzResearch.WordTrace tailWord_60820 prefixEnd_60820 27759905250273133484711 := by
  unfold tailWord_60820
  simp only [CollatzResearch.WordTrace]
  refine ⟨1109143819833501037069957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1478858426444668049426609 1109143819833501037069957)
  ·
    refine ⟨207964466218781444450617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1109143819833501037069957 207964466218781444450617)
    ·
      refine ⟨155973349664086083337963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 207964466218781444450617 155973349664086083337963)
      ·
        refine ⟨233960024496129125006945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155973349664086083337963 233960024496129125006945)
        ·
          refine ⟨175470018372096843755209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 233960024496129125006945 175470018372096843755209)
          ·
            refine ⟨131602513779072632816407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 175470018372096843755209 131602513779072632816407)
            ·
              refine ⟨197403770668608949224611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 131602513779072632816407 197403770668608949224611)
              ·
                refine ⟨296105656002913423836917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197403770668608949224611 296105656002913423836917)
                ·
                  refine ⟨27759905250273133484711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 296105656002913423836917 27759905250273133484711)
                  ·
                    rfl

theorem cell20_60820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_60820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60820 prefixEnd_60820 := by exact prefixLift 60820
  have htrace : WordTrace (prefixWord ++ tailWord_60820) baseStart_60820 baseEnd_60820 := by
    simpa [prefixWord, tailWord_60820, baseEnd_60820] using wordTrace_append hprefix tailTrace_60820
  have hstable : (prefixWord ++ tailWord_60820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60820).length < 2 ^ (prefixWord ++ tailWord_60820).sum := by decide
  have hdescent : baseEnd_60820 < baseStart_60820 := by decide
  rcases family_descends (prefixWord ++ tailWord_60820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60855 : List Nat := [1, 1, 3, 1, 3, 2, 3, 6]
def baseStart_60855 : Nat := 118140960795 + 60855 * 2 ^ 59
def prefixEnd_60855 : Nat := 4983230072969 + 3 ^ 40 * 60855 * 2
def baseEnd_60855 : Nat := 9258626734656189105967

theorem tailTrace_60855 : CollatzResearch.WordTrace tailWord_60855 prefixEnd_60855 9258626734656189105967 := by
  unfold tailWord_60855
  simp only [CollatzResearch.WordTrace]
  refine ⟨2219564194540203051664019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1479709463026802034442679 2219564194540203051664019)
  ·
    refine ⟨3329346291810304577496029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2219564194540203051664019 3329346291810304577496029)
    ·
      refine ⟨1248504859428864216561011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3329346291810304577496029 1248504859428864216561011)
      ·
        refine ⟨1872757289143296324841517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1248504859428864216561011 1872757289143296324841517)
        ·
          refine ⟨702283983428736121815569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1872757289143296324841517 702283983428736121815569)
          ·
            refine ⟨526712987571552091361677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 702283983428736121815569 526712987571552091361677)
            ·
              refine ⟨197517370339332034260629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 526712987571552091361677 197517370339332034260629)
              ·
                refine ⟨9258626734656189105967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 197517370339332034260629 9258626734656189105967)
                ·
                  rfl

theorem cell20_60855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 6].length) (baseStart_60855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60855 prefixEnd_60855 := by exact prefixLift 60855
  have htrace : WordTrace (prefixWord ++ tailWord_60855) baseStart_60855 baseEnd_60855 := by
    simpa [prefixWord, tailWord_60855, baseEnd_60855] using wordTrace_append hprefix tailTrace_60855
  have hstable : (prefixWord ++ tailWord_60855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60855).length < 2 ^ (prefixWord ++ tailWord_60855).sum := by decide
  have hdescent : baseEnd_60855 < baseStart_60855 := by decide
  rcases family_descends (prefixWord ++ tailWord_60855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60962 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_60962 : Nat := 118140960795 + 60962 * 2 ^ 59
def prefixEnd_60962 : Nat := 4983230072969 + 3 ^ 40 * 60962 * 2
def baseEnd_60962 : Nat := 27824717919551750750797

theorem tailTrace_60962 : CollatzResearch.WordTrace tailWord_60962 prefixEnd_60962 27824717919551750750797 := by
  unfold tailWord_60962
  simp only [CollatzResearch.WordTrace]
  refine ⟨555866701288140081452285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1482311203435040217206093 555866701288140081452285)
  ·
    refine ⟨208450012983052530544607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 555866701288140081452285 208450012983052530544607)
    ·
      refine ⟨312675019474578795816911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208450012983052530544607 312675019474578795816911)
      ·
        refine ⟨469012529211868193725367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 312675019474578795816911 469012529211868193725367)
        ·
          refine ⟨703518793817802290588051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 469012529211868193725367 703518793817802290588051)
          ·
            refine ⟨1055278190726703435882077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 703518793817802290588051 1055278190726703435882077)
            ·
              refine ⟨395729321522513788455779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1055278190726703435882077 395729321522513788455779)
              ·
                refine ⟨593593982283770682683669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 395729321522513788455779 593593982283770682683669)
                ·
                  refine ⟨27824717919551750750797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 593593982283770682683669 27824717919551750750797)
                  ·
                    rfl

theorem cell20_60962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_60962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60962 prefixEnd_60962 := by exact prefixLift 60962
  have htrace : WordTrace (prefixWord ++ tailWord_60962) baseStart_60962 baseEnd_60962 := by
    simpa [prefixWord, tailWord_60962, baseEnd_60962] using wordTrace_append hprefix tailTrace_60962
  have hstable : (prefixWord ++ tailWord_60962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60962).length < 2 ^ (prefixWord ++ tailWord_60962).sum := by decide
  have hdescent : baseEnd_60962 < baseStart_60962 := by decide
  rcases family_descends (prefixWord ++ tailWord_60962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60976 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_60976 : Nat := 118140960795 + 60976 * 2 ^ 59
def prefixEnd_60976 : Nat := 4983230072969 + 3 ^ 40 * 60976 * 2
def baseEnd_60976 : Nat := 27831107901029924284073

theorem tailTrace_60976 : CollatzResearch.WordTrace tailWord_60976 prefixEnd_60976 27831107901029924284073 := by
  unfold tailWord_60976
  simp only [CollatzResearch.WordTrace]
  refine ⟨1111988713550920358409391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1482651618067893811212521 1111988713550920358409391)
  ·
    refine ⟨1667983070326380537614087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1111988713550920358409391 1667983070326380537614087)
    ·
      refine ⟨2501974605489570806421131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1667983070326380537614087 2501974605489570806421131)
      ·
        refine ⟨3752961908234356209631697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2501974605489570806421131 3752961908234356209631697)
        ·
          refine ⟨2814721431175767157223773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3752961908234356209631697 2814721431175767157223773)
          ·
            refine ⟨1055520536690912683958915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2814721431175767157223773 1055520536690912683958915)
            ·
              refine ⟨1583280805036369025938373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1055520536690912683958915 1583280805036369025938373)
              ·
                refine ⟨296865150944319192363445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1583280805036369025938373 296865150944319192363445)
                ·
                  refine ⟨27831107901029924284073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 296865150944319192363445 27831107901029924284073)
                  ·
                    rfl

theorem cell20_60976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_60976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60976 prefixEnd_60976 := by exact prefixLift 60976
  have htrace : WordTrace (prefixWord ++ tailWord_60976) baseStart_60976 baseEnd_60976 := by
    simpa [prefixWord, tailWord_60976, baseEnd_60976] using wordTrace_append hprefix tailTrace_60976
  have hstable : (prefixWord ++ tailWord_60976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60976).length < 2 ^ (prefixWord ++ tailWord_60976).sum := by decide
  have hdescent : baseEnd_60976 < baseStart_60976 := by decide
  rcases family_descends (prefixWord ++ tailWord_60976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60979 : List Nat := [1, 1, 1, 2, 4, 3, 1, 5, 2]
def baseStart_60979 : Nat := 118140960795 + 60979 * 2 ^ 59
def prefixEnd_60979 : Nat := 4983230072969 + 3 ^ 40 * 60979 * 2
def baseEnd_60979 : Nat := 27832477182775247184061

theorem tailTrace_60979 : CollatzResearch.WordTrace tailWord_60979 prefixEnd_60979 27832477182775247184061 := by
  unfold tailWord_60979
  simp only [CollatzResearch.WordTrace]
  refine ⟨2224086846090972229177991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1482724564060648152785327 2224086846090972229177991)
  ·
    refine ⟨3336130269136458343766987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2224086846090972229177991 3336130269136458343766987)
    ·
      refine ⟨5004195403704687515650481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3336130269136458343766987 5004195403704687515650481)
      ·
        refine ⟨3753146552778515636737861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5004195403704687515650481 3753146552778515636737861)
        ·
          refine ⟨703714978645971681888349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3753146552778515636737861 703714978645971681888349)
          ·
            refine ⟨263893116992239380708131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 703714978645971681888349 263893116992239380708131)
            ·
              refine ⟨395839675488359071062197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263893116992239380708131 395839675488359071062197)
              ·
                refine ⟨37109969577033662912081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 395839675488359071062197 37109969577033662912081)
                ·
                  refine ⟨27832477182775247184061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37109969577033662912081 27832477182775247184061)
                  ·
                    rfl

theorem cell20_60979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 2].length) (baseStart_60979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60979 prefixEnd_60979 := by exact prefixLift 60979
  have htrace : WordTrace (prefixWord ++ tailWord_60979) baseStart_60979 baseEnd_60979 := by
    simpa [prefixWord, tailWord_60979, baseEnd_60979] using wordTrace_append hprefix tailTrace_60979
  have hstable : (prefixWord ++ tailWord_60979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60979).length < 2 ^ (prefixWord ++ tailWord_60979).sum := by decide
  have hdescent : baseEnd_60979 < baseStart_60979 := by decide
  rcases family_descends (prefixWord ++ tailWord_60979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60989 : List Nat := [1, 4, 1, 3, 3, 2, 1, 2, 3]
def baseStart_60989 : Nat := 118140960795 + 60989 * 2 ^ 59
def prefixEnd_60989 : Nat := 4983230072969 + 3 ^ 40 * 60989 * 2
def baseEnd_60989 : Nat := 27837041455259656850687

theorem tailTrace_60989 : CollatzResearch.WordTrace tailWord_60989 prefixEnd_60989 27837041455259656850687 := by
  unfold tailWord_60989
  simp only [CollatzResearch.WordTrace]
  refine ⟨2224451576054743937042021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1482967717369829291361347 2224451576054743937042021)
  ·
    refine ⟨417084670510264488195379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2224451576054743937042021 417084670510264488195379)
    ·
      refine ⟨625627005765396732293069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 417084670510264488195379 625627005765396732293069)
      ·
        refine ⟨234610127162023774609901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 625627005765396732293069 234610127162023774609901)
        ·
          refine ⟨87978797685758915478713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 234610127162023774609901 87978797685758915478713)
          ·
            refine ⟨65984098264319186609035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 87978797685758915478713 65984098264319186609035)
            ·
              refine ⟨98976147396478779913553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65984098264319186609035 98976147396478779913553)
              ·
                refine ⟨74232110547359084935165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 98976147396478779913553 74232110547359084935165)
                ·
                  refine ⟨27837041455259656850687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74232110547359084935165 27837041455259656850687)
                  ·
                    rfl

theorem cell20_60989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_60989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60989 prefixEnd_60989 := by exact prefixLift 60989
  have htrace : WordTrace (prefixWord ++ tailWord_60989) baseStart_60989 baseEnd_60989 := by
    simpa [prefixWord, tailWord_60989, baseEnd_60989] using wordTrace_append hprefix tailTrace_60989
  have hstable : (prefixWord ++ tailWord_60989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60989).length < 2 ^ (prefixWord ++ tailWord_60989).sum := by decide
  have hdescent : baseEnd_60989 < baseStart_60989 := by decide
  rcases family_descends (prefixWord ++ tailWord_60989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_60993 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 5]
def baseStart_60993 : Nat := 118140960795 + 60993 * 2 ^ 59
def prefixEnd_60993 : Nat := 4983230072969 + 3 ^ 40 * 60993 * 2
def baseEnd_60993 : Nat := 27838867164253420717337

theorem tailTrace_60993 : CollatzResearch.WordTrace tailWord_60993 prefixEnd_60993 27838867164253420717337 := by
  unfold tailWord_60993
  simp only [CollatzResearch.WordTrace]
  refine ⟨2224597468040252620187633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1483064978693501746791755 2224597468040252620187633)
  ·
    refine ⟨1668448101030189465140725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2224597468040252620187633 1668448101030189465140725)
    ·
      refine ⟨156417009471580262356943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1668448101030189465140725 156417009471580262356943)
      ·
        refine ⟨234625514207370393535415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156417009471580262356943 234625514207370393535415)
        ·
          refine ⟨351938271311055590303123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234625514207370393535415 351938271311055590303123)
          ·
            refine ⟨527907406966583385454685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 351938271311055590303123 527907406966583385454685)
            ·
              refine ⟨197965277612468769545507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 527907406966583385454685 197965277612468769545507)
              ·
                refine ⟨296947916418703154318261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 197965277612468769545507 296947916418703154318261)
                ·
                  refine ⟨27838867164253420717337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 296947916418703154318261 27838867164253420717337)
                  ·
                    rfl

theorem cell20_60993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_60993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_60993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_60993 prefixEnd_60993 := by exact prefixLift 60993
  have htrace : WordTrace (prefixWord ++ tailWord_60993) baseStart_60993 baseEnd_60993 := by
    simpa [prefixWord, tailWord_60993, baseEnd_60993] using wordTrace_append hprefix tailTrace_60993
  have hstable : (prefixWord ++ tailWord_60993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_60993).length < 2 ^ (prefixWord ++ tailWord_60993).sum := by decide
  have hdescent : baseEnd_60993 < baseStart_60993 := by decide
  rcases family_descends (prefixWord ++ tailWord_60993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61034 : List Nat := [3, 1, 3, 2, 1, 2, 3, 3, 2]
def baseStart_61034 : Nat := 118140960795 + 61034 * 2 ^ 59
def prefixEnd_61034 : Nat := 4983230072969 + 3 ^ 40 * 61034 * 2
def baseEnd_61034 : Nat := 27857580681439500350503

theorem tailTrace_61034 : CollatzResearch.WordTrace tailWord_61034 prefixEnd_61034 27857580681439500350503 := by
  unfold tailWord_61034
  simp only [CollatzResearch.WordTrace]
  refine ⟨556523215222929155607539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1484061907261144414953437 556523215222929155607539)
  ·
    refine ⟨834784822834393733411309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 556523215222929155607539 834784822834393733411309)
    ·
      refine ⟨313044308562897650029241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 834784822834393733411309 313044308562897650029241)
      ·
        refine ⟨234783231422173237521931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313044308562897650029241 234783231422173237521931)
        ·
          refine ⟨352174847133259856282897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234783231422173237521931 352174847133259856282897)
          ·
            refine ⟨264131135349944892212173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352174847133259856282897 264131135349944892212173)
            ·
              refine ⟨99049175756229334579565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264131135349944892212173 99049175756229334579565)
              ·
                refine ⟨37143440908586000467337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99049175756229334579565 37143440908586000467337)
                ·
                  refine ⟨27857580681439500350503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37143440908586000467337 27857580681439500350503)
                  ·
                    rfl

theorem cell20_61034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_61034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61034 prefixEnd_61034 := by exact prefixLift 61034
  have htrace : WordTrace (prefixWord ++ tailWord_61034) baseStart_61034 baseEnd_61034 := by
    simpa [prefixWord, tailWord_61034, baseEnd_61034] using wordTrace_append hprefix tailTrace_61034
  have hstable : (prefixWord ++ tailWord_61034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61034).length < 2 ^ (prefixWord ++ tailWord_61034).sum := by decide
  have hdescent : baseEnd_61034 < baseStart_61034 := by decide
  rcases family_descends (prefixWord ++ tailWord_61034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61096 : List Nat := [2, 1, 7, 1, 2, 7]
def baseStart_61096 : Nat := 118140960795 + 61096 * 2 ^ 59
def prefixEnd_61096 : Nat := 4983230072969 + 3 ^ 40 * 61096 * 2
def baseEnd_61096 : Nat := 1032810339660845936429

theorem tailTrace_61096 : CollatzResearch.WordTrace tailWord_61096 prefixEnd_61096 1032810339660845936429 := by
  unfold tailWord_61096
  simp only [CollatzResearch.WordTrace]
  refine ⟨1114177093333550605593571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1485569457778067474124761 1114177093333550605593571)
  ·
    refine ⟨1671265640000325908390357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1114177093333550605593571 1671265640000325908390357)
    ·
      refine ⟨39170288437507638477899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 1671265640000325908390357 39170288437507638477899)
      ·
        refine ⟨58755432656261457716849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39170288437507638477899 58755432656261457716849)
        ·
          refine ⟨44066574492196093287637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58755432656261457716849 44066574492196093287637)
          ·
            refine ⟨1032810339660845936429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 44066574492196093287637 1032810339660845936429)
            ·
              rfl

theorem cell20_61096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 7].length) (baseStart_61096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61096 prefixEnd_61096 := by exact prefixLift 61096
  have htrace : WordTrace (prefixWord ++ tailWord_61096) baseStart_61096 baseEnd_61096 := by
    simpa [prefixWord, tailWord_61096, baseEnd_61096] using wordTrace_append hprefix tailTrace_61096
  have hstable : (prefixWord ++ tailWord_61096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61096).length < 2 ^ (prefixWord ++ tailWord_61096).sum := by decide
  have hdescent : baseEnd_61096 < baseStart_61096 := by decide
  rcases family_descends (prefixWord ++ tailWord_61096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61107 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 3]
def baseStart_61107 : Nat := 118140960795 + 61107 * 2 ^ 59
def prefixEnd_61107 : Nat := 4983230072969 + 3 ^ 40 * 61107 * 2
def baseEnd_61107 : Nat := 27890899870575690916871

theorem tailTrace_61107 : CollatzResearch.WordTrace tailWord_61107 prefixEnd_61107 27890899870575690916871 := by
  unfold tailWord_61107
  simp only [CollatzResearch.WordTrace]
  refine ⟨2228755389627250089837575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1485836926418166726558383 2228755389627250089837575)
  ·
    refine ⟨3343133084440875134756363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2228755389627250089837575 3343133084440875134756363)
    ·
      refine ⟨5014699626661312702134545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3343133084440875134756363 5014699626661312702134545)
      ·
        refine ⟨3761024719995984526600909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5014699626661312702134545 3761024719995984526600909)
        ·
          refine ⟨1410384269998494197475341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3761024719995984526600909 1410384269998494197475341)
          ·
            refine ⟨528894101249435324053253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1410384269998494197475341 528894101249435324053253)
            ·
              refine ⟨99167643984269123259985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 528894101249435324053253 99167643984269123259985)
              ·
                refine ⟨74375732988201842444989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99167643984269123259985 74375732988201842444989)
                ·
                  refine ⟨27890899870575690916871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74375732988201842444989 27890899870575690916871)
                  ·
                    rfl

theorem cell20_61107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 3].length) (baseStart_61107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61107 prefixEnd_61107 := by exact prefixLift 61107
  have htrace : WordTrace (prefixWord ++ tailWord_61107) baseStart_61107 baseEnd_61107 := by
    simpa [prefixWord, tailWord_61107, baseEnd_61107] using wordTrace_append hprefix tailTrace_61107
  have hstable : (prefixWord ++ tailWord_61107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61107).length < 2 ^ (prefixWord ++ tailWord_61107).sum := by decide
  have hdescent : baseEnd_61107 < baseStart_61107 := by decide
  rcases family_descends (prefixWord ++ tailWord_61107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61169 : List Nat := [1, 2, 2, 2, 2, 3, 2, 4, 2]
def baseStart_61169 : Nat := 118140960795 + 61169 * 2 ^ 59
def prefixEnd_61169 : Nat := 4983230072969 + 3 ^ 40 * 61169 * 2
def baseEnd_61169 : Nat := 27919198359979030849951

theorem tailTrace_61169 : CollatzResearch.WordTrace tailWord_61169 prefixEnd_61169 27919198359979030849951 := by
  unfold tailWord_61169
  simp only [CollatzResearch.WordTrace]
  refine ⟨2231016715402634678594561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1487344476935089785729707 2231016715402634678594561)
  ·
    refine ⟨1673262536551976008945921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2231016715402634678594561 1673262536551976008945921)
    ·
      refine ⟨1254946902413982006709441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1673262536551976008945921 1254946902413982006709441)
      ·
        refine ⟨941210176810486505032081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1254946902413982006709441 941210176810486505032081)
        ·
          refine ⟨705907632607864878774061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 941210176810486505032081 705907632607864878774061)
          ·
            refine ⟨264715362227949329540273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705907632607864878774061 264715362227949329540273)
            ·
              refine ⟨198536521670961997155205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 264715362227949329540273 198536521670961997155205)
              ·
                refine ⟨37225597813305374466601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 198536521670961997155205 37225597813305374466601)
                ·
                  refine ⟨27919198359979030849951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37225597813305374466601 27919198359979030849951)
                  ·
                    rfl

theorem cell20_61169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 2].length) (baseStart_61169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61169 prefixEnd_61169 := by exact prefixLift 61169
  have htrace : WordTrace (prefixWord ++ tailWord_61169) baseStart_61169 baseEnd_61169 := by
    simpa [prefixWord, tailWord_61169, baseEnd_61169] using wordTrace_append hprefix tailTrace_61169
  have hstable : (prefixWord ++ tailWord_61169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61169).length < 2 ^ (prefixWord ++ tailWord_61169).sum := by decide
  have hdescent : baseEnd_61169 < baseStart_61169 := by decide
  rcases family_descends (prefixWord ++ tailWord_61169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61228 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_61228 : Nat := 118140960795 + 61228 * 2 ^ 59
def prefixEnd_61228 : Nat := 4983230072969 + 3 ^ 40 * 61228 * 2
def baseEnd_61228 : Nat := 27946127567637047883043

theorem tailTrace_61228 : CollatzResearch.WordTrace tailWord_61228 prefixEnd_61228 27946127567637047883043 := by
  unfold tailWord_61228
  simp only [CollatzResearch.WordTrace]
  refine ⟨1116584311094443877496169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1488779081459258503328225 1116584311094443877496169)
  ·
    refine ⟨837438233320832908122127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1116584311094443877496169 837438233320832908122127)
    ·
      refine ⟨1256157349981249362183191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 837438233320832908122127 1256157349981249362183191)
      ·
        refine ⟨1884236024971874043274787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1256157349981249362183191 1884236024971874043274787)
        ·
          refine ⟨2826354037457811064912181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1884236024971874043274787 2826354037457811064912181)
          ·
            refine ⟨264970691011669787335517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2826354037457811064912181 264970691011669787335517)
            ·
              refine ⟨99364009129376170250819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264970691011669787335517 99364009129376170250819)
              ·
                refine ⟨149046013694064255376229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99364009129376170250819 149046013694064255376229)
                ·
                  refine ⟨27946127567637047883043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149046013694064255376229 27946127567637047883043)
                  ·
                    rfl

theorem cell20_61228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_61228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61228 prefixEnd_61228 := by exact prefixLift 61228
  have htrace : WordTrace (prefixWord ++ tailWord_61228) baseStart_61228 baseEnd_61228 := by
    simpa [prefixWord, tailWord_61228, baseEnd_61228] using wordTrace_append hprefix tailTrace_61228
  have hstable : (prefixWord ++ tailWord_61228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61228).length < 2 ^ (prefixWord ++ tailWord_61228).sum := by decide
  have hdescent : baseEnd_61228 < baseStart_61228 := by decide
  rcases family_descends (prefixWord ++ tailWord_61228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61321 : List Nat := [1, 2, 1, 1, 5, 1, 4, 3, 2]
def baseStart_61321 : Nat := 118140960795 + 61321 * 2 ^ 59
def prefixEnd_61321 : Nat := 4983230072969 + 3 ^ 40 * 61321 * 2
def baseEnd_61321 : Nat := 27988575301742057782663

theorem tailTrace_61321 : CollatzResearch.WordTrace tailWord_61321 prefixEnd_61321 27988575301742057782663 := by
  unfold tailWord_61321
  simp only [CollatzResearch.WordTrace]
  refine ⟨2236560610851964638127817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1491040407234643092085211 2236560610851964638127817)
  ·
    refine ⟨1677420458138973478595863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2236560610851964638127817 1677420458138973478595863)
    ·
      refine ⟨2516130687208460217893795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1677420458138973478595863 2516130687208460217893795)
      ·
        refine ⟨3774196030812690326840693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2516130687208460217893795 3774196030812690326840693)
        ·
          refine ⟨353830877888689718141315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3774196030812690326840693 353830877888689718141315)
          ·
            refine ⟨530746316833034577211973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353830877888689718141315 530746316833034577211973)
            ·
              refine ⟨99514934406193983227245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 530746316833034577211973 99514934406193983227245)
              ·
                refine ⟨37318100402322743710217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99514934406193983227245 37318100402322743710217)
                ·
                  refine ⟨27988575301742057782663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37318100402322743710217 27988575301742057782663)
                  ·
                    rfl

theorem cell20_61321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 2].length) (baseStart_61321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61321 prefixEnd_61321 := by exact prefixLift 61321
  have htrace : WordTrace (prefixWord ++ tailWord_61321) baseStart_61321 baseEnd_61321 := by
    simpa [prefixWord, tailWord_61321, baseEnd_61321] using wordTrace_append hprefix tailTrace_61321
  have hstable : (prefixWord ++ tailWord_61321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61321).length < 2 ^ (prefixWord ++ tailWord_61321).sum := by decide
  have hdescent : baseEnd_61321 < baseStart_61321 := by decide
  rcases family_descends (prefixWord ++ tailWord_61321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61335 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 3]
def baseStart_61335 : Nat := 118140960795 + 61335 * 2 ^ 59
def prefixEnd_61335 : Nat := 4983230072969 + 3 ^ 40 * 61335 * 2
def baseEnd_61335 : Nat := 27994965283220231315939

theorem tailTrace_61335 : CollatzResearch.WordTrace tailWord_61335 prefixEnd_61335 27994965283220231315939 := by
  unfold tailWord_61335
  simp only [CollatzResearch.WordTrace]
  refine ⟨2237071232801245029137459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1491380821867496686091639 2237071232801245029137459)
  ·
    refine ⟨3355606849201867543706189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2237071232801245029137459 3355606849201867543706189)
    ·
      refine ⟨1258352568450700328889821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3355606849201867543706189 1258352568450700328889821)
      ·
        refine ⟨471882213169012623333683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1258352568450700328889821 471882213169012623333683)
        ·
          refine ⟨707823319753518935000525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 471882213169012623333683 707823319753518935000525)
          ·
            refine ⟨265433744907569600625197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 707823319753518935000525 265433744907569600625197)
            ·
              refine ⟨99537654340338600234449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265433744907569600625197 99537654340338600234449)
              ·
                refine ⟨74653240755253950175837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99537654340338600234449 74653240755253950175837)
                ·
                  refine ⟨27994965283220231315939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74653240755253950175837 27994965283220231315939)
                  ·
                    rfl

theorem cell20_61335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 3].length) (baseStart_61335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61335 prefixEnd_61335 := by exact prefixLift 61335
  have htrace : WordTrace (prefixWord ++ tailWord_61335) baseStart_61335 baseEnd_61335 := by
    simpa [prefixWord, tailWord_61335, baseEnd_61335] using wordTrace_append hprefix tailTrace_61335
  have hstable : (prefixWord ++ tailWord_61335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61335).length < 2 ^ (prefixWord ++ tailWord_61335).sum := by decide
  have hdescent : baseEnd_61335 < baseStart_61335 := by decide
  rcases family_descends (prefixWord ++ tailWord_61335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61358 : List Nat := [4, 1, 5, 1, 2, 1, 2, 4]
def baseStart_61358 : Nat := 118140960795 + 61358 * 2 ^ 59
def prefixEnd_61358 : Nat := 4983230072969 + 3 ^ 40 * 61358 * 2
def baseEnd_61358 : Nat := 9335154369978124516393

theorem tailTrace_61358 : CollatzResearch.WordTrace tailWord_61358 prefixEnd_61358 9335154369978124516393 := by
  unfold tailWord_61358
  simp only [CollatzResearch.WordTrace]
  refine ⟨279738763964739994653091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1491940074478613304816485 279738763964739994653091)
  ·
    refine ⟨419608145947109991979637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279738763964739994653091 419608145947109991979637)
    ·
      refine ⟨39338263682541561748091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 419608145947109991979637 39338263682541561748091)
      ·
        refine ⟨59007395523812342622137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39338263682541561748091 59007395523812342622137)
        ·
          refine ⟨44255546642859256966603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59007395523812342622137 44255546642859256966603)
          ·
            refine ⟨66383319964288885449905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44255546642859256966603 66383319964288885449905)
            ·
              refine ⟨49787489973216664087429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66383319964288885449905 49787489973216664087429)
              ·
                refine ⟨9335154369978124516393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49787489973216664087429 9335154369978124516393)
                ·
                  rfl

theorem cell20_61358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_61358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61358 prefixEnd_61358 := by exact prefixLift 61358
  have htrace : WordTrace (prefixWord ++ tailWord_61358) baseStart_61358 baseEnd_61358 := by
    simpa [prefixWord, tailWord_61358, baseEnd_61358] using wordTrace_append hprefix tailTrace_61358
  have hstable : (prefixWord ++ tailWord_61358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61358).length < 2 ^ (prefixWord ++ tailWord_61358).sum := by decide
  have hdescent : baseEnd_61358 < baseStart_61358 := by decide
  rcases family_descends (prefixWord ++ tailWord_61358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61363 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 4]
def baseStart_61363 : Nat := 118140960795 + 61363 * 2 ^ 59
def prefixEnd_61363 : Nat := 4983230072969 + 3 ^ 40 * 61363 * 2
def baseEnd_61363 : Nat := 28007745246176578382491

theorem tailTrace_61363 : CollatzResearch.WordTrace tailWord_61363 prefixEnd_61363 28007745246176578382491 := by
  unfold tailWord_61363
  simp only [CollatzResearch.WordTrace]
  refine ⟨2238092476699805811156743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1492061651133203874104495 2238092476699805811156743)
  ·
    refine ⟨3357138715049708716735115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2238092476699805811156743 3357138715049708716735115)
    ·
      refine ⟨5035708072574563075102673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3357138715049708716735115 5035708072574563075102673)
      ·
        refine ⟨3776781054430922306327005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5035708072574563075102673 3776781054430922306327005)
        ·
          refine ⟨1416292895411595864872627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3776781054430922306327005 1416292895411595864872627)
          ·
            refine ⟨2124439343117393797308941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1416292895411595864872627 2124439343117393797308941)
            ·
              refine ⟨796664753669022673990853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2124439343117393797308941 796664753669022673990853)
              ·
                refine ⟨149374641312941751373285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 796664753669022673990853 149374641312941751373285)
                ·
                  refine ⟨28007745246176578382491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149374641312941751373285 28007745246176578382491)
                  ·
                    rfl

theorem cell20_61363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_61363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61363 prefixEnd_61363 := by exact prefixLift 61363
  have htrace : WordTrace (prefixWord ++ tailWord_61363) baseStart_61363 baseEnd_61363 := by
    simpa [prefixWord, tailWord_61363, baseEnd_61363] using wordTrace_append hprefix tailTrace_61363
  have hstable : (prefixWord ++ tailWord_61363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61363).length < 2 ^ (prefixWord ++ tailWord_61363).sum := by decide
  have hdescent : baseEnd_61363 < baseStart_61363 := by decide
  rcases family_descends (prefixWord ++ tailWord_61363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_61372 : List Nat := [2, 2, 2, 5, 2, 1, 1, 3, 2]
def baseStart_61372 : Nat := 118140960795 + 61372 * 2 ^ 59
def prefixEnd_61372 : Nat := 4983230072969 + 3 ^ 40 * 61372 * 2
def baseEnd_61372 : Nat := 28011853091412547082455

theorem tailTrace_61372 : CollatzResearch.WordTrace tailWord_61372 prefixEnd_61372 28011853091412547082455 := by
  unfold tailWord_61372
  simp only [CollatzResearch.WordTrace]
  refine ⟨1119210366833600174117185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1492280489111466898822913 1119210366833600174117185)
  ·
    refine ⟨839407775125200130587889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1119210366833600174117185 839407775125200130587889)
    ·
      refine ⟨629555831343900097940917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 839407775125200130587889 629555831343900097940917)
      ·
        refine ⟨59020859188490634181961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 629555831343900097940917 59020859188490634181961)
        ·
          refine ⟨44265644391367975636471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59020859188490634181961 44265644391367975636471)
          ·
            refine ⟨66398466587051963454707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44265644391367975636471 66398466587051963454707)
            ·
              refine ⟨99597699880577945182061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66398466587051963454707 99597699880577945182061)
              ·
                refine ⟨37349137455216729443273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99597699880577945182061 37349137455216729443273)
                ·
                  refine ⟨28011853091412547082455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37349137455216729443273 28011853091412547082455)
                  ·
                    rfl

theorem cell20_61372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_61372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_61372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_61372 prefixEnd_61372 := by exact prefixLift 61372
  have htrace : WordTrace (prefixWord ++ tailWord_61372) baseStart_61372 baseEnd_61372 := by
    simpa [prefixWord, tailWord_61372, baseEnd_61372] using wordTrace_append hprefix tailTrace_61372
  have hstable : (prefixWord ++ tailWord_61372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_61372).length < 2 ^ (prefixWord ++ tailWord_61372).sum := by decide
  have hdescent : baseEnd_61372 < baseStart_61372 := by decide
  rcases family_descends (prefixWord ++ tailWord_61372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
