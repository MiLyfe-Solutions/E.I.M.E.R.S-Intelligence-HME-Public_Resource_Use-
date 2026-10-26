import V185TrunkScan23Chunk0715

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4232921 : List Nat := [1, 2, 1, 2, 3, 5, 1, 2, 1, 3, 2]
def baseStart_4232921 : Nat := 118140960795 + 4232921 * 2 ^ 59
def prefixEnd_4232921 : Nat := 4983230072969 + 3 ^ 40 * 4232921 * 2
def baseEnd_4232921 : Nat := 2173523045510338410820657

theorem tailTrace_4232921 : CollatzResearch.WordTrace tailWord_4232921 prefixEnd_4232921 2173523045510338410820657 := by
  unfold tailWord_4232921
  simp only [CollatzResearch.WordTrace]
  refine ⟨154387312297857617196882617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102924874865238411464588411 154387312297857617196882617)
  ·
    refine ⟨115790484223393212897661963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154387312297857617196882617 115790484223393212897661963)
    ·
      refine ⟨173685726335089819346492945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115790484223393212897661963 173685726335089819346492945)
      ·
        refine ⟨130264294751317364509869709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173685726335089819346492945 130264294751317364509869709)
        ·
          refine ⟨48849110531744011691201141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130264294751317364509869709 48849110531744011691201141)
          ·
            refine ⟨4579604112351001096050107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48849110531744011691201141 4579604112351001096050107)
            ·
              refine ⟨6869406168526501644075161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4579604112351001096050107 6869406168526501644075161)
              ·
                refine ⟨5152054626394876233056371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6869406168526501644075161 5152054626394876233056371)
                ·
                  refine ⟨7728081939592314349584557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5152054626394876233056371 7728081939592314349584557)
                  ·
                    refine ⟨2898030727347117881094209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7728081939592314349584557 2898030727347117881094209)
                    ·
                      refine ⟨2173523045510338410820657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898030727347117881094209 2173523045510338410820657)
                      ·
                        rfl

theorem cell23_4232921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 3, 2].length) (baseStart_4232921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232921 prefixEnd_4232921 := by exact prefixLift 4232921
  have htrace : WordTrace (prefixWord ++ tailWord_4232921) baseStart_4232921 baseEnd_4232921 := by
    simpa [prefixWord, tailWord_4232921, baseEnd_4232921] using wordTrace_append hprefix tailTrace_4232921
  have hstable : (prefixWord ++ tailWord_4232921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232921).length < 2 ^ (prefixWord ++ tailWord_4232921).sum := by decide
  have hdescent : baseEnd_4232921 < baseStart_4232921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4232977 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 4, 5, 2]
def baseStart_4232977 : Nat := 118140960795 + 4232977 * 2 ^ 59
def prefixEnd_4232977 : Nat := 4983230072969 + 3 ^ 40 * 4232977 * 2
def baseEnd_4232977 : Nat := 2173551800426990191720399

theorem tailTrace_4232977 : CollatzResearch.WordTrace tailWord_4232977 prefixEnd_4232977 2173551800426990191720399 := by
  unfold tailWord_4232977
  simp only [CollatzResearch.WordTrace]
  refine ⟨154389354785654738760921185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102926236523769825840614123 154389354785654738760921185)
  ·
    refine ⟨115792016089241054070690889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154389354785654738760921185 115792016089241054070690889)
    ·
      refine ⟨86844012066930790553018167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115792016089241054070690889 86844012066930790553018167)
      ·
        refine ⟨130266018100396185829527251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86844012066930790553018167 130266018100396185829527251)
        ·
          refine ⟨195399027150594278744290877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130266018100396185829527251 195399027150594278744290877)
          ·
            refine ⟨73274635181472854529109079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195399027150594278744290877 73274635181472854529109079)
            ·
              refine ⟨109911952772209281793663619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73274635181472854529109079 109911952772209281793663619)
              ·
                refine ⟨164867929158313922690495429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109911952772209281793663619 164867929158313922690495429)
                ·
                  refine ⟨30912736717183860504467893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164867929158313922690495429 30912736717183860504467893)
                  ·
                    refine ⟨2898069067235986922293865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30912736717183860504467893 2898069067235986922293865)
                    ·
                      refine ⟨2173551800426990191720399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898069067235986922293865 2173551800426990191720399)
                      ·
                        rfl

theorem cell23_4232977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 5, 2].length) (baseStart_4232977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4232977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4232977 prefixEnd_4232977 := by exact prefixLift 4232977
  have htrace : WordTrace (prefixWord ++ tailWord_4232977) baseStart_4232977 baseEnd_4232977 := by
    simpa [prefixWord, tailWord_4232977, baseEnd_4232977] using wordTrace_append hprefix tailTrace_4232977
  have hstable : (prefixWord ++ tailWord_4232977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4232977).length < 2 ^ (prefixWord ++ tailWord_4232977).sum := by decide
  have hdescent : baseEnd_4232977 < baseStart_4232977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4232977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233007 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 3, 6, 2]
def baseStart_4233007 : Nat := 118140960795 + 4233007 * 2 ^ 59
def prefixEnd_4233007 : Nat := 4983230072969 + 3 ^ 40 * 4233007 * 2
def baseEnd_4233007 : Nat := 2173567204846625074345261

theorem tailTrace_4233007 : CollatzResearch.WordTrace tailWord_4233007 prefixEnd_4233007 2173567204846625074345261 := by
  unfold tailWord_4233007
  simp only [CollatzResearch.WordTrace]
  refine ⟨154390448975546053884513275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102926965983697369256342183 154390448975546053884513275)
  ·
    refine ⟨231585673463319080826769913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154390448975546053884513275 231585673463319080826769913)
    ·
      refine ⟨173689255097489310620077435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231585673463319080826769913 173689255097489310620077435)
      ·
        refine ⟨260533882646233965930116153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173689255097489310620077435 260533882646233965930116153)
        ·
          refine ⟨195400411984675474447587115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260533882646233965930116153 195400411984675474447587115)
          ·
            refine ⟨293100617977013211671380673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195400411984675474447587115 293100617977013211671380673)
            ·
              refine ⟨219825463482759908753535505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293100617977013211671380673 219825463482759908753535505)
              ·
                refine ⟨164869097612069931565151629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 219825463482759908753535505 164869097612069931565151629)
                ·
                  refine ⟨61825911604526224336931861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164869097612069931565151629 61825911604526224336931861)
                  ·
                    refine ⟨2898089606462166765793681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61825911604526224336931861 2898089606462166765793681)
                    ·
                      refine ⟨2173567204846625074345261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898089606462166765793681 2173567204846625074345261)
                      ·
                        rfl

theorem cell23_4233007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 6, 2].length) (baseStart_4233007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233007 prefixEnd_4233007 := by exact prefixLift 4233007
  have htrace : WordTrace (prefixWord ++ tailWord_4233007) baseStart_4233007 baseEnd_4233007 := by
    simpa [prefixWord, tailWord_4233007, baseEnd_4233007] using wordTrace_append hprefix tailTrace_4233007
  have hstable : (prefixWord ++ tailWord_4233007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233007).length < 2 ^ (prefixWord ++ tailWord_4233007).sum := by decide
  have hdescent : baseEnd_4233007 < baseStart_4233007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233027 : List Nat := [1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 3]
def baseStart_4233027 : Nat := 118140960795 + 4233027 * 2 ^ 59
def prefixEnd_4233027 : Nat := 4983230072969 + 3 ^ 40 * 4233027 * 2
def baseEnd_4233027 : Nat := 2173577474459714996095169

theorem tailTrace_4233027 : CollatzResearch.WordTrace tailWord_4233027 prefixEnd_4233027 2173577474459714996095169 := by
  unfold tailWord_4233027
  simp only [CollatzResearch.WordTrace]
  refine ⟨154391178435473597300241335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102927452290315731533494223 154391178435473597300241335)
  ·
    refine ⟨231586767653210395950362003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154391178435473597300241335 231586767653210395950362003)
    ·
      refine ⟨347380151479815593925543005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231586767653210395950362003 347380151479815593925543005)
      ·
        refine ⟨130267556804930847722078627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347380151479815593925543005 130267556804930847722078627)
        ·
          refine ⟨195401335207396271583117941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130267556804930847722078627 195401335207396271583117941)
          ·
            refine ⟨18318875175693400460917307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 195401335207396271583117941 18318875175693400460917307)
            ·
              refine ⟨27478312763540100691375961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18318875175693400460917307 27478312763540100691375961)
              ·
                refine ⟨20608734572655075518531971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27478312763540100691375961 20608734572655075518531971)
                ·
                  refine ⟨30913101858982613277797957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20608734572655075518531971 30913101858982613277797957)
                  ·
                    refine ⟨5796206598559239989587117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30913101858982613277797957 5796206598559239989587117)
                    ·
                      refine ⟨2173577474459714996095169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5796206598559239989587117 2173577474459714996095169)
                      ·
                        rfl

theorem cell23_4233027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_4233027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233027 prefixEnd_4233027 := by exact prefixLift 4233027
  have htrace : WordTrace (prefixWord ++ tailWord_4233027) baseStart_4233027 baseEnd_4233027 := by
    simpa [prefixWord, tailWord_4233027, baseEnd_4233027] using wordTrace_append hprefix tailTrace_4233027
  have hstable : (prefixWord ++ tailWord_4233027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233027).length < 2 ^ (prefixWord ++ tailWord_4233027).sum := by decide
  have hdescent : baseEnd_4233027 < baseStart_4233027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233044 : List Nat := [2, 4, 1, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_4233044 : Nat := 118140960795 + 4233044 * 2 ^ 59
def prefixEnd_4233044 : Nat := 4983230072969 + 3 ^ 40 * 4233044 * 2
def baseEnd_4233044 : Nat := 2173586203630841429582591

theorem tailTrace_4233044 : CollatzResearch.WordTrace tailWord_4233044 prefixEnd_4233044 2173586203630841429582591 := by
  unfold tailWord_4233044
  simp only [CollatzResearch.WordTrace]
  refine ⟨77195899238206004601805093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102927865650941339469073457 77195899238206004601805093)
  ·
    refine ⟨14474231107163625862838455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77195899238206004601805093 14474231107163625862838455)
    ·
      refine ⟨21711346660745438794257683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14474231107163625862838455 21711346660745438794257683)
      ·
        refine ⟨32567019991118158191386525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21711346660745438794257683 32567019991118158191386525)
        ·
          refine ⟨12212632496669309321769947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32567019991118158191386525 12212632496669309321769947)
          ·
            refine ⟨18318948745003963982654921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12212632496669309321769947 18318948745003963982654921)
            ·
              refine ⟨13739211558752972986991191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18318948745003963982654921 13739211558752972986991191)
              ·
                refine ⟨20608817338129459480486787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13739211558752972986991191 20608817338129459480486787)
                ·
                  refine ⟨30913226007194189220730181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20608817338129459480486787 30913226007194189220730181)
                  ·
                    refine ⟨5796229876348910478886909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30913226007194189220730181 5796229876348910478886909)
                    ·
                      refine ⟨2173586203630841429582591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5796229876348910478886909 2173586203630841429582591)
                      ·
                        rfl

theorem cell23_4233044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_4233044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233044 prefixEnd_4233044 := by exact prefixLift 4233044
  have htrace : WordTrace (prefixWord ++ tailWord_4233044) baseStart_4233044 baseEnd_4233044 := by
    simpa [prefixWord, tailWord_4233044, baseEnd_4233044] using wordTrace_append hprefix tailTrace_4233044
  have hstable : (prefixWord ++ tailWord_4233044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233044).length < 2 ^ (prefixWord ++ tailWord_4233044).sum := by decide
  have hdescent : baseEnd_4233044 < baseStart_4233044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233068 : List Nat := [2, 2, 1, 1, 4, 3, 3, 2, 1, 4]
def baseStart_4233068 : Nat := 118140960795 + 4233068 * 2 ^ 59
def prefixEnd_4233068 : Nat := 4983230072969 + 3 ^ 40 * 4233068 * 2
def baseEnd_4233068 : Nat := 724532842388849778560827

theorem tailTrace_4233068 : CollatzResearch.WordTrace tailWord_4233068 prefixEnd_4233068 724532842388849778560827 := by
  unfold tailWord_4233068
  simp only [CollatzResearch.WordTrace]
  refine ⟨77196336914162530651241929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102928449218883374201655905 77196336914162530651241929)
  ·
    refine ⟨57897252685621897988431447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77196336914162530651241929 57897252685621897988431447)
    ·
      refine ⟨86845879028432846982647171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57897252685621897988431447 86845879028432846982647171)
      ·
        refine ⟨130268818542649270473970757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86845879028432846982647171 130268818542649270473970757)
        ·
          refine ⟨24425403476746738213869517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130268818542649270473970757 24425403476746738213869517)
          ·
            refine ⟨9159526303780026830201069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24425403476746738213869517 9159526303780026830201069)
            ·
              refine ⟨3434822363917510061325401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9159526303780026830201069 3434822363917510061325401)
              ·
                refine ⟨2576116772938132545994051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3434822363917510061325401 2576116772938132545994051)
                ·
                  refine ⟨3864175159407198818991077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2576116772938132545994051 3864175159407198818991077)
                  ·
                    refine ⟨724532842388849778560827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3864175159407198818991077 724532842388849778560827)
                    ·
                      rfl

theorem cell23_4233068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_4233068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233068 prefixEnd_4233068 := by exact prefixLift 4233068
  have htrace : WordTrace (prefixWord ++ tailWord_4233068) baseStart_4233068 baseEnd_4233068 := by
    simpa [prefixWord, tailWord_4233068, baseEnd_4233068] using wordTrace_append hprefix tailTrace_4233068
  have hstable : (prefixWord ++ tailWord_4233068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233068).length < 2 ^ (prefixWord ++ tailWord_4233068).sum := by decide
  have hdescent : baseEnd_4233068 < baseStart_4233068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233111 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 1, 5]
def baseStart_4233111 : Nat := 118140960795 + 4233111 * 2 ^ 59
def prefixEnd_4233111 : Nat := 4983230072969 + 3 ^ 40 * 4233111 * 2
def baseEnd_4233111 : Nat := 724540202278230889148261

theorem tailTrace_4233111 : CollatzResearch.WordTrace tailWord_4233111 prefixEnd_4233111 724540202278230889148261 := by
  unfold tailWord_4233111
  simp only [CollatzResearch.WordTrace]
  refine ⟨154394242167169279646299187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102929494778112853097532791 154394242167169279646299187)
  ·
    refine ⟨231591363250753919469448781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154394242167169279646299187 231591363250753919469448781)
    ·
      refine ⟨86846761219032719801043293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231591363250753919469448781 86846761219032719801043293)
      ·
        refine ⟨32567535457137269925391235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86846761219032719801043293 32567535457137269925391235)
        ·
          refine ⟨48851303185705904888086853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32567535457137269925391235 48851303185705904888086853)
          ·
            refine ⟨9159619347319857166516285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48851303185705904888086853 9159619347319857166516285)
            ·
              refine ⟨3434857255244946437443607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9159619347319857166516285 3434857255244946437443607)
              ·
                refine ⟨5152285882867419656165411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3434857255244946437443607 5152285882867419656165411)
                ·
                  refine ⟨7728428824301129484248117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5152285882867419656165411 7728428824301129484248117)
                  ·
                    refine ⟨724540202278230889148261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7728428824301129484248117 724540202278230889148261)
                    ·
                      rfl

theorem cell23_4233111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 5].length) (baseStart_4233111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233111 prefixEnd_4233111 := by exact prefixLift 4233111
  have htrace : WordTrace (prefixWord ++ tailWord_4233111) baseStart_4233111 baseEnd_4233111 := by
    simpa [prefixWord, tailWord_4233111, baseEnd_4233111] using wordTrace_append hprefix tailTrace_4233111
  have hstable : (prefixWord ++ tailWord_4233111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233111).length < 2 ^ (prefixWord ++ tailWord_4233111).sum := by decide
  have hdescent : baseEnd_4233111 < baseStart_4233111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233141 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 2, 4]
def baseStart_4233141 : Nat := 118140960795 + 4233141 * 2 ^ 59
def prefixEnd_4233141 : Nat := 4983230072969 + 3 ^ 40 * 4233141 * 2
def baseEnd_4233141 : Nat := 724545337084775850023215

theorem tailTrace_4233141 : CollatzResearch.WordTrace tailWord_4233141 prefixEnd_4233141 724545337084775850023215 := by
  unfold tailWord_4233141
  simp only [CollatzResearch.WordTrace]
  refine ⟨154395336357060594769891277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102930224238040396513260851 154395336357060594769891277)
  ·
    refine ⟨57898251133897723038709229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154395336357060594769891277 57898251133897723038709229)
    ·
      refine ⟨21711844175211646139515961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57898251133897723038709229 21711844175211646139515961)
      ·
        refine ⟨16283883131408734604636971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21711844175211646139515961 16283883131408734604636971)
        ·
          refine ⟨24425824697113101906955457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16283883131408734604636971 24425824697113101906955457)
          ·
            refine ⟨18319368522834826430216593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24425824697113101906955457 18319368522834826430216593)
            ·
              refine ⟨13739526392126119822662445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18319368522834826430216593 13739526392126119822662445)
              ·
                refine ⟨5152322397047294933498417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13739526392126119822662445 5152322397047294933498417)
                ·
                  refine ⟨3864241797785471200123813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5152322397047294933498417 3864241797785471200123813)
                  ·
                    refine ⟨724545337084775850023215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3864241797785471200123813 724545337084775850023215)
                    ·
                      rfl

theorem cell23_4233141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_4233141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233141 prefixEnd_4233141 := by exact prefixLift 4233141
  have htrace : WordTrace (prefixWord ++ tailWord_4233141) baseStart_4233141 baseEnd_4233141 := by
    simpa [prefixWord, tailWord_4233141, baseEnd_4233141] using wordTrace_append hprefix tailTrace_4233141
  have hstable : (prefixWord ++ tailWord_4233141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233141).length < 2 ^ (prefixWord ++ tailWord_4233141).sum := by decide
  have hdescent : baseEnd_4233141 < baseStart_4233141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233144 : List Nat := [2, 1, 2, 1, 2, 3, 4, 1, 1, 2, 4]
def baseStart_4233144 : Nat := 118140960795 + 4233144 * 2 ^ 59
def prefixEnd_4233144 : Nat := 4983230072969 + 3 ^ 40 * 4233144 * 2
def baseEnd_4233144 : Nat := 2173637551696291038332131

theorem tailTrace_4233144 : CollatzResearch.WordTrace tailWord_4233144 prefixEnd_4233144 2173637551696291038332131 := by
  unfold tailWord_4233144
  simp only [CollatzResearch.WordTrace]
  refine ⟨77197722888024863141125243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102930297184033150854833657 77197722888024863141125243)
  ·
    refine ⟨115796584332037294711687865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77197722888024863141125243 115796584332037294711687865)
    ·
      refine ⟨86847438249027971033765899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115796584332037294711687865 86847438249027971033765899)
      ·
        refine ⟨130271157373541956550648849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86847438249027971033765899 130271157373541956550648849)
        ·
          refine ⟨97703368030156467412986637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130271157373541956550648849 97703368030156467412986637)
          ·
            refine ⟨36638763011308675279869989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97703368030156467412986637 36638763011308675279869989)
            ·
              refine ⟨6869768064620376614975623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36638763011308675279869989 6869768064620376614975623)
              ·
                refine ⟨10304652096930564922463435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6869768064620376614975623 10304652096930564922463435)
                ·
                  refine ⟨15456978145395847383695153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10304652096930564922463435 15456978145395847383695153)
                  ·
                    refine ⟨11592733609046885537771365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15456978145395847383695153 11592733609046885537771365)
                    ·
                      refine ⟨2173637551696291038332131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11592733609046885537771365 2173637551696291038332131)
                      ·
                        rfl

theorem cell23_4233144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 1, 1, 2, 4].length) (baseStart_4233144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233144 prefixEnd_4233144 := by exact prefixLift 4233144
  have htrace : WordTrace (prefixWord ++ tailWord_4233144) baseStart_4233144 baseEnd_4233144 := by
    simpa [prefixWord, tailWord_4233144, baseEnd_4233144] using wordTrace_append hprefix tailTrace_4233144
  have hstable : (prefixWord ++ tailWord_4233144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233144).length < 2 ^ (prefixWord ++ tailWord_4233144).sum := by decide
  have hdescent : baseEnd_4233144 < baseStart_4233144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233198 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3]
def baseStart_4233198 : Nat := 118140960795 + 4233198 * 2 ^ 59
def prefixEnd_4233198 : Nat := 4983230072969 + 3 ^ 40 * 4233198 * 2
def baseEnd_4233198 : Nat := 2173665279651633827056883

theorem tailTrace_4233198 : CollatzResearch.WordTrace tailWord_4233198 prefixEnd_4233198 2173665279651633827056883 := by
  unfold tailWord_4233198
  simp only [CollatzResearch.WordTrace]
  refine ⟨19299676914731761688089531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102931610211902729003144165 19299676914731761688089531)
  ·
    refine ⟨28949515372097642532134297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19299676914731761688089531 28949515372097642532134297)
    ·
      refine ⟨21712136529073231899100723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28949515372097642532134297 21712136529073231899100723)
      ·
        refine ⟨32568204793609847848651085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21712136529073231899100723 32568204793609847848651085)
        ·
          refine ⟨12213076797603692943244157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32568204793609847848651085 12213076797603692943244157)
          ·
            refine ⟨4579903799101384853716559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12213076797603692943244157 4579903799101384853716559)
            ·
              refine ⟨6869855698652077280574839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4579903799101384853716559 6869855698652077280574839)
              ·
                refine ⟨10304783547978115920862259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6869855698652077280574839 10304783547978115920862259)
                ·
                  refine ⟨15457175321967173881293389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10304783547978115920862259 15457175321967173881293389)
                  ·
                    refine ⟨5796440745737690205485021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15457175321967173881293389 5796440745737690205485021)
                    ·
                      refine ⟨2173665279651633827056883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5796440745737690205485021 2173665279651633827056883)
                      ·
                        rfl

theorem cell23_4233198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_4233198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233198 prefixEnd_4233198 := by exact prefixLift 4233198
  have htrace : WordTrace (prefixWord ++ tailWord_4233198) baseStart_4233198 baseEnd_4233198 := by
    simpa [prefixWord, tailWord_4233198, baseEnd_4233198] using wordTrace_append hprefix tailTrace_4233198
  have hstable : (prefixWord ++ tailWord_4233198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233198).length < 2 ^ (prefixWord ++ tailWord_4233198).sum := by decide
  have hdescent : baseEnd_4233198 < baseStart_4233198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233207 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 5]
def baseStart_4233207 : Nat := 118140960795 + 4233207 * 2 ^ 59
def prefixEnd_4233207 : Nat := 4983230072969 + 3 ^ 40 * 4233207 * 2
def baseEnd_4233207 : Nat := 2173669900977524291844341

theorem tailTrace_4233207 : CollatzResearch.WordTrace tailWord_4233207 prefixEnd_4233207 2173669900977524291844341 := by
  unfold tailWord_4233207
  simp only [CollatzResearch.WordTrace]
  refine ⟨154397743574821488041793875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102931829049880992027862583 154397743574821488041793875)
  ·
    refine ⟨231596615362232232062690813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154397743574821488041793875 231596615362232232062690813)
    ·
      refine ⟨86848730760837087023509055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231596615362232232062690813 86848730760837087023509055)
      ·
        refine ⟨130273096141255630535263583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86848730760837087023509055 130273096141255630535263583)
        ·
          refine ⟨195409644211883445802895375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130273096141255630535263583 195409644211883445802895375)
          ·
            refine ⟨293114466317825168704343063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195409644211883445802895375 293114466317825168704343063)
            ·
              refine ⟨439671699476737753056514595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293114466317825168704343063 439671699476737753056514595)
              ·
                refine ⟨659507549215106629584771893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 439671699476737753056514595 659507549215106629584771893)
                ·
                  refine ⟨61828832738916246523572365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 659507549215106629584771893 61828832738916246523572365)
                  ·
                    refine ⟨23185812277093592446339637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61828832738916246523572365 23185812277093592446339637)
                    ·
                      refine ⟨2173669900977524291844341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23185812277093592446339637 2173669900977524291844341)
                      ·
                        rfl

theorem cell23_4233207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_4233207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233207 prefixEnd_4233207 := by exact prefixLift 4233207
  have htrace : WordTrace (prefixWord ++ tailWord_4233207) baseStart_4233207 baseEnd_4233207 := by
    simpa [prefixWord, tailWord_4233207, baseEnd_4233207] using wordTrace_append hprefix tailTrace_4233207
  have hstable : (prefixWord ++ tailWord_4233207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233207).length < 2 ^ (prefixWord ++ tailWord_4233207).sum := by decide
  have hdescent : baseEnd_4233207 < baseStart_4233207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233222 : List Nat := [6, 2, 1, 2, 2, 1, 9]
def baseStart_4233222 : Nat := 118140960795 + 4233222 * 2 ^ 59
def prefixEnd_4233222 : Nat := 4983230072969 + 3 ^ 40 * 4233222 * 2
def baseEnd_4233222 : Nat := 26835525965275823866133

theorem tailTrace_4233222 : CollatzResearch.WordTrace tailWord_4233222 prefixEnd_4233222 26835525965275823866133 := by
  unfold tailWord_4233222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4824946583430223300112185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 102932193779844763735726613 4824946583430223300112185)
  ·
    refine ⟨3618709937572667475084139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4824946583430223300112185 3618709937572667475084139)
    ·
      refine ⟨5428064906359001212626209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3618709937572667475084139 5428064906359001212626209)
      ·
        refine ⟨4071048679769250909469657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5428064906359001212626209 4071048679769250909469657)
        ·
          refine ⟨3053286509826938182102243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4071048679769250909469657 3053286509826938182102243)
          ·
            refine ⟨4579929764740407273153365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3053286509826938182102243 4579929764740407273153365)
            ·
              refine ⟨26835525965275823866133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4579929764740407273153365 26835525965275823866133)
              ·
                rfl

theorem cell23_4233222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 9].length) (baseStart_4233222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233222 prefixEnd_4233222 := by exact prefixLift 4233222
  have htrace : WordTrace (prefixWord ++ tailWord_4233222) baseStart_4233222 baseEnd_4233222 := by
    simpa [prefixWord, tailWord_4233222, baseEnd_4233222] using wordTrace_append hprefix tailTrace_4233222
  have hstable : (prefixWord ++ tailWord_4233222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233222).length < 2 ^ (prefixWord ++ tailWord_4233222).sum := by decide
  have hdescent : baseEnd_4233222 < baseStart_4233222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233224 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_4233224 : Nat := 118140960795 + 4233224 * 2 ^ 59
def prefixEnd_4233224 : Nat := 4983230072969 + 3 ^ 40 * 4233224 * 2
def baseEnd_4233224 : Nat := 2173678630148650725331763

theorem tailTrace_4233224 : CollatzResearch.WordTrace tailWord_4233224 prefixEnd_4233224 2173678630148650725331763 := by
  unfold tailWord_4233224
  simp only [CollatzResearch.WordTrace]
  refine ⟨77199181807879949972581363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102932242410506599963441817 77199181807879949972581363)
  ·
    refine ⟨115798772711819924958872045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77199181807879949972581363 115798772711819924958872045)
    ·
      refine ⟨43424539766932471859577017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115798772711819924958872045 43424539766932471859577017)
      ·
        refine ⟨32568404825199353894682763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43424539766932471859577017 32568404825199353894682763)
        ·
          refine ⟨48852607237799030842024145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32568404825199353894682763 48852607237799030842024145)
          ·
            refine ⟨36639455428349273131518109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48852607237799030842024145 36639455428349273131518109)
            ·
              refine ⟨13739795785630977424319291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36639455428349273131518109 13739795785630977424319291)
              ·
                refine ⟨20609693678446466136478937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13739795785630977424319291 20609693678446466136478937)
                ·
                  refine ⟨15457270258834849602359203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20609693678446466136478937 15457270258834849602359203)
                  ·
                    refine ⟨23185905388252274403538805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15457270258834849602359203 23185905388252274403538805)
                    ·
                      refine ⟨2173678630148650725331763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23185905388252274403538805 2173678630148650725331763)
                      ·
                        rfl

theorem cell23_4233224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_4233224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233224 prefixEnd_4233224 := by exact prefixLift 4233224
  have htrace : WordTrace (prefixWord ++ tailWord_4233224) baseStart_4233224 baseEnd_4233224 := by
    simpa [prefixWord, tailWord_4233224, baseEnd_4233224] using wordTrace_append hprefix tailTrace_4233224
  have hstable : (prefixWord ++ tailWord_4233224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233224).length < 2 ^ (prefixWord ++ tailWord_4233224).sum := by decide
  have hdescent : baseEnd_4233224 < baseStart_4233224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233321 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 3, 4]
def baseStart_4233321 : Nat := 118140960795 + 4233321 * 2 ^ 59
def prefixEnd_4233321 : Nat := 4983230072969 + 3 ^ 40 * 4233321 * 2
def baseEnd_4233321 : Nat := 724576145924045615272939

theorem tailTrace_4233321 : CollatzResearch.WordTrace tailWord_4233321 prefixEnd_4233321 724576145924045615272939 := by
  unfold tailWord_4233321
  simp only [CollatzResearch.WordTrace]
  refine ⟨154401901496408485511443817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102934600997605657007629211 154401901496408485511443817)
  ·
    refine ⟨115801426122306364133582863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154401901496408485511443817 115801426122306364133582863)
    ·
      refine ⟨173702139183459546200374295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115801426122306364133582863 173702139183459546200374295)
      ·
        refine ⟨260553208775189319300561443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173702139183459546200374295 260553208775189319300561443)
        ·
          refine ⟨390829813162783978950842165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260553208775189319300561443 390829813162783978950842165)
          ·
            refine ⟨36640294984010998026641453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 390829813162783978950842165 36640294984010998026641453)
            ·
              refine ⟨13740110619004124259990545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36640294984010998026641453 13740110619004124259990545)
              ·
                refine ⟨10305082964253093194992909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13740110619004124259990545 10305082964253093194992909)
                ·
                  refine ⟨3864406111594909948122341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10305082964253093194992909 3864406111594909948122341)
                  ·
                    refine ⟨724576145924045615272939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3864406111594909948122341 724576145924045615272939)
                    ·
                      rfl

theorem cell23_4233321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 4].length) (baseStart_4233321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233321 prefixEnd_4233321 := by exact prefixLift 4233321
  have htrace : WordTrace (prefixWord ++ tailWord_4233321) baseStart_4233321 baseEnd_4233321 := by
    simpa [prefixWord, tailWord_4233321, baseEnd_4233321] using wordTrace_append hprefix tailTrace_4233321
  have hstable : (prefixWord ++ tailWord_4233321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233321).length < 2 ^ (prefixWord ++ tailWord_4233321).sum := by decide
  have hdescent : baseEnd_4233321 < baseStart_4233321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233328 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 4]
def baseStart_4233328 : Nat := 118140960795 + 4233328 * 2 ^ 59
def prefixEnd_4233328 : Nat := 4983230072969 + 3 ^ 40 * 4233328 * 2
def baseEnd_4233328 : Nat := 2173732032136718318431285

theorem tailTrace_4233328 : CollatzResearch.WordTrace tailWord_4233328 prefixEnd_4233328 2173732032136718318431285 := by
  unfold tailWord_4233328
  simp only [CollatzResearch.WordTrace]
  refine ⟨77201078403691562853474319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102934771204922083804632425 77201078403691562853474319)
  ·
    refine ⟨115801617605537344280211479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77201078403691562853474319 115801617605537344280211479)
    ·
      refine ⟨173702426408306016420317219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115801617605537344280211479 173702426408306016420317219)
      ·
        refine ⟨260553639612459024630475829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173702426408306016420317219 260553639612459024630475829)
        ·
          refine ⟨24426903713668033559107109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 260553639612459024630475829 24426903713668033559107109)
          ·
            refine ⟨4580044446312756292332583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24426903713668033559107109 4580044446312756292332583)
            ·
              refine ⟨6870066669469134438498875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4580044446312756292332583 6870066669469134438498875)
              ·
                refine ⟨10305100004203701657748313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6870066669469134438498875 10305100004203701657748313)
                ·
                  refine ⟨7728825003152776243311235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10305100004203701657748313 7728825003152776243311235)
                  ·
                    refine ⟨11593237504729164364966853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7728825003152776243311235 11593237504729164364966853)
                    ·
                      refine ⟨2173732032136718318431285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11593237504729164364966853 2173732032136718318431285)
                      ·
                        rfl

theorem cell23_4233328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 4].length) (baseStart_4233328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233328 prefixEnd_4233328 := by exact prefixLift 4233328
  have htrace : WordTrace (prefixWord ++ tailWord_4233328) baseStart_4233328 baseEnd_4233328 := by
    simpa [prefixWord, tailWord_4233328, baseEnd_4233328] using wordTrace_append hprefix tailTrace_4233328
  have hstable : (prefixWord ++ tailWord_4233328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233328).length < 2 ^ (prefixWord ++ tailWord_4233328).sum := by decide
  have hdescent : baseEnd_4233328 < baseStart_4233328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233351 : List Nat := [1, 1, 4, 2, 1, 1, 5, 2, 6]
def baseStart_4233351 : Nat := 118140960795 + 4233351 * 2 ^ 59
def prefixEnd_4233351 : Nat := 4983230072969 + 3 ^ 40 * 4233351 * 2
def baseEnd_4233351 : Nat := 241527093576863525382631

theorem tailTrace_4233351 : CollatzResearch.WordTrace tailWord_4233351 prefixEnd_4233351 241527093576863525382631 := by
  unfold tailWord_4233351
  simp only [CollatzResearch.WordTrace]
  refine ⟨154402995686299800635035907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102935330457533200423357271 154402995686299800635035907)
  ·
    refine ⟨231604493529449700952553861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154402995686299800635035907 231604493529449700952553861)
    ·
      refine ⟨43425842536771818928603849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231604493529449700952553861 43425842536771818928603849)
      ·
        refine ⟨32569381902578864196452887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43425842536771818928603849 32569381902578864196452887)
        ·
          refine ⟨48854072853868296294679331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32569381902578864196452887 48854072853868296294679331)
          ·
            refine ⟨73281109280802444442018997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48854072853868296294679331 73281109280802444442018997)
            ·
              refine ⟨6870103995075229166439281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 73281109280802444442018997 6870103995075229166439281)
              ·
                refine ⟨5152577996306421874829461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6870103995075229166439281 5152577996306421874829461)
                ·
                  refine ⟨241527093576863525382631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5152577996306421874829461 241527093576863525382631)
                  ·
                    rfl

theorem cell23_4233351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 6].length) (baseStart_4233351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233351 prefixEnd_4233351 := by exact prefixLift 4233351
  have htrace : WordTrace (prefixWord ++ tailWord_4233351) baseStart_4233351 baseEnd_4233351 := by
    simpa [prefixWord, tailWord_4233351, baseEnd_4233351] using wordTrace_append hprefix tailTrace_4233351
  have hstable : (prefixWord ++ tailWord_4233351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233351).length < 2 ^ (prefixWord ++ tailWord_4233351).sum := by decide
  have hdescent : baseEnd_4233351 < baseStart_4233351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233371 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 3, 5, 2]
def baseStart_4233371 : Nat := 118140960795 + 4233371 * 2 ^ 59
def prefixEnd_4233371 : Nat := 4983230072969 + 3 ^ 40 * 4233371 * 2
def baseEnd_4233371 : Nat := 2173754111804861650193587

theorem tailTrace_4233371 : CollatzResearch.WordTrace tailWord_4233371 prefixEnd_4233371 2173754111804861650193587 := by
  unfold tailWord_4233371
  simp only [CollatzResearch.WordTrace]
  refine ⟨154403725146227344050763967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102935816764151562700509311 154403725146227344050763967)
  ·
    refine ⟨231605587719341016076145951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154403725146227344050763967 231605587719341016076145951)
    ·
      refine ⟨347408381579011524114218927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231605587719341016076145951 347408381579011524114218927)
      ·
        refine ⟨521112572368517286171328391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347408381579011524114218927 521112572368517286171328391)
        ·
          refine ⟨781668858552775929256992587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521112572368517286171328391 781668858552775929256992587)
          ·
            refine ⟨1172503287829163893885488881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781668858552775929256992587 1172503287829163893885488881)
            ·
              refine ⟨879377465871872920414116661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1172503287829163893885488881 879377465871872920414116661)
              ·
                refine ⟨82441637425488086288823437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 879377465871872920414116661 82441637425488086288823437)
                ·
                  refine ⟨30915614034558032358308789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82441637425488086288823437 30915614034558032358308789)
                  ·
                    refine ⟨2898338815739815533591449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30915614034558032358308789 2898338815739815533591449)
                    ·
                      refine ⟨2173754111804861650193587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898338815739815533591449 2173754111804861650193587)
                      ·
                        rfl

theorem cell23_4233371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 5, 2].length) (baseStart_4233371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233371 prefixEnd_4233371 := by exact prefixLift 4233371
  have htrace : WordTrace (prefixWord ++ tailWord_4233371) baseStart_4233371 baseEnd_4233371 := by
    simpa [prefixWord, tailWord_4233371, baseEnd_4233371] using wordTrace_append hprefix tailTrace_4233371
  have hstable : (prefixWord ++ tailWord_4233371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233371).length < 2 ^ (prefixWord ++ tailWord_4233371).sum := by decide
  have hdescent : baseEnd_4233371 < baseStart_4233371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233412 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_4233412 : Nat := 118140960795 + 4233412 * 2 ^ 59
def prefixEnd_4233412 : Nat := 4983230072969 + 3 ^ 40 * 4233412 * 2
def baseEnd_4233412 : Nat := 2173775164511695989780899

theorem tailTrace_4233412 : CollatzResearch.WordTrace tailWord_4233412 prefixEnd_4233412 2173775164511695989780899 := by
  unfold tailWord_4233412
  simp only [CollatzResearch.WordTrace]
  refine ⟨77202610269539404026503245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102936813692719205368670993 77202610269539404026503245)
  ·
    refine ⟨28950978851077276509938717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77202610269539404026503245 28950978851077276509938717)
    ·
      refine ⟨10856617069153978691227019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28950978851077276509938717 10856617069153978691227019)
      ·
        refine ⟨16284925603730968036840529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10856617069153978691227019 16284925603730968036840529)
        ·
          refine ⟨12213694202798226027630397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16284925603730968036840529 12213694202798226027630397)
          ·
            refine ⟨4580135326049334760361399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12213694202798226027630397 4580135326049334760361399)
            ·
              refine ⟨6870202989074002140542099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4580135326049334760361399 6870202989074002140542099)
              ·
                refine ⟨10305304483611003210813149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6870202989074002140542099 10305304483611003210813149)
                ·
                  refine ⟨3864489181354126204054931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10305304483611003210813149 3864489181354126204054931)
                  ·
                    refine ⟨5796733772031189306082397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3864489181354126204054931 5796733772031189306082397)
                    ·
                      refine ⟨2173775164511695989780899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5796733772031189306082397 2173775164511695989780899)
                      ·
                        rfl

theorem cell23_4233412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_4233412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233412 prefixEnd_4233412 := by exact prefixLift 4233412
  have htrace : WordTrace (prefixWord ++ tailWord_4233412) baseStart_4233412 baseEnd_4233412 := by
    simpa [prefixWord, tailWord_4233412, baseEnd_4233412] using wordTrace_append hprefix tailTrace_4233412
  have hstable : (prefixWord ++ tailWord_4233412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233412).length < 2 ^ (prefixWord ++ tailWord_4233412).sum := by decide
  have hdescent : baseEnd_4233412 < baseStart_4233412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233431 : List Nat := [1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 4]
def baseStart_4233431 : Nat := 118140960795 + 4233431 * 2 ^ 59
def prefixEnd_4233431 : Nat := 4983230072969 + 3 ^ 40 * 4233431 * 2
def baseEnd_4233431 : Nat := 2173784920644131415443311

theorem tailTrace_4233431 : CollatzResearch.WordTrace tailWord_4233431 prefixEnd_4233431 2173784920644131415443311 := by
  unfold tailWord_4233431
  simp only [CollatzResearch.WordTrace]
  refine ⟨154405913526009974297948147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102937275684006649531965431 154405913526009974297948147)
  ·
    refine ⟨231608870289014961446922221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154405913526009974297948147 231608870289014961446922221)
    ·
      refine ⟨86853326358380610542595833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231608870289014961446922221 86853326358380610542595833)
      ·
        refine ⟨65139994768785457906946875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86853326358380610542595833 65139994768785457906946875)
        ·
          refine ⟨97709992153178186860420313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65139994768785457906946875 97709992153178186860420313)
          ·
            refine ⟨73282494114883640145315235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97709992153178186860420313 73282494114883640145315235)
            ·
              refine ⟨109923741172325460217972853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73282494114883640145315235 109923741172325460217972853)
              ·
                refine ⟨10305350734905511895434955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109923741172325460217972853 10305350734905511895434955)
                ·
                  refine ⟨15458026102358267843152433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10305350734905511895434955 15458026102358267843152433)
                  ·
                    refine ⟨11593519576768700882364325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15458026102358267843152433 11593519576768700882364325)
                    ·
                      refine ⟨2173784920644131415443311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11593519576768700882364325 2173784920644131415443311)
                      ·
                        rfl

theorem cell23_4233431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_4233431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233431 prefixEnd_4233431 := by exact prefixLift 4233431
  have htrace : WordTrace (prefixWord ++ tailWord_4233431) baseStart_4233431 baseEnd_4233431 := by
    simpa [prefixWord, tailWord_4233431, baseEnd_4233431] using wordTrace_append hprefix tailTrace_4233431
  have hstable : (prefixWord ++ tailWord_4233431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233431).length < 2 ^ (prefixWord ++ tailWord_4233431).sum := by decide
  have hdescent : baseEnd_4233431 < baseStart_4233431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233448 : List Nat := [2, 1, 4, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_4233448 : Nat := 118140960795 + 4233448 * 2 ^ 59
def prefixEnd_4233448 : Nat := 4983230072969 + 3 ^ 40 * 4233448 * 2
def baseEnd_4233448 : Nat := 2173793649815257848930733

theorem tailTrace_4233448 : CollatzResearch.WordTrace tailWord_4233448 prefixEnd_4233448 2173793649815257848930733 := by
  unfold tailWord_4233448
  simp only [CollatzResearch.WordTrace]
  refine ⟨77203266783474193100658499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102937689044632257467544665 77203266783474193100658499)
  ·
    refine ⟨115804900175211289650987749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77203266783474193100658499 115804900175211289650987749)
    ·
      refine ⟨21713418782852116809560203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115804900175211289650987749 21713418782852116809560203)
      ·
        refine ⟨32570128174278175214340305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21713418782852116809560203 32570128174278175214340305)
        ·
          refine ⟨24427596130708631410755229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32570128174278175214340305 24427596130708631410755229)
          ·
            refine ⟨9160348549015736779033211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24427596130708631410755229 9160348549015736779033211)
            ·
              refine ⟨13740522823523605168549817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9160348549015736779033211 13740522823523605168549817)
              ·
                refine ⟨10305392117642703876412363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13740522823523605168549817 10305392117642703876412363)
                ·
                  refine ⟨15458088176464055814618545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10305392117642703876412363 15458088176464055814618545)
                  ·
                    refine ⟨11593566132348041860963909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15458088176464055814618545 11593566132348041860963909)
                    ·
                      refine ⟨2173793649815257848930733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11593566132348041860963909 2173793649815257848930733)
                      ·
                        rfl

theorem cell23_4233448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_4233448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233448 prefixEnd_4233448 := by exact prefixLift 4233448
  have htrace : WordTrace (prefixWord ++ tailWord_4233448) baseStart_4233448 baseEnd_4233448 := by
    simpa [prefixWord, tailWord_4233448, baseEnd_4233448] using wordTrace_append hprefix tailTrace_4233448
  have hstable : (prefixWord ++ tailWord_4233448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233448).length < 2 ^ (prefixWord ++ tailWord_4233448).sum := by decide
  have hdescent : baseEnd_4233448 < baseStart_4233448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233452 : List Nat := [2, 2, 1, 1, 2, 3, 2, 5, 1, 2, 2]
def baseStart_4233452 : Nat := 118140960795 + 4233452 * 2 ^ 59
def prefixEnd_4233452 : Nat := 4983230072969 + 3 ^ 40 * 4233452 * 2
def baseEnd_4233452 : Nat := 2173795703737875833280715

theorem tailTrace_4233452 : CollatzResearch.WordTrace tailWord_4233452 prefixEnd_4233452 2173795703737875833280715 := by
  unfold tailWord_4233452
  simp only [CollatzResearch.WordTrace]
  refine ⟨77203339729466947442231305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102937786305955929922975073 77203339729466947442231305)
  ·
    refine ⟨57902504797100210581673479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77203339729466947442231305 57902504797100210581673479)
    ·
      refine ⟨86853757195650315872510219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57902504797100210581673479 86853757195650315872510219)
      ·
        refine ⟨130280635793475473808765329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86853757195650315872510219 130280635793475473808765329)
        ·
          refine ⟨97710476845106605356573997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130280635793475473808765329 97710476845106605356573997)
          ·
            refine ⟨36641428816914977008715249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97710476845106605356573997 36641428816914977008715249)
            ·
              refine ⟨27481071612686232756536437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36641428816914977008715249 27481071612686232756536437)
              ·
                refine ⟨2576350463689334320925291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27481071612686232756536437 2576350463689334320925291)
                ·
                  refine ⟨3864525695534001481387937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2576350463689334320925291 3864525695534001481387937)
                  ·
                    refine ⟨2898394271650501111040953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3864525695534001481387937 2898394271650501111040953)
                    ·
                      refine ⟨2173795703737875833280715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898394271650501111040953 2173795703737875833280715)
                      ·
                        rfl

theorem cell23_4233452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 5, 1, 2, 2].length) (baseStart_4233452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233452 prefixEnd_4233452 := by exact prefixLift 4233452
  have htrace : WordTrace (prefixWord ++ tailWord_4233452) baseStart_4233452 baseEnd_4233452 := by
    simpa [prefixWord, tailWord_4233452, baseEnd_4233452] using wordTrace_append hprefix tailTrace_4233452
  have hstable : (prefixWord ++ tailWord_4233452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233452).length < 2 ^ (prefixWord ++ tailWord_4233452).sum := by decide
  have hdescent : baseEnd_4233452 < baseStart_4233452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233495 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 3, 3, 2]
def baseStart_4233495 : Nat := 118140960795 + 4233495 * 2 ^ 59
def prefixEnd_4233495 : Nat := 4983230072969 + 3 ^ 40 * 4233495 * 2
def baseEnd_4233495 : Nat := 2173817783406019165043017

theorem tailTrace_4233495 : CollatzResearch.WordTrace tailWord_4233495 prefixEnd_4233495 2173817783406019165043017 := by
  unfold tailWord_4233495
  simp only [CollatzResearch.WordTrace]
  refine ⟨154408247797778113228277939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102938831865185408818851959 154408247797778113228277939)
  ·
    refine ⟨231612371696667169842416909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154408247797778113228277939 231612371696667169842416909)
    ·
      refine ⟨86854639386250188690906341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231612371696667169842416909 86854639386250188690906341)
      ·
        refine ⟨16285244884921910379544939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86854639386250188690906341 16285244884921910379544939)
        ·
          refine ⟨24427867327382865569317409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16285244884921910379544939 24427867327382865569317409)
          ·
            refine ⟨18320900495537149176988057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24427867327382865569317409 18320900495537149176988057)
            ·
              refine ⟨13740675371652861882741043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18320900495537149176988057 13740675371652861882741043)
              ·
                refine ⟨20611013057479292824111565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13740675371652861882741043 20611013057479292824111565)
                ·
                  refine ⟨7729129896554734809041837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20611013057479292824111565 7729129896554734809041837)
                  ·
                    refine ⟨2898423711208025553390689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7729129896554734809041837 2898423711208025553390689)
                    ·
                      refine ⟨2173817783406019165043017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898423711208025553390689 2173817783406019165043017)
                      ·
                        rfl

theorem cell23_4233495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_4233495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233495 prefixEnd_4233495 := by exact prefixLift 4233495
  have htrace : WordTrace (prefixWord ++ tailWord_4233495) baseStart_4233495 baseEnd_4233495 := by
    simpa [prefixWord, tailWord_4233495, baseEnd_4233495] using wordTrace_append hprefix tailTrace_4233495
  have hstable : (prefixWord ++ tailWord_4233495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233495).length < 2 ^ (prefixWord ++ tailWord_4233495).sum := by decide
  have hdescent : baseEnd_4233495 < baseStart_4233495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233502 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 1, 3, 3]
def baseStart_4233502 : Nat := 118140960795 + 4233502 * 2 ^ 59
def prefixEnd_4233502 : Nat := 4983230072969 + 3 ^ 40 * 4233502 * 2
def baseEnd_4233502 : Nat := 2173821377770600637655485

theorem tailTrace_4233502 : CollatzResearch.WordTrace tailWord_4233502 prefixEnd_4233502 2173821377770600637655485 := by
  unfold tailWord_4233502
  simp only [CollatzResearch.WordTrace]
  refine ⟨19301062888594094177972845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102939002072501835615855173 19301062888594094177972845)
  ·
    refine ⟨7237898583222785316739817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19301062888594094177972845 7237898583222785316739817)
    ·
      refine ⟨5428423937417088987554863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7237898583222785316739817 5428423937417088987554863)
      ·
        refine ⟨8142635906125633481332295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5428423937417088987554863 8142635906125633481332295)
        ·
          refine ⟨12213953859188450221998443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8142635906125633481332295 12213953859188450221998443)
          ·
            refine ⟨18320930788782675332997665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12213953859188450221998443 18320930788782675332997665)
            ·
              refine ⟨13740698091587006499748249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18320930788782675332997665 13740698091587006499748249)
              ·
                refine ⟨10305523568690254874811187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13740698091587006499748249 10305523568690254874811187)
                ·
                  refine ⟨15458285353035382312216781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10305523568690254874811187 15458285353035382312216781)
                  ·
                    refine ⟨5796857007388268367081293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15458285353035382312216781 5796857007388268367081293)
                    ·
                      refine ⟨2173821377770600637655485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5796857007388268367081293 2173821377770600637655485)
                      ·
                        rfl

theorem cell23_4233502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_4233502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233502 prefixEnd_4233502 := by exact prefixLift 4233502
  have htrace : WordTrace (prefixWord ++ tailWord_4233502) baseStart_4233502 baseEnd_4233502 := by
    simpa [prefixWord, tailWord_4233502, baseEnd_4233502] using wordTrace_append hprefix tailTrace_4233502
  have hstable : (prefixWord ++ tailWord_4233502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233502).length < 2 ^ (prefixWord ++ tailWord_4233502).sum := by decide
  have hdescent : baseEnd_4233502 < baseStart_4233502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233591 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 2, 8]
def baseStart_4233591 : Nat := 118140960795 + 4233591 * 2 ^ 59
def prefixEnd_4233591 : Nat := 4983230072969 + 3 ^ 40 * 4233591 * 2
def baseEnd_4233591 : Nat := 724622359182950263147525

theorem tailTrace_4233591 : CollatzResearch.WordTrace tailWord_4233591 prefixEnd_4233591 724622359182950263147525 := by
  unfold tailWord_4233591
  simp only [CollatzResearch.WordTrace]
  refine ⟨154411749205430321623772627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102941166136953547749181751 154411749205430321623772627)
  ·
    refine ⟨231617623808145482435658941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154411749205430321623772627 231617623808145482435658941)
    ·
      refine ⟨86856608928054555913372103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231617623808145482435658941 86856608928054555913372103)
      ·
        refine ⟨130284913392081833870058155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86856608928054555913372103 130284913392081833870058155)
        ·
          refine ⟨195427370088122750805087233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130284913392081833870058155 195427370088122750805087233)
          ·
            refine ⟨146570527566092063103815425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195427370088122750805087233 146570527566092063103815425)
            ·
              refine ⟨109927895674569047327861569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146570527566092063103815425 109927895674569047327861569)
              ·
                refine ⟨82445921755926785495896177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109927895674569047327861569 82445921755926785495896177)
                ·
                  refine ⟨61834441316945089121922133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82445921755926785495896177 61834441316945089121922133)
                  ·
                    refine ⟨724622359182950263147525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61834441316945089121922133 724622359182950263147525)
                    ·
                      rfl

theorem cell23_4233591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 8].length) (baseStart_4233591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233591 prefixEnd_4233591 := by exact prefixLift 4233591
  have htrace : WordTrace (prefixWord ++ tailWord_4233591) baseStart_4233591 baseEnd_4233591 := by
    simpa [prefixWord, tailWord_4233591, baseEnd_4233591] using wordTrace_append hprefix tailTrace_4233591
  have hstable : (prefixWord ++ tailWord_4233591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233591).length < 2 ^ (prefixWord ++ tailWord_4233591).sum := by decide
  have hdescent : baseEnd_4233591 < baseStart_4233591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233635 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 3]
def baseStart_4233635 : Nat := 118140960795 + 4233635 * 2 ^ 59
def prefixEnd_4233635 : Nat := 4983230072969 + 3 ^ 40 * 4233635 * 2
def baseEnd_4233635 : Nat := 2173889670697648617292373

theorem tailTrace_4233635 : CollatzResearch.WordTrace tailWord_4233635 prefixEnd_4233635 2173889670697648617292373 := by
  unfold tailWord_4233635
  simp only [CollatzResearch.WordTrace]
  refine ⟨154413354017270917138374359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102942236011513944758916239 154413354017270917138374359)
  ·
    refine ⟨231620031025906375707561539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154413354017270917138374359 231620031025906375707561539)
    ·
      refine ⟨347430046538859563561342309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231620031025906375707561539 347430046538859563561342309)
      ·
        refine ⟨65143133726036168167751683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 347430046538859563561342309 65143133726036168167751683)
        ·
          refine ⟨97714700589054252251627525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65143133726036168167751683 97714700589054252251627525)
          ·
            refine ⟨18321506360447672297180161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97714700589054252251627525 18321506360447672297180161)
            ·
              refine ⟨13741129770335754222885121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18321506360447672297180161 13741129770335754222885121)
              ·
                refine ⟨10305847327751815667163841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13741129770335754222885121 10305847327751815667163841)
                ·
                  refine ⟨7729385495813861750372881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10305847327751815667163841 7729385495813861750372881)
                  ·
                    refine ⟨5797039121860396312779661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7729385495813861750372881 5797039121860396312779661)
                    ·
                      refine ⟨2173889670697648617292373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5797039121860396312779661 2173889670697648617292373)
                      ·
                        rfl

theorem cell23_4233635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_4233635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233635 prefixEnd_4233635 := by exact prefixLift 4233635
  have htrace : WordTrace (prefixWord ++ tailWord_4233635) baseStart_4233635 baseEnd_4233635 := by
    simpa [prefixWord, tailWord_4233635, baseEnd_4233635] using wordTrace_append hprefix tailTrace_4233635
  have hstable : (prefixWord ++ tailWord_4233635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233635).length < 2 ^ (prefixWord ++ tailWord_4233635).sum := by decide
  have hdescent : baseEnd_4233635 < baseStart_4233635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233678 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_4233678 : Nat := 118140960795 + 4233678 * 2 ^ 59
def prefixEnd_4233678 : Nat := 4983230072969 + 3 ^ 40 * 4233678 * 2
def baseEnd_4233678 : Nat := 2173911750365791949054675

theorem tailTrace_4233678 : CollatzResearch.WordTrace tailWord_4233678 prefixEnd_4233678 2173911750365791949054675 := by
  unfold tailWord_4233678
  simp only [CollatzResearch.WordTrace]
  refine ⟨19301865294514391935273711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102943281570743423654793125 19301865294514391935273711)
  ·
    refine ⟨28952797941771587902910567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19301865294514391935273711 28952797941771587902910567)
    ·
      refine ⟨43429196912657381854365851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28952797941771587902910567 43429196912657381854365851)
      ·
        refine ⟨65143795368986072781548777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43429196912657381854365851 65143795368986072781548777)
        ·
          refine ⟨48857846526739554586161583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65143795368986072781548777 48857846526739554586161583)
          ·
            refine ⟨73286769790109331879242375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48857846526739554586161583 73286769790109331879242375)
            ·
              refine ⟨109930154685163997818863563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73286769790109331879242375 109930154685163997818863563)
              ·
                refine ⟨164895232027745996728295345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109930154685163997818863563 164895232027745996728295345)
                ·
                  refine ⟨123671424020809497546221509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164895232027745996728295345 123671424020809497546221509)
                  ·
                    refine ⟨23188392003901780789916533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123671424020809497546221509 23188392003901780789916533)
                    ·
                      refine ⟨2173911750365791949054675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23188392003901780789916533 2173911750365791949054675)
                      ·
                        rfl

theorem cell23_4233678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_4233678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233678 prefixEnd_4233678 := by exact prefixLift 4233678
  have htrace : WordTrace (prefixWord ++ tailWord_4233678) baseStart_4233678 baseEnd_4233678 := by
    simpa [prefixWord, tailWord_4233678, baseEnd_4233678] using wordTrace_append hprefix tailTrace_4233678
  have hstable : (prefixWord ++ tailWord_4233678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233678).length < 2 ^ (prefixWord ++ tailWord_4233678).sum := by decide
  have hdescent : baseEnd_4233678 < baseStart_4233678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233699 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 3, 1, 3]
def baseStart_4233699 : Nat := 118140960795 + 4233699 * 2 ^ 59
def prefixEnd_4233699 : Nat := 4983230072969 + 3 ^ 40 * 4233699 * 2
def baseEnd_4233699 : Nat := 2173922533459536366892079

theorem tailTrace_4233699 : CollatzResearch.WordTrace tailWord_4233699 prefixEnd_4233699 2173922533459536366892079 := by
  unfold tailWord_4233699
  simp only [CollatzResearch.WordTrace]
  refine ⟨154415688289039056068704151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102943792192692704045802767 154415688289039056068704151)
  ·
    refine ⟨231623532433558584103056227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154415688289039056068704151 231623532433558584103056227)
    ·
      refine ⟨347435298650337876154584341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231623532433558584103056227 347435298650337876154584341)
      ·
        refine ⟨16286029624234587944746141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 347435298650337876154584341 16286029624234587944746141)
        ·
          refine ⟨6107261109087970479279803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16286029624234587944746141 6107261109087970479279803)
          ·
            refine ⟨9160891663631955718919705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6107261109087970479279803 9160891663631955718919705)
            ·
              refine ⟨6870668747723966789189779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9160891663631955718919705 6870668747723966789189779)
              ·
                refine ⟨10306003121585950183784669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6870668747723966789189779 10306003121585950183784669)
                ·
                  refine ⟨3864751170594731318919251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10306003121585950183784669 3864751170594731318919251)
                  ·
                    refine ⟨5797126755892096978378877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3864751170594731318919251 5797126755892096978378877)
                    ·
                      refine ⟨2173922533459536366892079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5797126755892096978378877 2173922533459536366892079)
                      ·
                        rfl

theorem cell23_4233699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_4233699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233699 prefixEnd_4233699 := by exact prefixLift 4233699
  have htrace : WordTrace (prefixWord ++ tailWord_4233699) baseStart_4233699 baseEnd_4233699 := by
    simpa [prefixWord, tailWord_4233699, baseEnd_4233699] using wordTrace_append hprefix tailTrace_4233699
  have hstable : (prefixWord ++ tailWord_4233699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233699).length < 2 ^ (prefixWord ++ tailWord_4233699).sum := by decide
  have hdescent : baseEnd_4233699 < baseStart_4233699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233722 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2]
def baseStart_4233722 : Nat := 118140960795 + 4233722 * 2 ^ 59
def prefixEnd_4233722 : Nat := 4983230072969 + 3 ^ 40 * 4233722 * 2
def baseEnd_4233722 : Nat := 2173934343514589776904473

theorem tailTrace_4233722 : CollatzResearch.WordTrace tailWord_4233722 prefixEnd_4233722 2173934343514589776904473 := by
  unfold tailWord_4233722
  simp only [CollatzResearch.WordTrace]
  refine ⟨38604131791988932749197855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102944351445303820664527613 38604131791988932749197855)
  ·
    refine ⟨57906197687983399123796783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38604131791988932749197855 57906197687983399123796783)
    ·
      refine ⟨86859296531975098685695175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57906197687983399123796783 86859296531975098685695175)
      ·
        refine ⟨130288944797962648028542763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86859296531975098685695175 130288944797962648028542763)
        ·
          refine ⟨195433417196943972042814145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130288944797962648028542763 195433417196943972042814145)
          ·
            refine ⟨146575062897707979032110609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195433417196943972042814145 146575062897707979032110609)
            ·
              refine ⟨109931297173280984274082957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146575062897707979032110609 109931297173280984274082957)
              ·
                refine ⟨41224236439980369102781109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109931297173280984274082957 41224236439980369102781109)
                ·
                  refine ⟨3864772166248159603385729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41224236439980369102781109 3864772166248159603385729)
                  ·
                    refine ⟨2898579124686119702539297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3864772166248159603385729 2898579124686119702539297)
                    ·
                      refine ⟨2173934343514589776904473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898579124686119702539297 2173934343514589776904473)
                      ·
                        rfl

theorem cell23_4233722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 5, 2, 2].length) (baseStart_4233722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233722 prefixEnd_4233722 := by exact prefixLift 4233722
  have htrace : WordTrace (prefixWord ++ tailWord_4233722) baseStart_4233722 baseEnd_4233722 := by
    simpa [prefixWord, tailWord_4233722, baseEnd_4233722] using wordTrace_append hprefix tailTrace_4233722
  have hstable : (prefixWord ++ tailWord_4233722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233722).length < 2 ^ (prefixWord ++ tailWord_4233722).sum := by decide
  have hdescent : baseEnd_4233722 < baseStart_4233722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233732 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_4233732 : Nat := 118140960795 + 4233732 * 2 ^ 59
def prefixEnd_4233732 : Nat := 4983230072969 + 3 ^ 40 * 4233732 * 2
def baseEnd_4233732 : Nat := 724646492773711579259809

theorem tailTrace_4233732 : CollatzResearch.WordTrace tailWord_4233732 prefixEnd_4233732 724646492773711579259809 := by
  unfold tailWord_4233732
  simp only [CollatzResearch.WordTrace]
  refine ⟨77208445948959751352327725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102944594598613001803103633 77208445948959751352327725)
  ·
    refine ⟨28953167230859906757122897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77208445948959751352327725 28953167230859906757122897)
    ·
      refine ⟨21714875423144930067842173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28953167230859906757122897 21714875423144930067842173)
      ·
        refine ⟨8143078283679348775440815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21714875423144930067842173 8143078283679348775440815)
        ·
          refine ⟨12214617425519023163161223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8143078283679348775440815 12214617425519023163161223)
          ·
            refine ⟨18321926138278534744741835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12214617425519023163161223 18321926138278534744741835)
            ·
              refine ⟨27482889207417802117112753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18321926138278534744741835 27482889207417802117112753)
              ·
                refine ⟨20612166905563351587834565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27482889207417802117112753 20612166905563351587834565)
                ·
                  refine ⟨3864781294793128422718981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20612166905563351587834565 3864781294793128422718981)
                  ·
                    refine ⟨724646492773711579259809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3864781294793128422718981 724646492773711579259809)
                    ·
                      rfl

theorem cell23_4233732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_4233732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233732 prefixEnd_4233732 := by exact prefixLift 4233732
  have htrace : WordTrace (prefixWord ++ tailWord_4233732) baseStart_4233732 baseEnd_4233732 := by
    simpa [prefixWord, tailWord_4233732, baseEnd_4233732] using wordTrace_append hprefix tailTrace_4233732
  have hstable : (prefixWord ++ tailWord_4233732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233732).length < 2 ^ (prefixWord ++ tailWord_4233732).sum := by decide
  have hdescent : baseEnd_4233732 < baseStart_4233732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233742 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_4233742 : Nat := 118140960795 + 4233742 * 2 ^ 59
def prefixEnd_4233742 : Nat := 4983230072969 + 3 ^ 40 * 4233742 * 2
def baseEnd_4233742 : Nat := 2173944613127679698654381

theorem tailTrace_4233742 : CollatzResearch.WordTrace tailWord_4233742 prefixEnd_4233742 2173944613127679698654381 := by
  unfold tailWord_4233742
  simp only [CollatzResearch.WordTrace]
  refine ⟨19302157078485409301564935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102944837751922182941679653 19302157078485409301564935)
  ·
    refine ⟨28953235617728113952347403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19302157078485409301564935 28953235617728113952347403)
    ·
      refine ⟨43429853426592170928521105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28953235617728113952347403 43429853426592170928521105)
      ·
        refine ⟨32572390069944128196390829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43429853426592170928521105 32572390069944128196390829)
        ·
          refine ⟨12214646276229048073646561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32572390069944128196390829 12214646276229048073646561)
          ·
            refine ⟨9160984707171786055234921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12214646276229048073646561 9160984707171786055234921)
            ·
              refine ⟨6870738530378839541426191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9160984707171786055234921 6870738530378839541426191)
              ·
                refine ⟨10306107795568259312139287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6870738530378839541426191 10306107795568259312139287)
                ·
                  refine ⟨15459161693352388968208931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10306107795568259312139287 15459161693352388968208931)
                  ·
                    refine ⟨23188742540028583452313397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15459161693352388968208931 23188742540028583452313397)
                    ·
                      refine ⟨2173944613127679698654381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23188742540028583452313397 2173944613127679698654381)
                      ·
                        rfl

theorem cell23_4233742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_4233742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233742 prefixEnd_4233742 := by exact prefixLift 4233742
  have htrace : WordTrace (prefixWord ++ tailWord_4233742) baseStart_4233742 baseEnd_4233742 := by
    simpa [prefixWord, tailWord_4233742, baseEnd_4233742] using wordTrace_append hprefix tailTrace_4233742
  have hstable : (prefixWord ++ tailWord_4233742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233742).length < 2 ^ (prefixWord ++ tailWord_4233742).sum := by decide
  have hdescent : baseEnd_4233742 < baseStart_4233742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233756 : List Nat := [2, 2, 3, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_4233756 : Nat := 118140960795 + 4233756 * 2 ^ 59
def prefixEnd_4233756 : Nat := 4983230072969 + 3 ^ 40 * 4233756 * 2
def baseEnd_4233756 : Nat := 2173951801856842643879317

theorem tailTrace_4233756 : CollatzResearch.WordTrace tailWord_4233756 prefixEnd_4233756 2173951801856842643879317 := by
  unfold tailWord_4233756
  simp only [CollatzResearch.WordTrace]
  refine ⟨77208883624916277401764561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102945178166555036535686081 77208883624916277401764561)
  ·
    refine ⟨57906662718687208051323421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77208883624916277401764561 57906662718687208051323421)
    ·
      refine ⟨21714998519507703019246283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57906662718687208051323421 21714998519507703019246283)
      ·
        refine ⟨32572497779261554528869425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21714998519507703019246283 32572497779261554528869425)
        ·
          refine ⟨24429373334446165896652069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32572497779261554528869425 24429373334446165896652069)
          ·
            refine ⟨4580507500208656105622263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24429373334446165896652069 4580507500208656105622263)
            ·
              refine ⟨6870761250312984158433395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4580507500208656105622263 6870761250312984158433395)
              ·
                refine ⟨10306141875469476237650093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6870761250312984158433395 10306141875469476237650093)
                ·
                  refine ⟨3864803203301053589118785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10306141875469476237650093 3864803203301053589118785)
                  ·
                    refine ⟨2898602402475790191839089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3864803203301053589118785 2898602402475790191839089)
                    ·
                      refine ⟨2173951801856842643879317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898602402475790191839089 2173951801856842643879317)
                      ·
                        rfl

theorem cell23_4233756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_4233756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233756 prefixEnd_4233756 := by exact prefixLift 4233756
  have htrace : WordTrace (prefixWord ++ tailWord_4233756) baseStart_4233756 baseEnd_4233756 := by
    simpa [prefixWord, tailWord_4233756, baseEnd_4233756] using wordTrace_append hprefix tailTrace_4233756
  have hstable : (prefixWord ++ tailWord_4233756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233756).length < 2 ^ (prefixWord ++ tailWord_4233756).sum := by decide
  have hdescent : baseEnd_4233756 < baseStart_4233756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233815 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 3]
def baseStart_4233815 : Nat := 118140960795 + 4233815 * 2 ^ 59
def prefixEnd_4233815 : Nat := 4983230072969 + 3 ^ 40 * 4233815 * 2
def baseEnd_4233815 : Nat := 2173982097215457913041545

theorem tailTrace_4233815 : CollatzResearch.WordTrace tailWord_4233815 prefixEnd_4233815 2173982097215457913041545 := by
  unfold tailWord_4233815
  simp only [CollatzResearch.WordTrace]
  refine ⟨154419919156618807879926899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102946612771079205253284599 154419919156618807879926899)
  ·
    refine ⟨231629878734928211819890349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154419919156618807879926899 231629878734928211819890349)
    ·
      refine ⟨86861204525598079432458881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231629878734928211819890349 86861204525598079432458881)
      ·
        refine ⟨65145903394198559574344161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86861204525598079432458881 65145903394198559574344161)
        ·
          refine ⟨48859427545648919680758121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65145903394198559574344161 48859427545648919680758121)
          ·
            refine ⟨36644570659236689760568591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48859427545648919680758121 36644570659236689760568591)
            ·
              refine ⟨54966855988855034640852887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36644570659236689760568591 54966855988855034640852887)
              ·
                refine ⟨82450283983282551961279331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54966855988855034640852887 82450283983282551961279331)
                ·
                  refine ⟨123675425974923827941918997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82450283983282551961279331 123675425974923827941918997)
                  ·
                    refine ⟨5797285592574554434777453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 123675425974923827941918997 5797285592574554434777453)
                    ·
                      refine ⟨2173982097215457913041545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5797285592574554434777453 2173982097215457913041545)
                      ·
                        rfl

theorem cell23_4233815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_4233815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233815 prefixEnd_4233815 := by exact prefixLift 4233815
  have htrace : WordTrace (prefixWord ++ tailWord_4233815) baseStart_4233815 baseEnd_4233815 := by
    simpa [prefixWord, tailWord_4233815, baseEnd_4233815] using wordTrace_append hprefix tailTrace_4233815
  have hstable : (prefixWord ++ tailWord_4233815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233815).length < 2 ^ (prefixWord ++ tailWord_4233815).sum := by decide
  have hdescent : baseEnd_4233815 < baseStart_4233815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233825 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_4233825 : Nat := 118140960795 + 4233825 * 2 ^ 59
def prefixEnd_4233825 : Nat := 4983230072969 + 3 ^ 40 * 4233825 * 2
def baseEnd_4233825 : Nat := 2173987232022002873916499

theorem tailTrace_4233825 : CollatzResearch.WordTrace tailWord_4233825 prefixEnd_4233825 2173987232022002873916499 := by
  unfold tailWord_4233825
  simp only [CollatzResearch.WordTrace]
  refine ⟨154420283886582579587790929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102946855924388386391860619 154420283886582579587790929)
  ·
    refine ⟨115815212914936934690843197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154420283886582579587790929 115815212914936934690843197)
    ·
      refine ⟨43430704843101350509066199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115815212914936934690843197 43430704843101350509066199)
      ·
        refine ⟨65146057264652025763599299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43430704843101350509066199 65146057264652025763599299)
        ·
          refine ⟨97719085896978038645398949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65146057264652025763599299 97719085896978038645398949)
          ·
            refine ⟨18322328605683382246012303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97719085896978038645398949 18322328605683382246012303)
            ·
              refine ⟨27483492908525073369018455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18322328605683382246012303 27483492908525073369018455)
              ·
                refine ⟨41225239362787610053527683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27483492908525073369018455 41225239362787610053527683)
                ·
                  refine ⟨61837859044181415080291525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41225239362787610053527683 61837859044181415080291525)
                  ·
                    refine ⟨11594598570784015327554661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61837859044181415080291525 11594598570784015327554661)
                    ·
                      refine ⟨2173987232022002873916499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11594598570784015327554661 2173987232022002873916499)
                      ·
                        rfl

theorem cell23_4233825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_4233825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233825 prefixEnd_4233825 := by exact prefixLift 4233825
  have htrace : WordTrace (prefixWord ++ tailWord_4233825) baseStart_4233825 baseEnd_4233825 := by
    simpa [prefixWord, tailWord_4233825, baseEnd_4233825] using wordTrace_append hprefix tailTrace_4233825
  have hstable : (prefixWord ++ tailWord_4233825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233825).length < 2 ^ (prefixWord ++ tailWord_4233825).sum := by decide
  have hdescent : baseEnd_4233825 < baseStart_4233825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233852 : List Nat := [2, 2, 2, 1, 1, 2, 3, 5, 5]
def baseStart_4233852 : Nat := 118140960795 + 4233852 * 2 ^ 59
def prefixEnd_4233852 : Nat := 4983230072969 + 3 ^ 40 * 4233852 * 2
def baseEnd_4233852 : Nat := 241555677333297140919875

theorem tailTrace_4233852 : CollatzResearch.WordTrace tailWord_4233852 prefixEnd_4233852 241555677333297140919875 := by
  unfold tailWord_4233852
  simp only [CollatzResearch.WordTrace]
  refine ⟨77210634328742381599511905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102947512438323175466015873 77210634328742381599511905)
  ·
    refine ⟨57907975746556786199633929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77210634328742381599511905 57907975746556786199633929)
    ·
      refine ⟨43430981809917589649725447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57907975746556786199633929 43430981809917589649725447)
      ·
        refine ⟨65146472714876384474588171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43430981809917589649725447 65146472714876384474588171)
        ·
          refine ⟨97719709072314576711882257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65146472714876384474588171 97719709072314576711882257)
          ·
            refine ⟨73289781804235932533911693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97719709072314576711882257 73289781804235932533911693)
            ·
              refine ⟨27483668176588474700216885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73289781804235932533911693 27483668176588474700216885)
              ·
                refine ⟨2576593891555169503145333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27483668176588474700216885 2576593891555169503145333)
                ·
                  refine ⟨241555677333297140919875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2576593891555169503145333 241555677333297140919875)
                  ·
                    rfl

theorem cell23_4233852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_4233852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233852 prefixEnd_4233852 := by exact prefixLift 4233852
  have htrace : WordTrace (prefixWord ++ tailWord_4233852) baseStart_4233852 baseEnd_4233852 := by
    simpa [prefixWord, tailWord_4233852, baseEnd_4233852] using wordTrace_append hprefix tailTrace_4233852
  have hstable : (prefixWord ++ tailWord_4233852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233852).length < 2 ^ (prefixWord ++ tailWord_4233852).sum := by decide
  have hdescent : baseEnd_4233852 < baseStart_4233852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4233865 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 4, 5]
def baseStart_4233865 : Nat := 118140960795 + 4233865 * 2 ^ 59
def prefixEnd_4233865 : Nat := 4983230072969 + 3 ^ 40 * 4233865 * 2
def baseEnd_4233865 : Nat := 724669257082727572472105

theorem tailTrace_4233865 : CollatzResearch.WordTrace tailWord_4233865 prefixEnd_4233865 724669257082727572472105 := by
  unfold tailWord_4233865
  simp only [CollatzResearch.WordTrace]
  refine ⟨154421742806437666419247049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102947828537625110946164699 154421742806437666419247049)
  ·
    refine ⟨115816307104828249814435287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154421742806437666419247049 115816307104828249814435287)
    ·
      refine ⟨173724460657242374721652931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115816307104828249814435287 173724460657242374721652931)
      ·
        refine ⟨260586690985863562082479397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173724460657242374721652931 260586690985863562082479397)
        ·
          refine ⟨48860004559849417890464887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 260586690985863562082479397 48860004559849417890464887)
          ·
            refine ⟨73290006839774126835697331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48860004559849417890464887 73290006839774126835697331)
            ·
              refine ⟨109935010259661190253545997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73290006839774126835697331 109935010259661190253545997)
              ·
                refine ⟨41225628847372946345079749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109935010259661190253545997 41225628847372946345079749)
                ·
                  refine ⟨7729805408882427439702453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41225628847372946345079749 7729805408882427439702453)
                  ·
                    refine ⟨724669257082727572472105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7729805408882427439702453 724669257082727572472105)
                    ·
                      rfl

theorem cell23_4233865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_4233865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4233865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4233865 prefixEnd_4233865 := by exact prefixLift 4233865
  have htrace : WordTrace (prefixWord ++ tailWord_4233865) baseStart_4233865 baseEnd_4233865 := by
    simpa [prefixWord, tailWord_4233865, baseEnd_4233865] using wordTrace_append hprefix tailTrace_4233865
  have hstable : (prefixWord ++ tailWord_4233865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4233865).length < 2 ^ (prefixWord ++ tailWord_4233865).sum := by decide
  have hdescent : baseEnd_4233865 < baseStart_4233865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4233865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234013 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_4234013 : Nat := 118140960795 + 4234013 * 2 ^ 59
def prefixEnd_4234013 : Nat := 4983230072969 + 3 ^ 40 * 4234013 * 2
def baseEnd_4234013 : Nat := 2174083766385048138365635

theorem tailTrace_4234013 : CollatzResearch.WordTrace tailWord_4234013 prefixEnd_4234013 2174083766385048138365635 := by
  unfold tailWord_4234013
  simp only [CollatzResearch.WordTrace]
  refine ⟨154427140809901487695634693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102951427206600991797089795 154427140809901487695634693)
  ·
    refine ⟨28955088901856528942931505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154427140809901487695634693 28955088901856528942931505)
    ·
      refine ⟨21716316676392396707198629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28955088901856528942931505 21716316676392396707198629)
      ·
        refine ⟨4071809376823574382599743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21716316676392396707198629 4071809376823574382599743)
        ·
          refine ⟨6107714065235361573899615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4071809376823574382599743 6107714065235361573899615)
          ·
            refine ⟨9161571097853042360849423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6107714065235361573899615 9161571097853042360849423)
            ·
              refine ⟨13742356646779563541274135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9161571097853042360849423 13742356646779563541274135)
              ·
                refine ⟨20613534970169345311911203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13742356646779563541274135 20613534970169345311911203)
                ·
                  refine ⟨30920302455254017967866805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20613534970169345311911203 30920302455254017967866805)
                  ·
                    refine ⟨2898778355180064184487513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30920302455254017967866805 2898778355180064184487513)
                    ·
                      refine ⟨2174083766385048138365635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898778355180064184487513 2174083766385048138365635)
                      ·
                        rfl

theorem cell23_4234013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_4234013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234013 prefixEnd_4234013 := by exact prefixLift 4234013
  have htrace : WordTrace (prefixWord ++ tailWord_4234013) baseStart_4234013 baseEnd_4234013 := by
    simpa [prefixWord, tailWord_4234013, baseEnd_4234013] using wordTrace_append hprefix tailTrace_4234013
  have hstable : (prefixWord ++ tailWord_4234013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234013).length < 2 ^ (prefixWord ++ tailWord_4234013).sum := by decide
  have hdescent : baseEnd_4234013 < baseStart_4234013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234020 : List Nat := [2, 3, 1, 3, 3, 1, 2, 3, 1, 1, 3]
def baseStart_4234020 : Nat := 118140960795 + 4234020 * 2 ^ 59
def prefixEnd_4234020 : Nat := 4983230072969 + 3 ^ 40 * 4234020 * 2
def baseEnd_4234020 : Nat := 2174087360749629610978103

theorem tailTrace_4234020 : CollatzResearch.WordTrace tailWord_4234020 prefixEnd_4234020 2174087360749629610978103 := by
  unfold tailWord_4234020
  simp only [CollatzResearch.WordTrace]
  refine ⟨77213698060438063945569757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102951597413917418594093009 77213698060438063945569757)
  ·
    refine ⟨28955136772664273979588659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77213698060438063945569757 28955136772664273979588659)
    ·
      refine ⟨43432705158996410969382989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28955136772664273979588659 43432705158996410969382989)
      ·
        refine ⟨16287264434623654113518621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43432705158996410969382989 16287264434623654113518621)
        ·
          refine ⟨6107724162983870292569483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16287264434623654113518621 6107724162983870292569483)
          ·
            refine ⟨9161586244475805438854225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6107724162983870292569483 9161586244475805438854225)
            ·
              refine ⟨6871189683356854079140669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9161586244475805438854225 6871189683356854079140669)
              ·
                refine ⟨2576696131258820279677751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6871189683356854079140669 2576696131258820279677751)
                ·
                  refine ⟨3865044196888230419516627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2576696131258820279677751 3865044196888230419516627)
                  ·
                    refine ⟨5797566295332345629274941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3865044196888230419516627 5797566295332345629274941)
                    ·
                      refine ⟨2174087360749629610978103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5797566295332345629274941 2174087360749629610978103)
                      ·
                        rfl

theorem cell23_4234020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_4234020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234020 prefixEnd_4234020 := by exact prefixLift 4234020
  have htrace : WordTrace (prefixWord ++ tailWord_4234020) baseStart_4234020 baseEnd_4234020 := by
    simpa [prefixWord, tailWord_4234020, baseEnd_4234020] using wordTrace_append hprefix tailTrace_4234020
  have hstable : (prefixWord ++ tailWord_4234020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234020).length < 2 ^ (prefixWord ++ tailWord_4234020).sum := by decide
  have hdescent : baseEnd_4234020 < baseStart_4234020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234046 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_4234046 : Nat := 118140960795 + 4234046 * 2 ^ 59
def prefixEnd_4234046 : Nat := 4983230072969 + 3 ^ 40 * 4234046 * 2
def baseEnd_4234046 : Nat := 2174100711246646509252983

theorem tailTrace_4234046 : CollatzResearch.WordTrace tailWord_4234046 prefixEnd_4234046 2174100711246646509252983 := by
  unfold tailWord_4234046
  simp only [CollatzResearch.WordTrace]
  refine ⟨19303543052347741791448249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102952229612521289554390661 19303543052347741791448249)
  ·
    refine ⟨14477657289260806343586187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19303543052347741791448249 14477657289260806343586187)
    ·
      refine ⟨21716485933891209515379281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14477657289260806343586187 21716485933891209515379281)
      ·
        refine ⟨16287364450418407136534461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21716485933891209515379281 16287364450418407136534461)
        ·
          refine ⟨6107761668906902676200423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16287364450418407136534461 6107761668906902676200423)
          ·
            refine ⟨9161642503360354014300635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6107761668906902676200423 9161642503360354014300635)
            ·
              refine ⟨13742463755040531021450953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9161642503360354014300635 13742463755040531021450953)
              ·
                refine ⟨10306847816280398266088215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13742463755040531021450953 10306847816280398266088215)
                ·
                  refine ⟨15460271724420597399132323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10306847816280398266088215 15460271724420597399132323)
                  ·
                    refine ⟨23190407586630896098698485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15460271724420597399132323 23190407586630896098698485)
                    ·
                      refine ⟨2174100711246646509252983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23190407586630896098698485 2174100711246646509252983)
                      ·
                        rfl

theorem cell23_4234046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_4234046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234046 prefixEnd_4234046 := by exact prefixLift 4234046
  have htrace : WordTrace (prefixWord ++ tailWord_4234046) baseStart_4234046 baseEnd_4234046 := by
    simpa [prefixWord, tailWord_4234046, baseEnd_4234046] using wordTrace_append hprefix tailTrace_4234046
  have hstable : (prefixWord ++ tailWord_4234046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234046).length < 2 ^ (prefixWord ++ tailWord_4234046).sum := by decide
  have hdescent : baseEnd_4234046 < baseStart_4234046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234062 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 2, 7]
def baseStart_4234062 : Nat := 118140960795 + 4234062 * 2 ^ 59
def prefixEnd_4234062 : Nat := 4983230072969 + 3 ^ 40 * 4234062 * 2
def baseEnd_4234062 : Nat := 724702975645706148884303

theorem tailTrace_4234062 : CollatzResearch.WordTrace tailWord_4234062 prefixEnd_4234062 724702975645706148884303 := by
  unfold tailWord_4234062
  simp only [CollatzResearch.WordTrace]
  refine ⟨19303615998340496133021055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102952618657815979376112293 19303615998340496133021055)
  ·
    refine ⟨28955423997510744199531583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19303615998340496133021055 28955423997510744199531583)
    ·
      refine ⟨43433135996266116299297375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28955423997510744199531583 43433135996266116299297375)
      ·
        refine ⟨65149703994399174448946063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43433135996266116299297375 65149703994399174448946063)
        ·
          refine ⟨97724555991598761673419095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65149703994399174448946063 97724555991598761673419095)
          ·
            refine ⟨146586833987398142510128643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97724555991598761673419095 146586833987398142510128643)
            ·
              refine ⟨219880250981097213765192965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146586833987398142510128643 219880250981097213765192965)
              ·
                refine ⟨41227547058955727580973681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 219880250981097213765192965 41227547058955727580973681)
                ·
                  refine ⟨30920660294216795685730261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41227547058955727580973681 30920660294216795685730261)
                  ·
                    refine ⟨724702975645706148884303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30920660294216795685730261 724702975645706148884303)
                    ·
                      rfl

theorem cell23_4234062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_4234062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234062 prefixEnd_4234062 := by exact prefixLift 4234062
  have htrace : WordTrace (prefixWord ++ tailWord_4234062) baseStart_4234062 baseEnd_4234062 := by
    simpa [prefixWord, tailWord_4234062, baseEnd_4234062] using wordTrace_append hprefix tailTrace_4234062
  have hstable : (prefixWord ++ tailWord_4234062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234062).length < 2 ^ (prefixWord ++ tailWord_4234062).sum := by decide
  have hdescent : baseEnd_4234062 < baseStart_4234062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234094 : List Nat := [4, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2]
def baseStart_4234094 : Nat := 118140960795 + 4234094 * 2 ^ 59
def prefixEnd_4234094 : Nat := 4983230072969 + 3 ^ 40 * 4234094 * 2
def baseEnd_4234094 : Nat := 2174125358318062321452763

theorem tailTrace_4234094 : CollatzResearch.WordTrace tailWord_4234094 prefixEnd_4234094 2174125358318062321452763 := by
  unfold tailWord_4234094
  simp only [CollatzResearch.WordTrace]
  refine ⟨19303761890326004816166667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102953396748405359019555557 19303761890326004816166667)
  ·
    refine ⟨28955642835489007224250001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19303761890326004816166667 28955642835489007224250001)
    ·
      refine ⟨21716732126616755418187501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28955642835489007224250001 21716732126616755418187501)
      ·
        refine ⟨8143774547481283281820313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21716732126616755418187501 8143774547481283281820313)
        ·
          refine ⟨6107830910610962461365235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8143774547481283281820313 6107830910610962461365235)
          ·
            refine ⟨9161746365916443692047853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6107830910610962461365235 9161746365916443692047853)
            ·
              refine ⟨3435654887218666384517945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9161746365916443692047853 3435654887218666384517945)
              ·
                refine ⟨2576741165413999788388459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3435654887218666384517945 2576741165413999788388459)
                ·
                  refine ⟨3865111748120999682582689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2576741165413999788388459 3865111748120999682582689)
                  ·
                    refine ⟨2898833811090749761937017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3865111748120999682582689 2898833811090749761937017)
                    ·
                      refine ⟨2174125358318062321452763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898833811090749761937017 2174125358318062321452763)
                      ·
                        rfl

theorem cell23_4234094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_4234094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234094 prefixEnd_4234094 := by exact prefixLift 4234094
  have htrace : WordTrace (prefixWord ++ tailWord_4234094) baseStart_4234094 baseEnd_4234094 := by
    simpa [prefixWord, tailWord_4234094, baseEnd_4234094] using wordTrace_append hprefix tailTrace_4234094
  have hstable : (prefixWord ++ tailWord_4234094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234094).length < 2 ^ (prefixWord ++ tailWord_4234094).sum := by decide
  have hdescent : baseEnd_4234094 < baseStart_4234094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234114 : List Nat := [3, 4, 2, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4234114 : Nat := 118140960795 + 4234114 * 2 ^ 59
def prefixEnd_4234114 : Nat := 4983230072969 + 3 ^ 40 * 4234114 * 2
def baseEnd_4234114 : Nat := 2174135627931152243202671

theorem tailTrace_4234114 : CollatzResearch.WordTrace tailWord_4234114 prefixEnd_4234114 2174135627931152243202671 := by
  unfold tailWord_4234114
  simp only [CollatzResearch.WordTrace]
  refine ⟨38607706145633895486265349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102953883055023721296707597 38607706145633895486265349)
  ·
    refine ⟨7238944902306355403674753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38607706145633895486265349 7238944902306355403674753)
    ·
      refine ⟨5429208676729766552756065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7238944902306355403674753 5429208676729766552756065)
      ·
        refine ⟨4071906507547324914567049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5429208676729766552756065 4071906507547324914567049)
        ·
          refine ⟨3053929880660493685925287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4071906507547324914567049 3053929880660493685925287)
          ·
            refine ⟨4580894820990740528887931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3053929880660493685925287 4580894820990740528887931)
            ·
              refine ⟨6871342231486110793331897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4580894820990740528887931 6871342231486110793331897)
              ·
                refine ⟨5153506673614583094998923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6871342231486110793331897 5153506673614583094998923)
                ·
                  refine ⟨7730260010421874642498385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5153506673614583094998923 7730260010421874642498385)
                  ·
                    refine ⟨5797695007816405981873789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7730260010421874642498385 5797695007816405981873789)
                    ·
                      refine ⟨2174135627931152243202671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5797695007816405981873789 2174135627931152243202671)
                      ·
                        rfl

theorem cell23_4234114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4234114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234114 prefixEnd_4234114 := by exact prefixLift 4234114
  have htrace : WordTrace (prefixWord ++ tailWord_4234114) baseStart_4234114 baseEnd_4234114 := by
    simpa [prefixWord, tailWord_4234114, baseEnd_4234114] using wordTrace_append hprefix tailTrace_4234114
  have hstable : (prefixWord ++ tailWord_4234114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234114).length < 2 ^ (prefixWord ++ tailWord_4234114).sum := by decide
  have hdescent : baseEnd_4234114 < baseStart_4234114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234116 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_4234116 : Nat := 118140960795 + 4234116 * 2 ^ 59
def prefixEnd_4234116 : Nat := 4983230072969 + 3 ^ 40 * 4234116 * 2
def baseEnd_4234116 : Nat := 2174136654892461235377661

theorem tailTrace_4234116 : CollatzResearch.WordTrace tailWord_4234116 prefixEnd_4234116 2174136654892461235377661 := by
  unfold tailWord_4234116
  simp only [CollatzResearch.WordTrace]
  refine ⟨77215448764264168143317101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102953931685685557524422801 77215448764264168143317101)
  ·
    refine ⟨28955793286599063053743913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77215448764264168143317101 28955793286599063053743913)
    ·
      refine ⟨21716844964949297290307935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28955793286599063053743913 21716844964949297290307935)
      ·
        refine ⟨32575267447423945935461903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21716844964949297290307935 32575267447423945935461903)
        ·
          refine ⟨48862901171135918903192855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32575267447423945935461903 48862901171135918903192855)
          ·
            refine ⟨73294351756703878354789283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48862901171135918903192855 73294351756703878354789283)
            ·
              refine ⟨109941527635055817532183925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73294351756703878354789283 109941527635055817532183925)
              ·
                refine ⟨10307018215786482893642243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109941527635055817532183925 10307018215786482893642243)
                ·
                  refine ⟨15460527323679724340463365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10307018215786482893642243 15460527323679724340463365)
                  ·
                    refine ⟨2898848873189948313836881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15460527323679724340463365 2898848873189948313836881)
                    ·
                      refine ⟨2174136654892461235377661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898848873189948313836881 2174136654892461235377661)
                      ·
                        rfl

theorem cell23_4234116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_4234116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234116 prefixEnd_4234116 := by exact prefixLift 4234116
  have htrace : WordTrace (prefixWord ++ tailWord_4234116) baseStart_4234116 baseEnd_4234116 := by
    simpa [prefixWord, tailWord_4234116, baseEnd_4234116] using wordTrace_append hprefix tailTrace_4234116
  have hstable : (prefixWord ++ tailWord_4234116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234116).length < 2 ^ (prefixWord ++ tailWord_4234116).sum := by decide
  have hdescent : baseEnd_4234116 < baseStart_4234116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234119 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_4234119 : Nat := 118140960795 + 4234119 * 2 ^ 59
def prefixEnd_4234119 : Nat := 4983230072969 + 3 ^ 40 * 4234119 * 2
def baseEnd_4234119 : Nat := 2174138195334424723640147

theorem tailTrace_4234119 : CollatzResearch.WordTrace tailWord_4234119 prefixEnd_4234119 2174138195334424723640147 := by
  unfold tailWord_4234119
  simp only [CollatzResearch.WordTrace]
  refine ⟨154431006947517467798993411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102954004631678311865995607 154431006947517467798993411)
  ·
    refine ⟨231646510421276201698490117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154431006947517467798993411 231646510421276201698490117)
    ·
      refine ⟨43433720703989287818466897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231646510421276201698490117 43433720703989287818466897)
      ·
        refine ⟨32575290527991965863850173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43433720703989287818466897 32575290527991965863850173)
        ·
          refine ⟨12215733947996987198943815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32575290527991965863850173 12215733947996987198943815)
          ·
            refine ⟨18323600921995480798415723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12215733947996987198943815 18323600921995480798415723)
            ·
              refine ⟨27485401382993221197623585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18323600921995480798415723 27485401382993221197623585)
              ·
                refine ⟨20614051037244915898217689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27485401382993221197623585 20614051037244915898217689)
                ·
                  refine ⟨15460538277933686923663267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20614051037244915898217689 15460538277933686923663267)
                  ·
                    refine ⟨23190807416900530385494901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15460538277933686923663267 23190807416900530385494901)
                    ·
                      refine ⟨2174138195334424723640147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23190807416900530385494901 2174138195334424723640147)
                      ·
                        rfl

theorem cell23_4234119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_4234119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234119 prefixEnd_4234119 := by exact prefixLift 4234119
  have htrace : WordTrace (prefixWord ++ tailWord_4234119) baseStart_4234119 baseEnd_4234119 := by
    simpa [prefixWord, tailWord_4234119, baseEnd_4234119] using wordTrace_append hprefix tailTrace_4234119
  have hstable : (prefixWord ++ tailWord_4234119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234119).length < 2 ^ (prefixWord ++ tailWord_4234119).sum := by decide
  have hdescent : baseEnd_4234119 < baseStart_4234119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234120 : List Nat := [2, 1, 3, 3, 2, 3, 1, 2, 1, 3, 2]
def baseStart_4234120 : Nat := 118140960795 + 4234120 * 2 ^ 59
def prefixEnd_4234120 : Nat := 4983230072969 + 3 ^ 40 * 4234120 * 2
def baseEnd_4234120 : Nat := 2174138708815079219727643

theorem tailTrace_4234120 : CollatzResearch.WordTrace tailWord_4234120 prefixEnd_4234120 2174138708815079219727643 := by
  unfold tailWord_4234120
  simp only [CollatzResearch.WordTrace]
  refine ⟨77215521710256922484889907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102954028947009229979853209 77215521710256922484889907)
  ·
    refine ⟨115823282565385383727334861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77215521710256922484889907 115823282565385383727334861)
    ·
      refine ⟨43433730962019518897750573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115823282565385383727334861 43433730962019518897750573)
      ·
        refine ⟨16287649110757319586656465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43433730962019518897750573 16287649110757319586656465)
        ·
          refine ⟨12215736833067989689992349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16287649110757319586656465 12215736833067989689992349)
          ·
            refine ⟨4580901312400496133747131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12215736833067989689992349 4580901312400496133747131)
            ·
              refine ⟨6871351968600744200620697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4580901312400496133747131 6871351968600744200620697)
              ·
                refine ⟨5153513976450558150465523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6871351968600744200620697 5153513976450558150465523)
                ·
                  refine ⟨7730270964675837225698285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5153513976450558150465523 7730270964675837225698285)
                  ·
                    refine ⟨2898851611753438959636857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7730270964675837225698285 2898851611753438959636857)
                    ·
                      refine ⟨2174138708815079219727643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898851611753438959636857 2174138708815079219727643)
                      ·
                        rfl

theorem cell23_4234120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_4234120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234120 prefixEnd_4234120 := by exact prefixLift 4234120
  have htrace : WordTrace (prefixWord ++ tailWord_4234120) baseStart_4234120 baseEnd_4234120 := by
    simpa [prefixWord, tailWord_4234120, baseEnd_4234120] using wordTrace_append hprefix tailTrace_4234120
  have hstable : (prefixWord ++ tailWord_4234120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234120).length < 2 ^ (prefixWord ++ tailWord_4234120).sum := by decide
  have hdescent : baseEnd_4234120 < baseStart_4234120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234216 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 3, 4]
def baseStart_4234216 : Nat := 118140960795 + 4234216 * 2 ^ 59
def prefixEnd_4234216 : Nat := 4983230072969 + 3 ^ 40 * 4234216 * 2
def baseEnd_4234216 : Nat := 724729334319303614709067

theorem tailTrace_4234216 : CollatzResearch.WordTrace tailWord_4234216 prefixEnd_4234216 724729334319303614709067 := by
  unfold tailWord_4234216
  simp only [CollatzResearch.WordTrace]
  refine ⟨77217272414083026682637251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102956363218777368910183001 77217272414083026682637251)
  ·
    refine ⟨115825908621124540023955877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77217272414083026682637251 115825908621124540023955877)
    ·
      refine ⟨21717357866460851254491727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115825908621124540023955877 21717357866460851254491727)
      ·
        refine ⟨32576036799691276881737591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21717357866460851254491727 32576036799691276881737591)
        ·
          refine ⟨48864055199536915322606387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32576036799691276881737591 48864055199536915322606387)
          ·
            refine ⟨73296082799305372983909581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48864055199536915322606387 73296082799305372983909581)
            ·
              refine ⟨27486031049739514868966093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73296082799305372983909581 27486031049739514868966093)
              ·
                refine ⟨10307261643652318075862285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27486031049739514868966093 10307261643652318075862285)
                ·
                  refine ⟨3865223116369619278448357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10307261643652318075862285 3865223116369619278448357)
                  ·
                    refine ⟨724729334319303614709067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3865223116369619278448357 724729334319303614709067)
                    ·
                      rfl

theorem cell23_4234216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_4234216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234216 prefixEnd_4234216 := by exact prefixLift 4234216
  have htrace : WordTrace (prefixWord ++ tailWord_4234216) baseStart_4234216 baseEnd_4234216 := by
    simpa [prefixWord, tailWord_4234216, baseEnd_4234216] using wordTrace_append hprefix tailTrace_4234216
  have hstable : (prefixWord ++ tailWord_4234216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234216).length < 2 ^ (prefixWord ++ tailWord_4234216).sum := by decide
  have hdescent : baseEnd_4234216 < baseStart_4234216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234250 : List Nat := [3, 1, 2, 2, 3, 1, 3, 3, 1, 4]
def baseStart_4234250 : Nat := 118140960795 + 4234250 * 2 ^ 59
def prefixEnd_4234250 : Nat := 4983230072969 + 3 ^ 40 * 4234250 * 2
def baseEnd_4234250 : Nat := 724735153766721237034015

theorem tailTrace_4234250 : CollatzResearch.WordTrace tailWord_4234250 prefixEnd_4234250 724735153766721237034015 := by
  unfold tailWord_4234250
  simp only [CollatzResearch.WordTrace]
  refine ⟨38608946227510719293003051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102957189940028584781341469 38608946227510719293003051)
  ·
    refine ⟨57913419341266078939504577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38608946227510719293003051 57913419341266078939504577)
    ·
      refine ⟨43435064505949559204628433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57913419341266078939504577 43435064505949559204628433)
      ·
        refine ⟨32576298379462169403471325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43435064505949559204628433 32576298379462169403471325)
        ·
          refine ⟨12216111892298313526301747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32576298379462169403471325 12216111892298313526301747)
          ·
            refine ⟨18324167838447470289452621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12216111892298313526301747 18324167838447470289452621)
            ·
              refine ⟨6871562939417801358544733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18324167838447470289452621 6871562939417801358544733)
              ·
                refine ⟨2576836102281675509454275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6871562939417801358544733 2576836102281675509454275)
                ·
                  refine ⟨3865254153422513264181413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2576836102281675509454275 3865254153422513264181413)
                  ·
                    refine ⟨724735153766721237034015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3865254153422513264181413 724735153766721237034015)
                    ·
                      rfl

theorem cell23_4234250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_4234250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234250 prefixEnd_4234250 := by exact prefixLift 4234250
  have htrace : WordTrace (prefixWord ++ tailWord_4234250) baseStart_4234250 baseEnd_4234250 := by
    simpa [prefixWord, tailWord_4234250, baseEnd_4234250] using wordTrace_append hprefix tailTrace_4234250
  have hstable : (prefixWord ++ tailWord_4234250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234250).length < 2 ^ (prefixWord ++ tailWord_4234250).sum := by decide
  have hdescent : baseEnd_4234250 < baseStart_4234250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234259 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 5, 5]
def baseStart_4234259 : Nat := 118140960795 + 4234259 * 2 ^ 59
def prefixEnd_4234259 : Nat := 4983230072969 + 3 ^ 40 * 4234259 * 2
def baseEnd_4234259 : Nat := 724736694208684725296501

theorem tailTrace_4234259 : CollatzResearch.WordTrace tailWord_4234259 prefixEnd_4234259 724736694208684725296501 := by
  unfold tailWord_4234259
  simp only [CollatzResearch.WordTrace]
  refine ⟨154436113167010271709089831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102957408778006847806059887 154436113167010271709089831)
  ·
    refine ⟨231654169750515407563634747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154436113167010271709089831 231654169750515407563634747)
    ·
      refine ⟨347481254625773111345452121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231654169750515407563634747 347481254625773111345452121)
      ·
        refine ⟨260610940969329833509089091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347481254625773111345452121 260610940969329833509089091)
        ·
          refine ⟨390916411453994750263633637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260610940969329833509089091 390916411453994750263633637)
          ·
            refine ⟨73296827147624015674431307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 390916411453994750263633637 73296827147624015674431307)
            ·
              refine ⟨109945240721436023511646961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73296827147624015674431307 109945240721436023511646961)
              ·
                refine ⟨82458930541077017633735221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109945240721436023511646961 82458930541077017633735221)
                ·
                  refine ⟨7730524738225970403162677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82458930541077017633735221 7730524738225970403162677)
                  ·
                    refine ⟨724736694208684725296501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7730524738225970403162677 724736694208684725296501)
                    ·
                      rfl

theorem cell23_4234259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 5].length) (baseStart_4234259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234259 prefixEnd_4234259 := by exact prefixLift 4234259
  have htrace : WordTrace (prefixWord ++ tailWord_4234259) baseStart_4234259 baseEnd_4234259 := by
    simpa [prefixWord, tailWord_4234259, baseEnd_4234259] using wordTrace_append hprefix tailTrace_4234259
  have hstable : (prefixWord ++ tailWord_4234259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234259).length < 2 ^ (prefixWord ++ tailWord_4234259).sum := by decide
  have hdescent : baseEnd_4234259 < baseStart_4234259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234300 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 2, 3, 2]
def baseStart_4234300 : Nat := 118140960795 + 4234300 * 2 ^ 59
def prefixEnd_4234300 : Nat := 4983230072969 + 3 ^ 40 * 4234300 * 2
def baseEnd_4234300 : Nat := 2174231135332888515476815

theorem tailTrace_4234300 : CollatzResearch.WordTrace tailWord_4234300 prefixEnd_4234300 2174231135332888515476815 := by
  unfold tailWord_4234300
  simp only [CollatzResearch.WordTrace]
  refine ⟨77218804279930867855666177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102958405706574490474221569 77218804279930867855666177)
  ·
    refine ⟨57914103209948150891749633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77218804279930867855666177 57914103209948150891749633)
    ·
      refine ⟨43435577407461113168812225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57914103209948150891749633 43435577407461113168812225)
      ·
        refine ⟨32576683055595834876609169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43435577407461113168812225 32576683055595834876609169)
        ·
          refine ⟨24432512291696876157456877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32576683055595834876609169 24432512291696876157456877)
          ·
            refine ⟨9162192109386328559046329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24432512291696876157456877 9162192109386328559046329)
            ·
              refine ⟨6871644082039746419284747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9162192109386328559046329 6871644082039746419284747)
              ·
                refine ⟨10307466123059619628927121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6871644082039746419284747 10307466123059619628927121)
                ·
                  refine ⟨7730599592294714721695341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10307466123059619628927121 7730599592294714721695341)
                  ·
                    refine ⟨2898974847110518020635753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7730599592294714721695341 2898974847110518020635753)
                    ·
                      refine ⟨2174231135332888515476815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898974847110518020635753 2174231135332888515476815)
                      ·
                        rfl

theorem cell23_4234300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_4234300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234300 prefixEnd_4234300 := by exact prefixLift 4234300
  have htrace : WordTrace (prefixWord ++ tailWord_4234300) baseStart_4234300 baseEnd_4234300 := by
    simpa [prefixWord, tailWord_4234300, baseEnd_4234300] using wordTrace_append hprefix tailTrace_4234300
  have hstable : (prefixWord ++ tailWord_4234300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234300).length < 2 ^ (prefixWord ++ tailWord_4234300).sum := by decide
  have hdescent : baseEnd_4234300 < baseStart_4234300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234313 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 7, 2, 2]
def baseStart_4234313 : Nat := 118140960795 + 4234313 * 2 ^ 59
def prefixEnd_4234313 : Nat := 4983230072969 + 3 ^ 40 * 4234313 * 2
def baseEnd_4234313 : Nat := 2174237810581396964614255

theorem tailTrace_4234313 : CollatzResearch.WordTrace tailWord_4234313 prefixEnd_4234313 2174237810581396964614255 := by
  unfold tailWord_4234313
  simp only [CollatzResearch.WordTrace]
  refine ⟨154438082708814638931555593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102958721805876425954370395 154438082708814638931555593)
  ·
    refine ⟨115828562031610979198666695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154438082708814638931555593 115828562031610979198666695)
    ·
      refine ⟨173742843047416468798000043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115828562031610979198666695 173742843047416468798000043)
      ·
        refine ⟨260614264571124703197000065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173742843047416468798000043 260614264571124703197000065)
        ·
          refine ⟨195460698428343527397750049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260614264571124703197000065 195460698428343527397750049)
          ·
            refine ⟨146595523821257645548312537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195460698428343527397750049 146595523821257645548312537)
            ·
              refine ⟨109946642865943234161234403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146595523821257645548312537 109946642865943234161234403)
              ·
                refine ⟨164919964298914851241851605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109946642865943234161234403 164919964298914851241851605)
                ·
                  refine ⟨3865311663255816825980897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 164919964298914851241851605 3865311663255816825980897)
                  ·
                    refine ⟨2898983747441862619485673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3865311663255816825980897 2898983747441862619485673)
                    ·
                      refine ⟨2174237810581396964614255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2898983747441862619485673 2174237810581396964614255)
                      ·
                        rfl

theorem cell23_4234313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 2, 2].length) (baseStart_4234313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234313 prefixEnd_4234313 := by exact prefixLift 4234313
  have htrace : WordTrace (prefixWord ++ tailWord_4234313) baseStart_4234313 baseEnd_4234313 := by
    simpa [prefixWord, tailWord_4234313, baseEnd_4234313] using wordTrace_append hprefix tailTrace_4234313
  have hstable : (prefixWord ++ tailWord_4234313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234313).length < 2 ^ (prefixWord ++ tailWord_4234313).sum := by decide
  have hdescent : baseEnd_4234313 < baseStart_4234313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234329 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_4234329 : Nat := 118140960795 + 4234329 * 2 ^ 59
def prefixEnd_4234329 : Nat := 4983230072969 + 3 ^ 40 * 4234329 * 2
def baseEnd_4234329 : Nat := 2174246026271868902014181

theorem tailTrace_4234329 : CollatzResearch.WordTrace tailWord_4234329 prefixEnd_4234329 2174246026271868902014181 := by
  unfold tailWord_4234329
  simp only [CollatzResearch.WordTrace]
  refine ⟨154438666276756673664138041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102959110851171115776092027 154438666276756673664138041)
  ·
    refine ⟨115828999707567505248103531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154438666276756673664138041 115828999707567505248103531)
    ·
      refine ⟨173743499561351257872155297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115828999707567505248103531 173743499561351257872155297)
      ·
        refine ⟨130307624671013443404116473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173743499561351257872155297 130307624671013443404116473)
        ·
          refine ⟨97730718503260082553087355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130307624671013443404116473 97730718503260082553087355)
          ·
            refine ⟨146596077754890123829631033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97730718503260082553087355 146596077754890123829631033)
            ·
              refine ⟨109947058316167592872223275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146596077754890123829631033 109947058316167592872223275)
              ·
                refine ⟨164920587474251389308334913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109947058316167592872223275 164920587474251389308334913)
                ·
                  refine ⟨123690440605688541981251185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164920587474251389308334913 123690440605688541981251185)
                  ·
                    refine ⟨92767830454266406485938389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123690440605688541981251185 92767830454266406485938389)
                    ·
                      refine ⟨2174246026271868902014181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92767830454266406485938389 2174246026271868902014181)
                      ·
                        rfl

theorem cell23_4234329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_4234329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234329 prefixEnd_4234329 := by exact prefixLift 4234329
  have htrace : WordTrace (prefixWord ++ tailWord_4234329) baseStart_4234329 baseEnd_4234329 := by
    simpa [prefixWord, tailWord_4234329, baseEnd_4234329] using wordTrace_append hprefix tailTrace_4234329
  have hstable : (prefixWord ++ tailWord_4234329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234329).length < 2 ^ (prefixWord ++ tailWord_4234329).sum := by decide
  have hdescent : baseEnd_4234329 < baseStart_4234329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234343 : List Nat := [1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_4234343 : Nat := 118140960795 + 4234343 * 2 ^ 59
def prefixEnd_4234343 : Nat := 4983230072969 + 3 ^ 40 * 4234343 * 2
def baseEnd_4234343 : Nat := 2174253215001031847239117

theorem tailTrace_4234343 : CollatzResearch.WordTrace tailWord_4234343 prefixEnd_4234343 2174253215001031847239117 := by
  unfold tailWord_4234343
  simp only [CollatzResearch.WordTrace]
  refine ⟨154439176898705954055147683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102959451265803969370098455 154439176898705954055147683)
  ·
    refine ⟨231658765348058931082721525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154439176898705954055147683 231658765348058931082721525)
    ·
      refine ⟨21718009251380524789005143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 231658765348058931082721525 21718009251380524789005143)
      ·
        refine ⟨32577013877070787183507715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21718009251380524789005143 32577013877070787183507715)
        ·
          refine ⟨48865520815606180775261573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32577013877070787183507715 48865520815606180775261573)
          ·
            refine ⟨9162285152926158895361545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48865520815606180775261573 9162285152926158895361545)
            ·
              refine ⟨6871713864694619171521159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9162285152926158895361545 6871713864694619171521159)
              ·
                refine ⟨10307570797041928757281739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6871713864694619171521159 10307570797041928757281739)
                ·
                  refine ⟨15461356195562893135922609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10307570797041928757281739 15461356195562893135922609)
                  ·
                    refine ⟨11596017146672169851941957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15461356195562893135922609 11596017146672169851941957)
                    ·
                      refine ⟨2174253215001031847239117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11596017146672169851941957 2174253215001031847239117)
                      ·
                        rfl

theorem cell23_4234343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_4234343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234343 prefixEnd_4234343 := by exact prefixLift 4234343
  have htrace : WordTrace (prefixWord ++ tailWord_4234343) baseStart_4234343 baseEnd_4234343 := by
    simpa [prefixWord, tailWord_4234343, baseEnd_4234343] using wordTrace_append hprefix tailTrace_4234343
  have hstable : (prefixWord ++ tailWord_4234343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234343).length < 2 ^ (prefixWord ++ tailWord_4234343).sum := by decide
  have hdescent : baseEnd_4234343 < baseStart_4234343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234397 : List Nat := [1, 4, 2, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_4234397 : Nat := 118140960795 + 4234397 * 2 ^ 59
def prefixEnd_4234397 : Nat := 4983230072969 + 3 ^ 40 * 4234397 * 2
def baseEnd_4234397 : Nat := 2174280942956374635963869

theorem tailTrace_4234397 : CollatzResearch.WordTrace tailWord_4234397 prefixEnd_4234397 2174280942956374635963869 := by
  unfold tailWord_4234397
  simp only [CollatzResearch.WordTrace]
  refine ⟨154441146440510321277613445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102960764293673547518408963 154441146440510321277613445)
  ·
    refine ⟨28957714957595685239552521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154441146440510321277613445 28957714957595685239552521)
    ·
      refine ⟨21718286218196763929664391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28957714957595685239552521 21718286218196763929664391)
      ·
        refine ⟨32577429327295145894496587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21718286218196763929664391 32577429327295145894496587)
        ·
          refine ⟨48866143990942718841744881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32577429327295145894496587 48866143990942718841744881)
          ·
            refine ⟨36649607993207039131308661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48866143990942718841744881 36649607993207039131308661)
            ·
              refine ⟨3435900749363159918560187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36649607993207039131308661 3435900749363159918560187)
              ·
                refine ⟨5153851124044739877840281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3435900749363159918560187 5153851124044739877840281)
                ·
                  refine ⟨3865388343033554908380211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5153851124044739877840281 3865388343033554908380211)
                  ·
                    refine ⟨5798082514550332362570317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3865388343033554908380211 5798082514550332362570317)
                    ·
                      refine ⟨2174280942956374635963869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5798082514550332362570317 2174280942956374635963869)
                      ·
                        rfl

theorem cell23_4234397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_4234397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234397 prefixEnd_4234397 := by exact prefixLift 4234397
  have htrace : WordTrace (prefixWord ++ tailWord_4234397) baseStart_4234397 baseEnd_4234397 := by
    simpa [prefixWord, tailWord_4234397, baseEnd_4234397] using wordTrace_append hprefix tailTrace_4234397
  have hstable : (prefixWord ++ tailWord_4234397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234397).length < 2 ^ (prefixWord ++ tailWord_4234397).sum := by decide
  have hdescent : baseEnd_4234397 < baseStart_4234397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234407 : List Nat := [1, 1, 6, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_4234407 : Nat := 118140960795 + 4234407 * 2 ^ 59
def prefixEnd_4234407 : Nat := 4983230072969 + 3 ^ 40 * 4234407 * 2
def baseEnd_4234407 : Nat := 2174286077762919596838823

theorem tailTrace_4234407 : CollatzResearch.WordTrace tailWord_4234407 prefixEnd_4234407 2174286077762919596838823 := by
  unfold tailWord_4234407
  simp only [CollatzResearch.WordTrace]
  refine ⟨154441511170474092985477475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102961007446982728656984983 154441511170474092985477475)
  ·
    refine ⟨231662266755711139478216213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154441511170474092985477475 231662266755711139478216213)
    ·
      refine ⟨10859168754173959663041385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 231662266755711139478216213 10859168754173959663041385)
      ·
        refine ⟨8144376565630469747281039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10859168754173959663041385 8144376565630469747281039)
        ·
          refine ⟨12216564848445704620921559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8144376565630469747281039 12216564848445704620921559)
          ·
            refine ⟨18324847272668556931382339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12216564848445704620921559 18324847272668556931382339)
            ·
              refine ⟨27487270909002835397073509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18324847272668556931382339 27487270909002835397073509)
              ·
                refine ⟨5153863295438031636951283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27487270909002835397073509 5153863295438031636951283)
                ·
                  refine ⟨7730794943157047455426925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5153863295438031636951283 7730794943157047455426925)
                  ·
                    refine ⟨2899048103683892795785097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7730794943157047455426925 2899048103683892795785097)
                    ·
                      refine ⟨2174286077762919596838823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899048103683892795785097 2174286077762919596838823)
                      ·
                        rfl

theorem cell23_4234407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_4234407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234407 prefixEnd_4234407 := by exact prefixLift 4234407
  have htrace : WordTrace (prefixWord ++ tailWord_4234407) baseStart_4234407 baseEnd_4234407 := by
    simpa [prefixWord, tailWord_4234407, baseEnd_4234407] using wordTrace_append hprefix tailTrace_4234407
  have hstable : (prefixWord ++ tailWord_4234407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234407).length < 2 ^ (prefixWord ++ tailWord_4234407).sum := by decide
  have hdescent : baseEnd_4234407 < baseStart_4234407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234494 : List Nat := [4, 2, 2, 1, 1, 4, 2, 2, 5]
def baseStart_4234494 : Nat := 118140960795 + 4234494 * 2 ^ 59
def prefixEnd_4234494 : Nat := 4983230072969 + 3 ^ 40 * 4234494 * 2
def baseEnd_4234494 : Nat := 241592305619984528494547

theorem tailTrace_4234494 : CollatzResearch.WordTrace tailWord_4234494 prefixEnd_4234494 241592305619984528494547 := by
  unfold tailWord_4234494
  simp only [CollatzResearch.WordTrace]
  refine ⟨19305585540144863355486817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102963122880772604562596357 19305585540144863355486817)
  ·
    refine ⟨14479189155108647516615113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19305585540144863355486817 14479189155108647516615113)
    ·
      refine ⟨10859391866331485637461335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14479189155108647516615113 10859391866331485637461335)
      ·
        refine ⟨16289087799497228456192003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10859391866331485637461335 16289087799497228456192003)
        ·
          refine ⟨24433631699245842684288005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16289087799497228456192003 24433631699245842684288005)
          ·
            refine ⟨4581305943608595503304001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24433631699245842684288005 4581305943608595503304001)
            ·
              refine ⟨3435979457706446627478001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4581305943608595503304001 3435979457706446627478001)
              ·
                refine ⟨2576984593279834970608501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3435979457706446627478001 2576984593279834970608501)
                ·
                  refine ⟨241592305619984528494547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2576984593279834970608501 241592305619984528494547)
                  ·
                    rfl

theorem cell23_4234494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_4234494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234494 prefixEnd_4234494 := by exact prefixLift 4234494
  have htrace : WordTrace (prefixWord ++ tailWord_4234494) baseStart_4234494 baseEnd_4234494 := by
    simpa [prefixWord, tailWord_4234494, baseEnd_4234494] using wordTrace_append hprefix tailTrace_4234494
  have hstable : (prefixWord ++ tailWord_4234494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234494).length < 2 ^ (prefixWord ++ tailWord_4234494).sum := by decide
  have hdescent : baseEnd_4234494 < baseStart_4234494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234496 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_4234496 : Nat := 118140960795 + 4234496 * 2 ^ 59
def prefixEnd_4234496 : Nat := 4983230072969 + 3 ^ 40 * 4234496 * 2
def baseEnd_4234496 : Nat := 2174331777541169748625913

theorem tailTrace_4234496 : CollatzResearch.WordTrace tailWord_4234496 prefixEnd_4234496 2174331777541169748625913 := by
  unfold tailWord_4234496
  simp only [CollatzResearch.WordTrace]
  refine ⟨77222378633575830592733671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102963171511434440790311561 77222378633575830592733671)
  ·
    refine ⟨115833567950363745889100507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77222378633575830592733671 115833567950363745889100507)
    ·
      refine ⟨173750351925545618833650761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115833567950363745889100507 173750351925545618833650761)
      ·
        refine ⟨130312763944159214125238071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173750351925545618833650761 130312763944159214125238071)
        ·
          refine ⟨195469145916238821187857107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130312763944159214125238071 195469145916238821187857107)
          ·
            refine ⟨293203718874358231781785661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195469145916238821187857107 293203718874358231781785661)
            ·
              refine ⟨109951394577884336918169623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293203718874358231781785661 109951394577884336918169623)
              ·
                refine ⟨164927091866826505377254435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109951394577884336918169623 164927091866826505377254435)
                ·
                  refine ⟨247390637800239758065881653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164927091866826505377254435 247390637800239758065881653)
                  ·
                    refine ⟨23192872293772477318676405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 247390637800239758065881653 23192872293772477318676405)
                    ·
                      refine ⟨2174331777541169748625913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23192872293772477318676405 2174331777541169748625913)
                      ·
                        rfl

theorem cell23_4234496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_4234496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234496 prefixEnd_4234496 := by exact prefixLift 4234496
  have htrace : WordTrace (prefixWord ++ tailWord_4234496) baseStart_4234496 baseEnd_4234496 := by
    simpa [prefixWord, tailWord_4234496, baseEnd_4234496] using wordTrace_append hprefix tailTrace_4234496
  have hstable : (prefixWord ++ tailWord_4234496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234496).length < 2 ^ (prefixWord ++ tailWord_4234496).sum := by decide
  have hdescent : baseEnd_4234496 < baseStart_4234496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234510 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2]
def baseStart_4234510 : Nat := 118140960795 + 4234510 * 2 ^ 59
def prefixEnd_4234510 : Nat := 4983230072969 + 3 ^ 40 * 4234510 * 2
def baseEnd_4234510 : Nat := 2174338966270332693850849

theorem tailTrace_4234510 : CollatzResearch.WordTrace tailWord_4234510 prefixEnd_4234510 2174338966270332693850849 := by
  unfold tailWord_4234510
  simp only [CollatzResearch.WordTrace]
  refine ⟨19305658486137617697059623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102963511926067294384317989 19305658486137617697059623)
  ·
    refine ⟨28958487729206426545589435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19305658486137617697059623 28958487729206426545589435)
    ·
      refine ⟨43437731593809639818384153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28958487729206426545589435 43437731593809639818384153)
      ·
        refine ⟨32578298695357229863788115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43437731593809639818384153 32578298695357229863788115)
        ·
          refine ⟨48867448043035844795682173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32578298695357229863788115 48867448043035844795682173)
          ·
            refine ⟨18325293016138441798380815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48867448043035844795682173 18325293016138441798380815)
            ·
              refine ⟨27487939524207662697571223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18325293016138441798380815 27487939524207662697571223)
              ·
                refine ⟨41231909286311494046356835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27487939524207662697571223 41231909286311494046356835)
                ·
                  refine ⟨61847863929467241069535253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41231909286311494046356835 61847863929467241069535253)
                  ·
                    refine ⟨2899118621693776925134465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61847863929467241069535253 2899118621693776925134465)
                    ·
                      refine ⟨2174338966270332693850849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899118621693776925134465 2174338966270332693850849)
                      ·
                        rfl

theorem cell23_4234510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_4234510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234510 prefixEnd_4234510 := by exact prefixLift 4234510
  have htrace : WordTrace (prefixWord ++ tailWord_4234510) baseStart_4234510 baseEnd_4234510 := by
    simpa [prefixWord, tailWord_4234510, baseEnd_4234510] using wordTrace_append hprefix tailTrace_4234510
  have hstable : (prefixWord ++ tailWord_4234510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234510).length < 2 ^ (prefixWord ++ tailWord_4234510).sum := by decide
  have hdescent : baseEnd_4234510 < baseStart_4234510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234513 : List Nat := [1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 3]
def baseStart_4234513 : Nat := 118140960795 + 4234513 * 2 ^ 59
def prefixEnd_4234513 : Nat := 4983230072969 + 3 ^ 40 * 4234513 * 2
def baseEnd_4234513 : Nat := 2174340506712296182113335

theorem tailTrace_4234513 : CollatzResearch.WordTrace tailWord_4234513 prefixEnd_4234513 2174340506712296182113335 := by
  unfold tailWord_4234513
  simp only [CollatzResearch.WordTrace]
  refine ⟨154445377308090073088836193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102963584872060048725890795 154445377308090073088836193)
  ·
    refine ⟨115834032981067554816627145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154445377308090073088836193 115834032981067554816627145)
    ·
      refine ⟨86875524735800666112470359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115834032981067554816627145 86875524735800666112470359)
      ·
        refine ⟨130313287103700999168705539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86875524735800666112470359 130313287103700999168705539)
        ·
          refine ⟨195469930655551498753058309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130313287103700999168705539 195469930655551498753058309)
          ·
            refine ⟨36650611997915906016198433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195469930655551498753058309 36650611997915906016198433)
            ·
              refine ⟨27487958998436929512148825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36650611997915906016198433 27487958998436929512148825)
              ·
                refine ⟨20615969248827697134111619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27487958998436929512148825 20615969248827697134111619)
                ·
                  refine ⟨30923953873241545701167429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20615969248827697134111619 30923953873241545701167429)
                  ·
                    refine ⟨5798241351232789818968893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30923953873241545701167429 5798241351232789818968893)
                    ·
                      refine ⟨2174340506712296182113335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5798241351232789818968893 2174340506712296182113335)
                      ·
                        rfl

theorem cell23_4234513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_4234513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234513 prefixEnd_4234513 := by exact prefixLift 4234513
  have htrace : WordTrace (prefixWord ++ tailWord_4234513) baseStart_4234513 baseEnd_4234513 := by
    simpa [prefixWord, tailWord_4234513, baseEnd_4234513] using wordTrace_append hprefix tailTrace_4234513
  have hstable : (prefixWord ++ tailWord_4234513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234513).length < 2 ^ (prefixWord ++ tailWord_4234513).sum := by decide
  have hdescent : baseEnd_4234513 < baseStart_4234513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234520 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 3, 4]
def baseStart_4234520 : Nat := 118140960795 + 4234520 * 2 ^ 59
def prefixEnd_4234520 : Nat := 4983230072969 + 3 ^ 40 * 4234520 * 2
def baseEnd_4234520 : Nat := 724781367025625884908601

theorem tailTrace_4234520 : CollatzResearch.WordTrace tailWord_4234520 prefixEnd_4234520 724781367025625884908601 := by
  unfold tailWord_4234520
  simp only [CollatzResearch.WordTrace]
  refine ⟨77222816309532356642170507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102963755079376475522894009 77222816309532356642170507)
  ·
    refine ⟨115834224464298534963255761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77222816309532356642170507 115834224464298534963255761)
    ·
      refine ⟨86875668348223901222441821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115834224464298534963255761 86875668348223901222441821)
      ·
        refine ⟨32578375630583962958415683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86875668348223901222441821 32578375630583962958415683)
        ·
          refine ⟨48867563445875944437623525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32578375630583962958415683 48867563445875944437623525)
          ·
            refine ⟨9162668146101739582054411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48867563445875944437623525 9162668146101739582054411)
            ·
              refine ⟨13744002219152609373081617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9162668146101739582054411 13744002219152609373081617)
              ·
                refine ⟨10308001664364457029811213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13744002219152609373081617 10308001664364457029811213)
                ·
                  refine ⟨3865500624136671386179205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10308001664364457029811213 3865500624136671386179205)
                  ·
                    refine ⟨724781367025625884908601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3865500624136671386179205 724781367025625884908601)
                    ·
                      rfl

theorem cell23_4234520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_4234520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234520 prefixEnd_4234520 := by exact prefixLift 4234520
  have htrace : WordTrace (prefixWord ++ tailWord_4234520) baseStart_4234520 baseEnd_4234520 := by
    simpa [prefixWord, tailWord_4234520, baseEnd_4234520] using wordTrace_append hprefix tailTrace_4234520
  have hstable : (prefixWord ++ tailWord_4234520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234520).length < 2 ^ (prefixWord ++ tailWord_4234520).sum := by decide
  have hdescent : baseEnd_4234520 < baseStart_4234520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234527 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 4]
def baseStart_4234527 : Nat := 118140960795 + 4234527 * 2 ^ 59
def prefixEnd_4234527 : Nat := 4983230072969 + 3 ^ 40 * 4234527 * 2
def baseEnd_4234527 : Nat := 2174347695441459127338271

theorem tailTrace_4234527 : CollatzResearch.WordTrace tailWord_4234527 prefixEnd_4234527 2174347695441459127338271 := by
  unfold tailWord_4234527
  simp only [CollatzResearch.WordTrace]
  refine ⟨154445887930039353479845835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102963925286692902319897223 154445887930039353479845835)
  ·
    refine ⟨231668831895059030219768753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154445887930039353479845835 231668831895059030219768753)
    ·
      refine ⟨173751623921294272664826565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231668831895059030219768753 173751623921294272664826565)
      ·
        refine ⟨32578429485242676124654981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173751623921294272664826565 32578429485242676124654981)
        ·
          refine ⟨6108455528483001773372809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32578429485242676124654981 6108455528483001773372809)
          ·
            refine ⟨4581341646362251330029607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6108455528483001773372809 4581341646362251330029607)
            ·
              refine ⟨6872012469543376995044411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4581341646362251330029607 6872012469543376995044411)
              ·
                refine ⟨10308018704315065492566617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6872012469543376995044411 10308018704315065492566617)
                ·
                  refine ⟨7731014028236299119424963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10308018704315065492566617 7731014028236299119424963)
                  ·
                    refine ⟨11596521042354448679137445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7731014028236299119424963 11596521042354448679137445)
                    ·
                      refine ⟨2174347695441459127338271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11596521042354448679137445 2174347695441459127338271)
                      ·
                        rfl

theorem cell23_4234527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_4234527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234527 prefixEnd_4234527 := by exact prefixLift 4234527
  have htrace : WordTrace (prefixWord ++ tailWord_4234527) baseStart_4234527 baseEnd_4234527 := by
    simpa [prefixWord, tailWord_4234527, baseEnd_4234527] using wordTrace_append hprefix tailTrace_4234527
  have hstable : (prefixWord ++ tailWord_4234527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234527).length < 2 ^ (prefixWord ++ tailWord_4234527).sum := by decide
  have hdescent : baseEnd_4234527 < baseStart_4234527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234593 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 1, 6]
def baseStart_4234593 : Nat := 118140960795 + 4234593 * 2 ^ 59
def prefixEnd_4234593 : Nat := 4983230072969 + 3 ^ 40 * 4234593 * 2
def baseEnd_4234593 : Nat := 724793861721551956370989

theorem tailTrace_4234593 : CollatzResearch.WordTrace tailWord_4234593 prefixEnd_4234593 724793861721551956370989 := by
  unfold tailWord_4234593
  simp only [CollatzResearch.WordTrace]
  refine ⟨154448295147800246751748433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102965530098533497834498955 154448295147800246751748433)
  ·
    refine ⟨115836221360850185063811325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154448295147800246751748433 115836221360850185063811325)
    ·
      refine ⟨43438583010318819398929247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115836221360850185063811325 43438583010318819398929247)
      ·
        refine ⟨65157874515478229098393871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43438583010318819398929247 65157874515478229098393871)
        ·
          refine ⟨97736811773217343647590807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65157874515478229098393871 97736811773217343647590807)
          ·
            refine ⟨146605217659826015471386211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97736811773217343647590807 146605217659826015471386211)
            ·
              refine ⟨219907826489739023207079317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146605217659826015471386211 219907826489739023207079317)
              ·
                refine ⟨10308179366706516712831843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 219907826489739023207079317 10308179366706516712831843)
                ·
                  refine ⟨15462269050059775069247765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10308179366706516712831843 15462269050059775069247765)
                  ·
                    refine ⟨724793861721551956370989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15462269050059775069247765 724793861721551956370989)
                    ·
                      rfl

theorem cell23_4234593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_4234593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234593 prefixEnd_4234593 := by exact prefixLift 4234593
  have htrace : WordTrace (prefixWord ++ tailWord_4234593) baseStart_4234593 baseEnd_4234593 := by
    simpa [prefixWord, tailWord_4234593, baseEnd_4234593] using wordTrace_append hprefix tailTrace_4234593
  have hstable : (prefixWord ++ tailWord_4234593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234593).length < 2 ^ (prefixWord ++ tailWord_4234593).sum := by decide
  have hdescent : baseEnd_4234593 < baseStart_4234593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234610 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 4, 4]
def baseStart_4234610 : Nat := 118140960795 + 4234610 * 2 ^ 59
def prefixEnd_4234610 : Nat := 4983230072969 + 3 ^ 40 * 4234610 * 2
def baseEnd_4234610 : Nat := 724796771445260767533463

theorem tailTrace_4234610 : CollatzResearch.WordTrace tailWord_4234610 prefixEnd_4234610 724796771445260767533463 := by
  unfold tailWord_4234610
  simp only [CollatzResearch.WordTrace]
  refine ⟨38612228797184664663779321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102965943459159105770078189 38612228797184664663779321)
  ·
    refine ⟨28959171597888498497834491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38612228797184664663779321 28959171597888498497834491)
    ·
      refine ⟨43438757396832747746751737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28959171597888498497834491 43438757396832747746751737)
      ·
        refine ⟨32579068047624560810063803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43438757396832747746751737 32579068047624560810063803)
        ·
          refine ⟨48868602071436841215095705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32579068047624560810063803 48868602071436841215095705)
          ·
            refine ⟨36651451553577630911321779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48868602071436841215095705 36651451553577630911321779)
            ·
              refine ⟨54977177330366446366982669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36651451553577630911321779 54977177330366446366982669)
              ·
                refine ⟨20616441498887417387618501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54977177330366446366982669 20616441498887417387618501)
                ·
                  refine ⟨3865582781041390760178469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20616441498887417387618501 3865582781041390760178469)
                  ·
                    refine ⟨724796771445260767533463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3865582781041390760178469 724796771445260767533463)
                    ·
                      rfl

theorem cell23_4234610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_4234610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234610 prefixEnd_4234610 := by exact prefixLift 4234610
  have htrace : WordTrace (prefixWord ++ tailWord_4234610) baseStart_4234610 baseEnd_4234610 := by
    simpa [prefixWord, tailWord_4234610, baseEnd_4234610] using wordTrace_append hprefix tailTrace_4234610
  have hstable : (prefixWord ++ tailWord_4234610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234610).length < 2 ^ (prefixWord ++ tailWord_4234610).sum := by decide
  have hdescent : baseEnd_4234610 < baseStart_4234610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234620 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_4234620 : Nat := 118140960795 + 4234620 * 2 ^ 59
def prefixEnd_4234620 : Nat := 4983230072969 + 3 ^ 40 * 4234620 * 2
def baseEnd_4234620 : Nat := 2174395449142327263475343

theorem tailTrace_4234620 : CollatzResearch.WordTrace tailWord_4234620 prefixEnd_4234620 2174395449142327263475343 := by
  unfold tailWord_4234620
  simp only [CollatzResearch.WordTrace]
  refine ⟨77224639959351215181490657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102966186612468286908654209 77224639959351215181490657)
  ·
    refine ⟨57918479969513411386117993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77224639959351215181490657 57918479969513411386117993)
    ·
      refine ⟨43438859977135058539588495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57918479969513411386117993 43438859977135058539588495)
      ·
        refine ⟨65158289965702587809382743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43438859977135058539588495 65158289965702587809382743)
        ·
          refine ⟨97737434948553881714074115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65158289965702587809382743 97737434948553881714074115)
          ·
            refine ⟨146606152422830822571111173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97737434948553881714074115 146606152422830822571111173)
            ·
              refine ⟨27488653579280779232083345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146606152422830822571111173 27488653579280779232083345)
              ·
                refine ⟨20616490184460584424062509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27488653579280779232083345 20616490184460584424062509)
                ·
                  refine ⟨7731183819172719159023441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20616490184460584424062509 7731183819172719159023441)
                  ·
                    refine ⟨5798387864379539369267581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7731183819172719159023441 5798387864379539369267581)
                    ·
                      refine ⟨2174395449142327263475343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5798387864379539369267581 2174395449142327263475343)
                      ·
                        rfl

theorem cell23_4234620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_4234620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234620 prefixEnd_4234620 := by exact prefixLift 4234620
  have htrace : WordTrace (prefixWord ++ tailWord_4234620) baseStart_4234620 baseEnd_4234620 := by
    simpa [prefixWord, tailWord_4234620, baseEnd_4234620] using wordTrace_append hprefix tailTrace_4234620
  have hstable : (prefixWord ++ tailWord_4234620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234620).length < 2 ^ (prefixWord ++ tailWord_4234620).sum := by decide
  have hdescent : baseEnd_4234620 < baseStart_4234620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234627 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 2, 4]
def baseStart_4234627 : Nat := 118140960795 + 4234627 * 2 ^ 59
def prefixEnd_4234627 : Nat := 4983230072969 + 3 ^ 40 * 4234627 * 2
def baseEnd_4234627 : Nat := 724799681168969578695937

theorem tailTrace_4234627 : CollatzResearch.WordTrace tailWord_4234627 prefixEnd_4234627 724799681168969578695937 := by
  unfold tailWord_4234627
  simp only [CollatzResearch.WordTrace]
  refine ⟨154449535229677070558486135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102966356819784713705657423 154449535229677070558486135)
  ·
    refine ⟨231674302844515605837729203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154449535229677070558486135 231674302844515605837729203)
    ·
      refine ⟨347511454266773408756593805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231674302844515605837729203 347511454266773408756593805)
      ·
        refine ⟨130316795350040028283722677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347511454266773408756593805 130316795350040028283722677)
        ·
          refine ⟨12217199564066252651599001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130316795350040028283722677 12217199564066252651599001)
          ·
            refine ⟨9162899673049689488699251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12217199564066252651599001 9162899673049689488699251)
            ·
              refine ⟨13744349509574534233048877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9162899673049689488699251 13744349509574534233048877)
              ·
                refine ⟨5154131066090450337393329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13744349509574534233048877 5154131066090450337393329)
                ·
                  refine ⟨3865598299567837753044997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5154131066090450337393329 3865598299567837753044997)
                  ·
                    refine ⟨724799681168969578695937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3865598299567837753044997 724799681168969578695937)
                    ·
                      rfl

theorem cell23_4234627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 4].length) (baseStart_4234627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234627 prefixEnd_4234627 := by exact prefixLift 4234627
  have htrace : WordTrace (prefixWord ++ tailWord_4234627) baseStart_4234627 baseEnd_4234627 := by
    simpa [prefixWord, tailWord_4234627, baseEnd_4234627] using wordTrace_append hprefix tailTrace_4234627
  have hstable : (prefixWord ++ tailWord_4234627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234627).length < 2 ^ (prefixWord ++ tailWord_4234627).sum := by decide
  have hdescent : baseEnd_4234627 < baseStart_4234627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234684 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_4234684 : Nat := 118140960795 + 4234684 * 2 ^ 59
def prefixEnd_4234684 : Nat := 4983230072969 + 3 ^ 40 * 4234684 * 2
def baseEnd_4234684 : Nat := 2174428311904215013075049

theorem tailTrace_4234684 : CollatzResearch.WordTrace tailWord_4234684 prefixEnd_4234684 2174428311904215013075049 := by
  unfold tailWord_4234684
  simp only [CollatzResearch.WordTrace]
  refine ⟨77225807095235284646655553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102967742793647046195540737 77225807095235284646655553)
  ·
    refine ⟨57919355321426463484991665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77225807095235284646655553 57919355321426463484991665)
    ·
      refine ⟨43439516491069847613743749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57919355321426463484991665 43439516491069847613743749)
      ·
        refine ⟨8144909342075596427576953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43439516491069847613743749 8144909342075596427576953)
        ·
          refine ⟨6108682006556697320682715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8144909342075596427576953 6108682006556697320682715)
          ·
            refine ⟨9163023009835045981024073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6108682006556697320682715 9163023009835045981024073)
            ·
              refine ⟨6872267257376284485768055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9163023009835045981024073 6872267257376284485768055)
              ·
                refine ⟨10308400886064426728652083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6872267257376284485768055 10308400886064426728652083)
                ·
                  refine ⟨15462601329096640092978125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10308400886064426728652083 15462601329096640092978125)
                  ·
                    refine ⟨5798475498411240034866797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15462601329096640092978125 5798475498411240034866797)
                    ·
                      refine ⟨2174428311904215013075049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5798475498411240034866797 2174428311904215013075049)
                      ·
                        rfl

theorem cell23_4234684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_4234684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234684 prefixEnd_4234684 := by exact prefixLift 4234684
  have htrace : WordTrace (prefixWord ++ tailWord_4234684) baseStart_4234684 baseEnd_4234684 := by
    simpa [prefixWord, tailWord_4234684, baseEnd_4234684] using wordTrace_append hprefix tailTrace_4234684
  have hstable : (prefixWord ++ tailWord_4234684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234684).length < 2 ^ (prefixWord ++ tailWord_4234684).sum := by decide
  have hdescent : baseEnd_4234684 < baseStart_4234684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234741 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_4234741 : Nat := 118140960795 + 4234741 * 2 ^ 59
def prefixEnd_4234741 : Nat := 4983230072969 + 3 ^ 40 * 4234741 * 2
def baseEnd_4234741 : Nat := 2174457580301521290062287

theorem tailTrace_4234741 : CollatzResearch.WordTrace tailWord_4234741 prefixEnd_4234741 2174457580301521290062287 := by
  unfold tailWord_4234741
  simp only [CollatzResearch.WordTrace]
  refine ⟨154453693151264068028136077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102969128767509378685424051 154453693151264068028136077)
  ·
    refine ⟨57920134931724025510551029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154453693151264068028136077 57920134931724025510551029)
    ·
      refine ⟨5430012649849127391614159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57920134931724025510551029 5430012649849127391614159)
      ·
        refine ⟨8145018974773691087421239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5430012649849127391614159 8145018974773691087421239)
        ·
          refine ⟨12217528462160536631131859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8145018974773691087421239 12217528462160536631131859)
          ·
            refine ⟨18326292693240804946697789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12217528462160536631131859 18326292693240804946697789)
            ·
              refine ⟨6872359759965301855011671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18326292693240804946697789 6872359759965301855011671)
              ·
                refine ⟨10308539639947952782517507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6872359759965301855011671 10308539639947952782517507)
                ·
                  refine ⟨15462809459921929173776261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10308539639947952782517507 15462809459921929173776261)
                  ·
                    refine ⟨2899276773735361720083049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15462809459921929173776261 2899276773735361720083049)
                    ·
                      refine ⟨2174457580301521290062287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899276773735361720083049 2174457580301521290062287)
                      ·
                        rfl

theorem cell23_4234741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_4234741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234741 prefixEnd_4234741 := by exact prefixLift 4234741
  have htrace : WordTrace (prefixWord ++ tailWord_4234741) baseStart_4234741 baseEnd_4234741 := by
    simpa [prefixWord, tailWord_4234741, baseEnd_4234741] using wordTrace_append hprefix tailTrace_4234741
  have hstable : (prefixWord ++ tailWord_4234741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234741).length < 2 ^ (prefixWord ++ tailWord_4234741).sum := by decide
  have hdescent : baseEnd_4234741 < baseStart_4234741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234760 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 1, 7]
def baseStart_4234760 : Nat := 118140960795 + 4234760 * 2 ^ 59
def prefixEnd_4234760 : Nat := 4983230072969 + 3 ^ 40 * 4234760 * 2
def baseEnd_4234760 : Nat := 724822445477985571908233

theorem tailTrace_4234760 : CollatzResearch.WordTrace tailWord_4234760 prefixEnd_4234760 724822445477985571908233 := by
  unfold tailWord_4234760
  simp only [CollatzResearch.WordTrace]
  refine ⟨77227193069097617136538867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102969590758796822848718489 77227193069097617136538867)
  ·
    refine ⟨115840789603646425704808301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77227193069097617136538867 115840789603646425704808301)
    ·
      refine ⟨43440296101367409639303113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115840789603646425704808301 43440296101367409639303113)
      ·
        refine ⟨32580222076025557229477335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43440296101367409639303113 32580222076025557229477335)
        ·
          refine ⟨48870333114038335844216003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32580222076025557229477335 48870333114038335844216003)
          ·
            refine ⟨73305499671057503766324005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48870333114038335844216003 73305499671057503766324005)
            ·
              refine ⟨13744781188323281956185751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73305499671057503766324005 13744781188323281956185751)
              ·
                refine ⟨20617171782484922934278627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13744781188323281956185751 20617171782484922934278627)
                ·
                  refine ⟨30925757673727384401417941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20617171782484922934278627 30925757673727384401417941)
                  ·
                    refine ⟨724822445477985571908233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30925757673727384401417941 724822445477985571908233)
                    ·
                      rfl

theorem cell23_4234760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_4234760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234760 prefixEnd_4234760 := by exact prefixLift 4234760
  have htrace : WordTrace (prefixWord ++ tailWord_4234760) baseStart_4234760 baseEnd_4234760 := by
    simpa [prefixWord, tailWord_4234760, baseEnd_4234760] using wordTrace_append hprefix tailTrace_4234760
  have hstable : (prefixWord ++ tailWord_4234760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234760).length < 2 ^ (prefixWord ++ tailWord_4234760).sum := by decide
  have hdescent : baseEnd_4234760 < baseStart_4234760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234787 : List Nat := [1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 5]
def baseStart_4234787 : Nat := 118140960795 + 4234787 * 2 ^ 59
def prefixEnd_4234787 : Nat := 4983230072969 + 3 ^ 40 * 4234787 * 2
def baseEnd_4234787 : Nat := 2174481200411628110087075

theorem tailTrace_4234787 : CollatzResearch.WordTrace tailWord_4234787 prefixEnd_4234787 2174481200411628110087075 := by
  unfold tailWord_4234787
  simp only [CollatzResearch.WordTrace]
  refine ⟨154455370909097417884310615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102970247272731611922873743 154455370909097417884310615)
  ·
    refine ⟨231683056363646126826465923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154455370909097417884310615 231683056363646126826465923)
    ·
      refine ⟨347524584545469190239698885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231683056363646126826465923 347524584545469190239698885)
      ·
        refine ⟨65160859602275473169943541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 347524584545469190239698885 65160859602275473169943541)
        ·
          refine ⟨6108830587713325609682207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65160859602275473169943541 6108830587713325609682207)
          ·
            refine ⟨9163245881569988414523311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6108830587713325609682207 9163245881569988414523311)
            ·
              refine ⟨13744868822354982621784967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9163245881569988414523311 13744868822354982621784967)
              ·
                refine ⟨20617303233532473932677451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13744868822354982621784967 20617303233532473932677451)
                ·
                  refine ⟨30925954850298710899016177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20617303233532473932677451 30925954850298710899016177)
                  ·
                    refine ⟨23194466137724033174262133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30925954850298710899016177 23194466137724033174262133)
                    ·
                      refine ⟨2174481200411628110087075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23194466137724033174262133 2174481200411628110087075)
                      ·
                        rfl

theorem cell23_4234787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_4234787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234787 prefixEnd_4234787 := by exact prefixLift 4234787
  have htrace : WordTrace (prefixWord ++ tailWord_4234787) baseStart_4234787 baseEnd_4234787 := by
    simpa [prefixWord, tailWord_4234787, baseEnd_4234787] using wordTrace_append hprefix tailTrace_4234787
  have hstable : (prefixWord ++ tailWord_4234787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234787).length < 2 ^ (prefixWord ++ tailWord_4234787).sum := by decide
  have hdescent : baseEnd_4234787 < baseStart_4234787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234792 : List Nat := [2, 1, 5, 2, 3, 1, 2, 1, 2, 2, 2]
def baseStart_4234792 : Nat := 118140960795 + 4234792 * 2 ^ 59
def prefixEnd_4234792 : Nat := 4983230072969 + 3 ^ 40 * 4234792 * 2
def baseEnd_4234792 : Nat := 2174483767814900590524553

theorem tailTrace_4234792 : CollatzResearch.WordTrace tailWord_4234792 prefixEnd_4234792 2174483767814900590524553 := by
  unfold tailWord_4234792
  simp only [CollatzResearch.WordTrace]
  refine ⟨77227776637039651869121315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102970368849386202492161753 77227776637039651869121315)
  ·
    refine ⟨115841664955559477803681973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77227776637039651869121315 115841664955559477803681973)
    ·
      refine ⟨10860156089583701044095185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115841664955559477803681973 10860156089583701044095185)
      ·
        refine ⟨8145117067187775783071389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10860156089583701044095185 8145117067187775783071389)
        ·
          refine ⟨3054418900195415918651771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8145117067187775783071389 3054418900195415918651771)
          ·
            refine ⟨4581628350293123877977657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054418900195415918651771 4581628350293123877977657)
            ·
              refine ⟨3436221262719842908483243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4581628350293123877977657 3436221262719842908483243)
              ·
                refine ⟨5154331894079764362724865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3436221262719842908483243 5154331894079764362724865)
                ·
                  refine ⟨3865748920559823272043649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5154331894079764362724865 3865748920559823272043649)
                  ·
                    refine ⟨2899311690419867454032737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3865748920559823272043649 2899311690419867454032737)
                    ·
                      refine ⟨2174483767814900590524553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899311690419867454032737 2174483767814900590524553)
                      ·
                        rfl

theorem cell23_4234792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_4234792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234792 prefixEnd_4234792 := by exact prefixLift 4234792
  have htrace : WordTrace (prefixWord ++ tailWord_4234792) baseStart_4234792 baseEnd_4234792 := by
    simpa [prefixWord, tailWord_4234792, baseEnd_4234792] using wordTrace_append hprefix tailTrace_4234792
  have hstable : (prefixWord ++ tailWord_4234792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234792).length < 2 ^ (prefixWord ++ tailWord_4234792).sum := by decide
  have hdescent : baseEnd_4234792 < baseStart_4234792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234834 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_4234834 : Nat := 118140960795 + 4234834 * 2 ^ 59
def prefixEnd_4234834 : Nat := 4983230072969 + 3 ^ 40 * 4234834 * 2
def baseEnd_4234834 : Nat := 2174505334002389426199359

theorem tailTrace_4234834 : CollatzResearch.WordTrace tailWord_4234834 prefixEnd_4234834 2174505334002389426199359 := by
  unfold tailWord_4234834
  simp only [CollatzResearch.WordTrace]
  refine ⟨38614271284981786227817889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102971390093284763274181037 38614271284981786227817889)
  ·
    refine ⟨28960703463736339670863417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38614271284981786227817889 28960703463736339670863417)
    ·
      refine ⟨21720527597802254753147563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28960703463736339670863417 21720527597802254753147563)
      ·
        refine ⟨32580791396703382129721345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21720527597802254753147563 32580791396703382129721345)
        ·
          refine ⟨24435593547527536597291009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32580791396703382129721345 24435593547527536597291009)
          ·
            refine ⟨18326695160645652447968257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24435593547527536597291009 18326695160645652447968257)
            ·
              refine ⟨13745021370484239335976193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18326695160645652447968257 13745021370484239335976193)
              ·
                refine ⟨10308766027863179501982145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13745021370484239335976193 10308766027863179501982145)
                ·
                  refine ⟨7731574520897384626486609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10308766027863179501982145 7731574520897384626486609)
                  ·
                    refine ⟨5798680890673038469864957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7731574520897384626486609 5798680890673038469864957)
                    ·
                      refine ⟨2174505334002389426199359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5798680890673038469864957 2174505334002389426199359)
                      ·
                        rfl

theorem cell23_4234834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_4234834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234834 prefixEnd_4234834 := by exact prefixLift 4234834
  have htrace : WordTrace (prefixWord ++ tailWord_4234834) baseStart_4234834 baseEnd_4234834 := by
    simpa [prefixWord, tailWord_4234834, baseEnd_4234834] using wordTrace_append hprefix tailTrace_4234834
  have hstable : (prefixWord ++ tailWord_4234834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234834).length < 2 ^ (prefixWord ++ tailWord_4234834).sum := by decide
  have hdescent : baseEnd_4234834 < baseStart_4234834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234840 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_4234840 : Nat := 118140960795 + 4234840 * 2 ^ 59
def prefixEnd_4234840 : Nat := 4983230072969 + 3 ^ 40 * 4234840 * 2
def baseEnd_4234840 : Nat := 2174508414886316402724331

theorem tailTrace_4234840 : CollatzResearch.WordTrace tailWord_4234840 prefixEnd_4234840 2174508414886316402724331 := by
  unfold tailWord_4234840
  simp only [CollatzResearch.WordTrace]
  refine ⟨77228651988952703967994987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102971535985270271957326649 77228651988952703967994987)
  ·
    refine ⟨115842977983429055951992481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77228651988952703967994987 115842977983429055951992481)
    ·
      refine ⟨86882233487571791963994361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115842977983429055951992481 86882233487571791963994361)
      ·
        refine ⟨65161675115678843972995771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86882233487571791963994361 65161675115678843972995771)
        ·
          refine ⟨97742512673518265959493657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65161675115678843972995771 97742512673518265959493657)
          ·
            refine ⟨73306884505138699469620243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97742512673518265959493657 73306884505138699469620243)
            ·
              refine ⟨109960326757708049204430365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73306884505138699469620243 109960326757708049204430365)
              ·
                refine ⟨41235122534140518451661387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109960326757708049204430365 41235122534140518451661387)
                ·
                  refine ⟨61852683801210777677492081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41235122534140518451661387 61852683801210777677492081)
                  ·
                    refine ⟨46389512850908083258119061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61852683801210777677492081 46389512850908083258119061)
                    ·
                      refine ⟨2174508414886316402724331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46389512850908083258119061 2174508414886316402724331)
                      ·
                        rfl

theorem cell23_4234840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_4234840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234840 prefixEnd_4234840 := by exact prefixLift 4234840
  have htrace : WordTrace (prefixWord ++ tailWord_4234840) baseStart_4234840 baseEnd_4234840 := by
    simpa [prefixWord, tailWord_4234840, baseEnd_4234840] using wordTrace_append hprefix tailTrace_4234840
  have hstable : (prefixWord ++ tailWord_4234840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234840).length < 2 ^ (prefixWord ++ tailWord_4234840).sum := by decide
  have hdescent : baseEnd_4234840 < baseStart_4234840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234860 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_4234860 : Nat := 118140960795 + 4234860 * 2 ^ 59
def prefixEnd_4234860 : Nat := 4983230072969 + 3 ^ 40 * 4234860 * 2
def baseEnd_4234860 : Nat := 2174518684499406324474239

theorem tailTrace_4234860 : CollatzResearch.WordTrace tailWord_4234860 prefixEnd_4234860 2174518684499406324474239 := by
  unfold tailWord_4234860
  simp only [CollatzResearch.WordTrace]
  refine ⟨77229016718916475675859017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102972022291888634234478689 77229016718916475675859017)
  ·
    refine ⟨57921762539187356756894263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77229016718916475675859017 57921762539187356756894263)
    ·
      refine ⟨86882643808781035135341395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57921762539187356756894263 86882643808781035135341395)
      ·
        refine ⟨130323965713171552703012093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86882643808781035135341395 130323965713171552703012093)
        ·
          refine ⟨48871487142439332263629535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130323965713171552703012093 48871487142439332263629535)
          ·
            refine ⟨73307230713658998395444303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48871487142439332263629535 73307230713658998395444303)
            ·
              refine ⟨109960846070488497593166455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73307230713658998395444303 109960846070488497593166455)
              ·
                refine ⟨164941269105732746389749683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109960846070488497593166455 164941269105732746389749683)
                ·
                  refine ⟨247411903658599119584624525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164941269105732746389749683 247411903658599119584624525)
                  ·
                    refine ⟨92779463871974669844234197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 247411903658599119584624525 92779463871974669844234197)
                    ·
                      refine ⟨2174518684499406324474239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92779463871974669844234197 2174518684499406324474239)
                      ·
                        rfl

theorem cell23_4234860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_4234860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234860 prefixEnd_4234860 := by exact prefixLift 4234860
  have htrace : WordTrace (prefixWord ++ tailWord_4234860) baseStart_4234860 baseEnd_4234860 := by
    simpa [prefixWord, tailWord_4234860, baseEnd_4234860] using wordTrace_append hprefix tailTrace_4234860
  have hstable : (prefixWord ++ tailWord_4234860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234860).length < 2 ^ (prefixWord ++ tailWord_4234860).sum := by decide
  have hdescent : baseEnd_4234860 < baseStart_4234860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234864 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 5, 1, 3]
def baseStart_4234864 : Nat := 118140960795 + 4234864 * 2 ^ 59
def prefixEnd_4234864 : Nat := 4983230072969 + 3 ^ 40 * 4234864 * 2
def baseEnd_4234864 : Nat := 2174520738422024308824221

theorem tailTrace_4234864 : CollatzResearch.WordTrace tailWord_4234864 prefixEnd_4234864 2174520738422024308824221 := by
  unfold tailWord_4234864
  simp only [CollatzResearch.WordTrace]
  refine ⟨77229089664909230017431823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102972119553212306689909097 77229089664909230017431823)
  ·
    refine ⟨115843634497363845026147735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77229089664909230017431823 115843634497363845026147735)
    ·
      refine ⟨173765451746045767539221603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115843634497363845026147735 173765451746045767539221603)
      ·
        refine ⟨260648177619068651308832405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173765451746045767539221603 260648177619068651308832405)
        ·
          refine ⟨12217883325893843030101519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 260648177619068651308832405 12217883325893843030101519)
          ·
            refine ⟨18326824988840764545152279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12217883325893843030101519 18326824988840764545152279)
            ·
              refine ⟨27490237483261146817728419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18326824988840764545152279 27490237483261146817728419)
              ·
                refine ⟨41235356224891720226592629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27490237483261146817728419 41235356224891720226592629)
                ·
                  refine ⟨3865814646083598771243059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41235356224891720226592629 3865814646083598771243059)
                  ·
                    refine ⟨5798721969125398156864589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3865814646083598771243059 5798721969125398156864589)
                    ·
                      refine ⟨2174520738422024308824221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5798721969125398156864589 2174520738422024308824221)
                      ·
                        rfl

theorem cell23_4234864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 5, 1, 3].length) (baseStart_4234864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234864 prefixEnd_4234864 := by exact prefixLift 4234864
  have htrace : WordTrace (prefixWord ++ tailWord_4234864) baseStart_4234864 baseEnd_4234864 := by
    simpa [prefixWord, tailWord_4234864, baseEnd_4234864] using wordTrace_append hprefix tailTrace_4234864
  have hstable : (prefixWord ++ tailWord_4234864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234864).length < 2 ^ (prefixWord ++ tailWord_4234864).sum := by decide
  have hdescent : baseEnd_4234864 < baseStart_4234864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234874 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2]
def baseStart_4234874 : Nat := 118140960795 + 4234874 * 2 ^ 59
def prefixEnd_4234874 : Nat := 4983230072969 + 3 ^ 40 * 4234874 * 2
def baseEnd_4234874 : Nat := 2174525873228569269699175

theorem tailTrace_4234874 : CollatzResearch.WordTrace tailWord_4234874 prefixEnd_4234874 2174525873228569269699175 := by
  unfold tailWord_4234874
  simp only [CollatzResearch.WordTrace]
  refine ⟨38614636014945557935681919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102972362706521487828485117 38614636014945557935681919)
  ·
    refine ⟨57921954022418336903522879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38614636014945557935681919 57921954022418336903522879)
    ·
      refine ⟨86882931033627505355284319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57921954022418336903522879 86882931033627505355284319)
      ·
        refine ⟨130324396550441258032926479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86882931033627505355284319 130324396550441258032926479)
        ·
          refine ⟨195486594825661887049389719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130324396550441258032926479 195486594825661887049389719)
          ·
            refine ⟨293229892238492830574084579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195486594825661887049389719 293229892238492830574084579)
            ·
              refine ⟨439844838357739245861126869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293229892238492830574084579 439844838357739245861126869)
              ·
                refine ⟨10308863399009513574870161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 439844838357739245861126869 10308863399009513574870161)
                ·
                  refine ⟨7731647549257135181152621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10308863399009513574870161 7731647549257135181152621)
                  ·
                    refine ⟨2899367830971425692932233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7731647549257135181152621 2899367830971425692932233)
                    ·
                      refine ⟨2174525873228569269699175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899367830971425692932233 2174525873228569269699175)
                      ·
                        rfl

theorem cell23_4234874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 2, 3, 2].length) (baseStart_4234874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234874 prefixEnd_4234874 := by exact prefixLift 4234874
  have htrace : WordTrace (prefixWord ++ tailWord_4234874) baseStart_4234874 baseEnd_4234874 := by
    simpa [prefixWord, tailWord_4234874, baseEnd_4234874] using wordTrace_append hprefix tailTrace_4234874
  have hstable : (prefixWord ++ tailWord_4234874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234874).length < 2 ^ (prefixWord ++ tailWord_4234874).sum := by decide
  have hdescent : baseEnd_4234874 < baseStart_4234874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234888 : List Nat := [2, 1, 3, 5, 2, 1, 1, 2, 6]
def baseStart_4234888 : Nat := 118140960795 + 4234888 * 2 ^ 59
def prefixEnd_4234888 : Nat := 4983230072969 + 3 ^ 40 * 4234888 * 2
def baseEnd_4234888 : Nat := 241614784661970246102679

theorem tailTrace_4234888 : CollatzResearch.WordTrace tailWord_4234888 prefixEnd_4234888 241614784661970246102679 := by
  unfold tailWord_4234888
  simp only [CollatzResearch.WordTrace]
  refine ⟨77229527340865756066868659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102972703121154341422491545 77229527340865756066868659)
  ·
    refine ⟨115844291011298634100302989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77229527340865756066868659 115844291011298634100302989)
    ·
      refine ⟨43441609129236987787613621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115844291011298634100302989 43441609129236987787613621)
      ·
        refine ⟨4072650855865967605088777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43441609129236987787613621 4072650855865967605088777)
        ·
          refine ⟨3054488141899475703816583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4072650855865967605088777 3054488141899475703816583)
          ·
            refine ⟨4581732212849213555724875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054488141899475703816583 4581732212849213555724875)
            ·
              refine ⟨6872598319273820333587313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4581732212849213555724875 6872598319273820333587313)
              ·
                refine ⟨5154448739455365250190485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6872598319273820333587313 5154448739455365250190485)
                ·
                  refine ⟨241614784661970246102679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5154448739455365250190485 241614784661970246102679)
                  ·
                    rfl

theorem cell23_4234888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 2, 6].length) (baseStart_4234888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234888 prefixEnd_4234888 := by exact prefixLift 4234888
  have htrace : WordTrace (prefixWord ++ tailWord_4234888) baseStart_4234888 baseEnd_4234888 := by
    simpa [prefixWord, tailWord_4234888, baseEnd_4234888] using wordTrace_append hprefix tailTrace_4234888
  have hstable : (prefixWord ++ tailWord_4234888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234888).length < 2 ^ (prefixWord ++ tailWord_4234888).sum := by decide
  have hdescent : baseEnd_4234888 < baseStart_4234888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234898 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_4234898 : Nat := 118140960795 + 4234898 * 2 ^ 59
def prefixEnd_4234898 : Nat := 4983230072969 + 3 ^ 40 * 4234898 * 2
def baseEnd_4234898 : Nat := 2174538196764277175799065

theorem tailTrace_4234898 : CollatzResearch.WordTrace tailWord_4234898 prefixEnd_4234898 2174538196764277175799065 := by
  unfold tailWord_4234898
  simp only [CollatzResearch.WordTrace]
  refine ⟨38614854852923820960400337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102972946274463522561067565 38614854852923820960400337)
  ·
    refine ⟨28961141139692865720300253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38614854852923820960400337 28961141139692865720300253)
    ·
      refine ⟨10860427927384824645112595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28961141139692865720300253 10860427927384824645112595)
      ·
        refine ⟨16290641891077236967668893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10860427927384824645112595 16290641891077236967668893)
        ·
          refine ⟨6108990709153963862875835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16290641891077236967668893 6108990709153963862875835)
          ·
            refine ⟨9163486063730945794313753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6108990709153963862875835 9163486063730945794313753)
            ·
              refine ⟨6872614547798209345735315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9163486063730945794313753 6872614547798209345735315)
              ·
                refine ⟨10308921821697314018602973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6872614547798209345735315 10308921821697314018602973)
                ·
                  refine ⟨3865845683136492756976115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10308921821697314018602973 3865845683136492756976115)
                  ·
                    refine ⟨5798768524704739135464173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3865845683136492756976115 5798768524704739135464173)
                    ·
                      refine ⟨2174538196764277175799065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5798768524704739135464173 2174538196764277175799065)
                      ·
                        rfl

theorem cell23_4234898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_4234898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234898 prefixEnd_4234898 := by exact prefixLift 4234898
  have htrace : WordTrace (prefixWord ++ tailWord_4234898) baseStart_4234898 baseEnd_4234898 := by
    simpa [prefixWord, tailWord_4234898, baseEnd_4234898] using wordTrace_append hprefix tailTrace_4234898
  have hstable : (prefixWord ++ tailWord_4234898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234898).length < 2 ^ (prefixWord ++ tailWord_4234898).sum := by decide
  have hdescent : baseEnd_4234898 < baseStart_4234898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4234981 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 3, 3, 2]
def baseStart_4234981 : Nat := 118140960795 + 4234981 * 2 ^ 59
def prefixEnd_4234981 : Nat := 4983230072969 + 3 ^ 40 * 4234981 * 2
def baseEnd_4234981 : Nat := 2174580815658600351061183

theorem tailTrace_4234981 : CollatzResearch.WordTrace tailWord_4234981 prefixEnd_4234981 2174580815658600351061183 := by
  unfold tailWord_4234981
  simp only [CollatzResearch.WordTrace]
  refine ⟨154462446670394589016872797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102974964446929726011248531 154462446670394589016872797)
  ·
    refine ⟨57923417501397970881327299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154462446670394589016872797 57923417501397970881327299)
    ·
      refine ⟨86885126252096956321990949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57923417501397970881327299 86885126252096956321990949)
      ·
        refine ⟨16290961172268179310373303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86885126252096956321990949 16290961172268179310373303)
        ·
          refine ⟨24436441758402268965559955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16290961172268179310373303 24436441758402268965559955)
          ·
            refine ⟨36654662637603403448339933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24436441758402268965559955 36654662637603403448339933)
            ·
              refine ⟨13745498489101276293127475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36654662637603403448339933 13745498489101276293127475)
              ·
                refine ⟨20618247733651914439691213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13745498489101276293127475 20618247733651914439691213)
                ·
                  refine ⟨7731842900119467914884205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20618247733651914439691213 7731842900119467914884205)
                  ·
                    refine ⟨2899441087544800468081577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7731842900119467914884205 2899441087544800468081577)
                    ·
                      refine ⟨2174580815658600351061183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899441087544800468081577 2174580815658600351061183)
                      ·
                        rfl

theorem cell23_4234981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_4234981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4234981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4234981 prefixEnd_4234981 := by exact prefixLift 4234981
  have htrace : WordTrace (prefixWord ++ tailWord_4234981) baseStart_4234981 baseEnd_4234981 := by
    simpa [prefixWord, tailWord_4234981, baseEnd_4234981] using wordTrace_append hprefix tailTrace_4234981
  have hstable : (prefixWord ++ tailWord_4234981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4234981).length < 2 ^ (prefixWord ++ tailWord_4234981).sum := by decide
  have hdescent : baseEnd_4234981 < baseStart_4234981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4234981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235006 : List Nat := [4, 2, 2, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_4235006 : Nat := 118140960795 + 4235006 * 2 ^ 59
def prefixEnd_4235006 : Nat := 4983230072969 + 3 ^ 40 * 4235006 * 2
def baseEnd_4235006 : Nat := 2174593652674962753248569

theorem tailTrace_4235006 : CollatzResearch.WordTrace tailWord_4235006 prefixEnd_4235006 2174593652674962753248569 := by
  unfold tailWord_4235006
  simp only [CollatzResearch.WordTrace]
  refine ⟨19307919811913002285816609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102975572330202678857688581 19307919811913002285816609)
  ·
    refine ⟨14480939858934751714362457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19307919811913002285816609 14480939858934751714362457)
    ·
      refine ⟨10860704894201063785771843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14480939858934751714362457 10860704894201063785771843)
      ·
        refine ⟨16291057341301595678657765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10860704894201063785771843 16291057341301595678657765)
        ·
          refine ⟨3054573251494049189748331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16291057341301595678657765 3054573251494049189748331)
          ·
            refine ⟨4581859877241073784622497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3054573251494049189748331 4581859877241073784622497)
            ·
              refine ⟨3436394907930805338466873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4581859877241073784622497 3436394907930805338466873)
              ·
                refine ⟨2577296180948104003850155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3436394907930805338466873 2577296180948104003850155)
                ·
                  refine ⟨3865944271422156005775233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2577296180948104003850155 3865944271422156005775233)
                  ·
                    refine ⟨2899458203566617004331425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3865944271422156005775233 2899458203566617004331425)
                    ·
                      refine ⟨2174593652674962753248569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899458203566617004331425 2174593652674962753248569)
                      ·
                        rfl

theorem cell23_4235006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_4235006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235006 prefixEnd_4235006 := by exact prefixLift 4235006
  have htrace : WordTrace (prefixWord ++ tailWord_4235006) baseStart_4235006 baseEnd_4235006 := by
    simpa [prefixWord, tailWord_4235006, baseEnd_4235006] using wordTrace_append hprefix tailTrace_4235006
  have hstable : (prefixWord ++ tailWord_4235006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235006).length < 2 ^ (prefixWord ++ tailWord_4235006).sum := by decide
  have hdescent : baseEnd_4235006 < baseStart_4235006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235011 : List Nat := [1, 1, 1, 3, 2, 2, 2, 3, 4, 2, 2]
def baseStart_4235011 : Nat := 118140960795 + 4235011 * 2 ^ 59
def prefixEnd_4235011 : Nat := 4983230072969 + 3 ^ 40 * 4235011 * 2
def baseEnd_4235011 : Nat := 2174596220078235233686045

theorem tailTrace_4235011 : CollatzResearch.WordTrace tailWord_4235011 prefixEnd_4235011 2174596220078235233686045 := by
  unfold tailWord_4235011
  simp only [CollatzResearch.WordTrace]
  refine ⟨154463540860285904140464887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102975693906857269426976591 154463540860285904140464887)
  ·
    refine ⟨231695311290428856210697331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154463540860285904140464887 231695311290428856210697331)
    ·
      refine ⟨347542966935643284316045997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231695311290428856210697331 347542966935643284316045997)
      ·
        refine ⟨130328612600866231618517249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347542966935643284316045997 130328612600866231618517249)
        ·
          refine ⟨97746459450649673713887937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130328612600866231618517249 97746459450649673713887937)
          ·
            refine ⟨73309844587987255285415953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97746459450649673713887937 73309844587987255285415953)
            ·
              refine ⟨54982383440990441464061965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73309844587987255285415953 54982383440990441464061965)
              ·
                refine ⟨20618393790371415549023237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54982383440990441464061965 20618393790371415549023237)
                ·
                  refine ⟨3865948835694640415441857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20618393790371415549023237 3865948835694640415441857)
                  ·
                    refine ⟨2899461626770980311581393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3865948835694640415441857 2899461626770980311581393)
                    ·
                      refine ⟨2174596220078235233686045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899461626770980311581393 2174596220078235233686045)
                      ·
                        rfl

theorem cell23_4235011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 2, 2].length) (baseStart_4235011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235011 prefixEnd_4235011 := by exact prefixLift 4235011
  have htrace : WordTrace (prefixWord ++ tailWord_4235011) baseStart_4235011 baseEnd_4235011 := by
    simpa [prefixWord, tailWord_4235011, baseEnd_4235011] using wordTrace_append hprefix tailTrace_4235011
  have hstable : (prefixWord ++ tailWord_4235011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235011).length < 2 ^ (prefixWord ++ tailWord_4235011).sum := by decide
  have hdescent : baseEnd_4235011 < baseStart_4235011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235017 : List Nat := [1, 2, 1, 1, 3, 2, 1, 5, 7]
def baseStart_4235017 : Nat := 118140960795 + 4235017 * 2 ^ 59
def prefixEnd_4235017 : Nat := 4983230072969 + 3 ^ 40 * 4235017 * 2
def baseEnd_4235017 : Nat := 241622144551351356690113

theorem tailTrace_4235017 : CollatzResearch.WordTrace tailWord_4235017 prefixEnd_4235017 241622144551351356690113 := by
  unfold tailWord_4235017
  simp only [CollatzResearch.WordTrace]
  refine ⟨154463759698264167165183305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102975839798842778110122203 154463759698264167165183305)
  ·
    refine ⟨115847819773698125373887479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154463759698264167165183305 115847819773698125373887479)
    ·
      refine ⟨173771729660547188060831219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115847819773698125373887479 173771729660547188060831219)
      ·
        refine ⟨260657594490820782091246829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173771729660547188060831219 260657594490820782091246829)
        ·
          refine ⟨97746597934057793284217561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260657594490820782091246829 97746597934057793284217561)
          ·
            refine ⟨73309948450543344963163171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97746597934057793284217561 73309948450543344963163171)
            ·
              refine ⟨109964922675815017444744757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73309948450543344963163171 109964922675815017444744757)
              ·
                refine ⟨10309211500857657885444821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109964922675815017444744757 10309211500857657885444821)
                ·
                  refine ⟨241622144551351356690113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10309211500857657885444821 241622144551351356690113)
                  ·
                    rfl

theorem cell23_4235017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 5, 7].length) (baseStart_4235017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235017 prefixEnd_4235017 := by exact prefixLift 4235017
  have htrace : WordTrace (prefixWord ++ tailWord_4235017) baseStart_4235017 baseEnd_4235017 := by
    simpa [prefixWord, tailWord_4235017, baseEnd_4235017] using wordTrace_append hprefix tailTrace_4235017
  have hstable : (prefixWord ++ tailWord_4235017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235017).length < 2 ^ (prefixWord ++ tailWord_4235017).sum := by decide
  have hdescent : baseEnd_4235017 < baseStart_4235017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235034 : List Nat := [3, 1, 1, 3, 2, 3, 1, 2, 7]
def baseStart_4235034 : Nat := 118140960795 + 4235034 * 2 ^ 59
def prefixEnd_4235034 : Nat := 4983230072969 + 3 ^ 40 * 4235034 * 2
def baseEnd_4235034 : Nat := 241623114459254293744271

theorem tailTrace_4235034 : CollatzResearch.WordTrace tailWord_4235034 prefixEnd_4235034 241623114459254293744271 := by
  unfold tailWord_4235034
  simp only [CollatzResearch.WordTrace]
  refine ⟨38616094934800644767138039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102976253159468386045701437 38616094934800644767138039)
  ·
    refine ⟨57924142402200967150707059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38616094934800644767138039 57924142402200967150707059)
    ·
      refine ⟨86886213603301450726060589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57924142402200967150707059 86886213603301450726060589)
      ·
        refine ⟨32582330101238044022272721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86886213603301450726060589 32582330101238044022272721)
        ·
          refine ⟨24436747575928533016704541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32582330101238044022272721 24436747575928533016704541)
          ·
            refine ⟨9163780340973199881264203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24436747575928533016704541 9163780340973199881264203)
            ·
              refine ⟨13745670511459799821896305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9163780340973199881264203 13745670511459799821896305)
              ·
                refine ⟨10309252883594849866422229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13745670511459799821896305 10309252883594849866422229)
                ·
                  refine ⟨241623114459254293744271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10309252883594849866422229 241623114459254293744271)
                  ·
                    rfl

theorem cell23_4235034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 7].length) (baseStart_4235034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235034 prefixEnd_4235034 := by exact prefixLift 4235034
  have htrace : WordTrace (prefixWord ++ tailWord_4235034) baseStart_4235034 baseEnd_4235034 := by
    simpa [prefixWord, tailWord_4235034, baseEnd_4235034] using wordTrace_append hprefix tailTrace_4235034
  have hstable : (prefixWord ++ tailWord_4235034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235034).length < 2 ^ (prefixWord ++ tailWord_4235034).sum := by decide
  have hdescent : baseEnd_4235034 < baseStart_4235034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235062 : List Nat := [5, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_4235062 : Nat := 118140960795 + 4235062 * 2 ^ 59
def prefixEnd_4235062 : Nat := 4983230072969 + 3 ^ 40 * 4235062 * 2
def baseEnd_4235062 : Nat := 2174622407591614534148311

theorem tailTrace_4235062 : CollatzResearch.WordTrace tailWord_4235062 prefixEnd_4235062 2174622407591614534148311 := by
  unfold tailWord_4235062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9654087561443821240660715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102976933988734093233714293 9654087561443821240660715)
  ·
    refine ⟨14481131342165731860991073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9654087561443821240660715 14481131342165731860991073)
    ·
      refine ⟨10860848506624298895743305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14481131342165731860991073 10860848506624298895743305)
      ·
        refine ⟨8145636379968224171807479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10860848506624298895743305 8145636379968224171807479)
        ·
          refine ⟨12218454569952336257711219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8145636379968224171807479 12218454569952336257711219)
          ·
            refine ⟨18327681854928504386566829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12218454569952336257711219 18327681854928504386566829)
            ·
              refine ⟨6872880695598189144962561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18327681854928504386566829 6872880695598189144962561)
              ·
                refine ⟨5154660521698641858721921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6872880695598189144962561 5154660521698641858721921)
                ·
                  refine ⟨3865995391273981394041441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5154660521698641858721921 3865995391273981394041441)
                  ·
                    refine ⟨2899496543455486045531081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3865995391273981394041441 2899496543455486045531081)
                    ·
                      refine ⟨2174622407591614534148311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899496543455486045531081 2174622407591614534148311)
                      ·
                        rfl

theorem cell23_4235062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_4235062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235062 prefixEnd_4235062 := by exact prefixLift 4235062
  have htrace : WordTrace (prefixWord ++ tailWord_4235062) baseStart_4235062 baseEnd_4235062 := by
    simpa [prefixWord, tailWord_4235062, baseEnd_4235062] using wordTrace_append hprefix tailTrace_4235062
  have hstable : (prefixWord ++ tailWord_4235062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235062).length < 2 ^ (prefixWord ++ tailWord_4235062).sum := by decide
  have hdescent : baseEnd_4235062 < baseStart_4235062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235118 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_4235118 : Nat := 118140960795 + 4235118 * 2 ^ 59
def prefixEnd_4235118 : Nat := 4983230072969 + 3 ^ 40 * 4235118 * 2
def baseEnd_4235118 : Nat := 2174651162508266315048053

theorem tailTrace_4235118 : CollatzResearch.WordTrace tailWord_4235118 prefixEnd_4235118 2174651162508266315048053 := by
  unfold tailWord_4235118
  simp only [CollatzResearch.WordTrace]
  refine ⟨19308430433862282676826251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102978295647265507609740005 19308430433862282676826251)
  ·
    refine ⟨28962645650793424015239377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19308430433862282676826251 28962645650793424015239377)
    ·
      refine ⟨21721984238095068011429533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28962645650793424015239377 21721984238095068011429533)
      ·
        refine ⟨8145744089285650504286075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21721984238095068011429533 8145744089285650504286075)
        ·
          refine ⟨12218616133928475756429113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8145744089285650504286075 12218616133928475756429113)
          ·
            refine ⟨9163962100446356817321835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12218616133928475756429113 9163962100446356817321835)
            ·
              refine ⟨13745943150669535225982753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9163962100446356817321835 13745943150669535225982753)
              ·
                refine ⟨10309457363002151419487065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13745943150669535225982753 10309457363002151419487065)
                ·
                  refine ⟨7732093022251613564615299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10309457363002151419487065 7732093022251613564615299)
                  ·
                    refine ⟨11598139533377420346922949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7732093022251613564615299 11598139533377420346922949)
                    ·
                      refine ⟨2174651162508266315048053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11598139533377420346922949 2174651162508266315048053)
                      ·
                        rfl

theorem cell23_4235118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_4235118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235118 prefixEnd_4235118 := by exact prefixLift 4235118
  have htrace : WordTrace (prefixWord ++ tailWord_4235118) baseStart_4235118 baseEnd_4235118 := by
    simpa [prefixWord, tailWord_4235118, baseEnd_4235118] using wordTrace_append hprefix tailTrace_4235118
  have hstable : (prefixWord ++ tailWord_4235118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235118).length < 2 ^ (prefixWord ++ tailWord_4235118).sum := by decide
  have hdescent : baseEnd_4235118 < baseStart_4235118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235121 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 2, 2, 3]
def baseStart_4235121 : Nat := 118140960795 + 4235121 * 2 ^ 59
def prefixEnd_4235121 : Nat := 4983230072969 + 3 ^ 40 * 4235121 * 2
def baseEnd_4235121 : Nat := 2174652702950229803310539

theorem tailTrace_4235121 : CollatzResearch.WordTrace tailWord_4235121 prefixEnd_4235121 2174652702950229803310539 := by
  unfold tailWord_4235121
  simp only [CollatzResearch.WordTrace]
  refine ⟨154467552889887392926969217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102978368593258261951312811 154467552889887392926969217)
  ·
    refine ⟨115850664667415544695226913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154467552889887392926969217 115850664667415544695226913)
    ·
      refine ⟨86887998500561658521420185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115850664667415544695226913 86887998500561658521420185)
      ·
        refine ⟨65165998875421243891065139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86887998500561658521420185 65165998875421243891065139)
        ·
          refine ⟨97748998313131865836597709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65165998875421243891065139 97748998313131865836597709)
          ·
            refine ⟨36655874367424449688724141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97748998313131865836597709 36655874367424449688724141)
            ·
              refine ⟨13745952887784168633271553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36655874367424449688724141 13745952887784168633271553)
              ·
                refine ⟨10309464665838126474953665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13745952887784168633271553 10309464665838126474953665)
                ·
                  refine ⟨7732098499378594856215249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10309464665838126474953665 7732098499378594856215249)
                  ·
                    refine ⟨5799073874533946142161437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7732098499378594856215249 5799073874533946142161437)
                    ·
                      refine ⟨2174652702950229803310539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5799073874533946142161437 2174652702950229803310539)
                      ·
                        rfl

theorem cell23_4235121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_4235121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235121 prefixEnd_4235121 := by exact prefixLift 4235121
  have htrace : WordTrace (prefixWord ++ tailWord_4235121) baseStart_4235121 baseEnd_4235121 := by
    simpa [prefixWord, tailWord_4235121, baseEnd_4235121] using wordTrace_append hprefix tailTrace_4235121
  have hstable : (prefixWord ++ tailWord_4235121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235121).length < 2 ^ (prefixWord ++ tailWord_4235121).sum := by decide
  have hdescent : baseEnd_4235121 < baseStart_4235121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235161 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 1, 5, 2]
def baseStart_4235161 : Nat := 118140960795 + 4235161 * 2 ^ 59
def prefixEnd_4235161 : Nat := 4983230072969 + 3 ^ 40 * 4235161 * 2
def baseEnd_4235161 : Nat := 2174673242176409646810355

theorem tailTrace_4235161 : CollatzResearch.WordTrace tailWord_4235161 prefixEnd_4235161 2174673242176409646810355 := by
  unfold tailWord_4235161
  simp only [CollatzResearch.WordTrace]
  refine ⟨154469011809742479758425337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102979341206494986505616891 154469011809742479758425337)
  ·
    refine ⟨115851758857306859818819003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154469011809742479758425337 115851758857306859818819003)
    ·
      refine ⟨173777638285960289728228505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115851758857306859818819003 173777638285960289728228505)
      ·
        refine ⟨130333228714470217296171379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173777638285960289728228505 130333228714470217296171379)
        ·
          refine ⟨195499843071705325944257069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130333228714470217296171379 195499843071705325944257069)
          ·
            refine ⟨73312441151889497229096401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195499843071705325944257069 73312441151889497229096401)
            ·
              refine ⟨54984330863917122921822301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73312441151889497229096401 54984330863917122921822301)
              ·
                refine ⟨20619124073968921095683363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54984330863917122921822301 20619124073968921095683363)
                ·
                  refine ⟨30928686110953381643525045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20619124073968921095683363 30928686110953381643525045)
                  ·
                    refine ⟨2899564322901879529080473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30928686110953381643525045 2899564322901879529080473)
                    ·
                      refine ⟨2174673242176409646810355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899564322901879529080473 2174673242176409646810355)
                      ·
                        rfl

theorem cell23_4235161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 5, 2].length) (baseStart_4235161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235161 prefixEnd_4235161 := by exact prefixLift 4235161
  have htrace : WordTrace (prefixWord ++ tailWord_4235161) baseStart_4235161 baseEnd_4235161 := by
    simpa [prefixWord, tailWord_4235161, baseEnd_4235161] using wordTrace_append hprefix tailTrace_4235161
  have hstable : (prefixWord ++ tailWord_4235161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235161).length < 2 ^ (prefixWord ++ tailWord_4235161).sum := by decide
  have hdescent : baseEnd_4235161 < baseStart_4235161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235191 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 2, 6, 2]
def baseStart_4235191 : Nat := 118140960795 + 4235191 * 2 ^ 59
def prefixEnd_4235191 : Nat := 4983230072969 + 3 ^ 40 * 4235191 * 2
def baseEnd_4235191 : Nat := 2174688646596044529435217

theorem tailTrace_4235191 : CollatzResearch.WordTrace tailWord_4235191 prefixEnd_4235191 2174688646596044529435217 := by
  unfold tailWord_4235191
  simp only [CollatzResearch.WordTrace]
  refine ⟨154470105999633794882017427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102980070666422529921344951 154470105999633794882017427)
  ·
    refine ⟨231705158999450692323026141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154470105999633794882017427 231705158999450692323026141)
    ·
      refine ⟨86889434624794009621134803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231705158999450692323026141 86889434624794009621134803)
      ·
        refine ⟨130334151937191014431702205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86889434624794009621134803 130334151937191014431702205)
        ·
          refine ⟨48875306976446630411888327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130334151937191014431702205 48875306976446630411888327)
          ·
            refine ⟨73312960464669945617832491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48875306976446630411888327 73312960464669945617832491)
            ·
              refine ⟨109969440697004918426748737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73312960464669945617832491 109969440697004918426748737)
              ·
                refine ⟨82477080522753688820061553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109969440697004918426748737 82477080522753688820061553)
                ·
                  refine ⟨61857810392065266615046165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82477080522753688820061553 61857810392065266615046165)
                  ·
                    refine ⟨2899584862128059372580289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61857810392065266615046165 2899584862128059372580289)
                    ·
                      refine ⟨2174688646596044529435217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899584862128059372580289 2174688646596044529435217)
                      ·
                        rfl

theorem cell23_4235191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 6, 2].length) (baseStart_4235191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235191 prefixEnd_4235191 := by exact prefixLift 4235191
  have htrace : WordTrace (prefixWord ++ tailWord_4235191) baseStart_4235191 baseEnd_4235191 := by
    simpa [prefixWord, tailWord_4235191, baseEnd_4235191] using wordTrace_append hprefix tailTrace_4235191
  have hstable : (prefixWord ++ tailWord_4235191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235191).length < 2 ^ (prefixWord ++ tailWord_4235191).sum := by decide
  have hdescent : baseEnd_4235191 < baseStart_4235191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235211 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 3]
def baseStart_4235211 : Nat := 118140960795 + 4235211 * 2 ^ 59
def prefixEnd_4235211 : Nat := 4983230072969 + 3 ^ 40 * 4235211 * 2
def baseEnd_4235211 : Nat := 2174698916209134451185125

theorem tailTrace_4235211 : CollatzResearch.WordTrace tailWord_4235211 prefixEnd_4235211 2174698916209134451185125 := by
  unfold tailWord_4235211
  simp only [CollatzResearch.WordTrace]
  refine ⟨154470835459561338297745487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102980556973040892198496991 154470835459561338297745487)
  ·
    refine ⟨231706253189342007446618231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154470835459561338297745487 231706253189342007446618231)
    ·
      refine ⟨347559379784013011169927347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231706253189342007446618231 347559379784013011169927347)
      ·
        refine ⟨521339069676019516754891021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347559379784013011169927347 521339069676019516754891021)
        ·
          refine ⟨195502151128507318783084133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 521339069676019516754891021 195502151128507318783084133)
          ·
            refine ⟨36656653336595122271828275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195502151128507318783084133 36656653336595122271828275)
            ·
              refine ⟨54984980004892683407742413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36656653336595122271828275 54984980004892683407742413)
              ·
                refine ⟨20619367501834756277903405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54984980004892683407742413 20619367501834756277903405)
                ·
                  refine ⟨7732262813188033604213777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20619367501834756277903405 7732262813188033604213777)
                  ·
                    refine ⟨5799197109891025203160333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7732262813188033604213777 5799197109891025203160333)
                    ·
                      refine ⟨2174698916209134451185125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5799197109891025203160333 2174698916209134451185125)
                      ·
                        rfl

theorem cell23_4235211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 3].length) (baseStart_4235211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235211 prefixEnd_4235211 := by exact prefixLift 4235211
  have htrace : WordTrace (prefixWord ++ tailWord_4235211) baseStart_4235211 baseEnd_4235211 := by
    simpa [prefixWord, tailWord_4235211, baseEnd_4235211] using wordTrace_append hprefix tailTrace_4235211
  have hstable : (prefixWord ++ tailWord_4235211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235211).length < 2 ^ (prefixWord ++ tailWord_4235211).sum := by decide
  have hdescent : baseEnd_4235211 < baseStart_4235211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235235 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 2, 4]
def baseStart_4235235 : Nat := 118140960795 + 4235235 * 2 ^ 59
def prefixEnd_4235235 : Nat := 4983230072969 + 3 ^ 40 * 4235235 * 2
def baseEnd_4235235 : Nat := 724903746581614119095005

theorem tailTrace_4235235 : CollatzResearch.WordTrace tailWord_4235235 prefixEnd_4235235 724903746581614119095005 := by
  unfold tailWord_4235235
  simp only [CollatzResearch.WordTrace]
  refine ⟨154471710811474390396619159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102981140540982926931079439 154471710811474390396619159)
  ·
    refine ⟨231707566217211585594928739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154471710811474390396619159 231707566217211585594928739)
    ·
      refine ⟨347561349325817378392393109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231707566217211585594928739 347561349325817378392393109)
      ·
        refine ⟨16291938249647689612143427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 347561349325817378392393109 16291938249647689612143427)
        ·
          refine ⟨24437907374471534418215141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16291938249647689612143427 24437907374471534418215141)
          ·
            refine ⟨4582107632713412703415339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24437907374471534418215141 4582107632713412703415339)
            ·
              refine ⟨6873161449070119055123009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4582107632713412703415339 6873161449070119055123009)
              ·
                refine ⟨5154871086802589291342257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6873161449070119055123009 5154871086802589291342257)
                ·
                  refine ⟨3866153315101941968506693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5154871086802589291342257 3866153315101941968506693)
                  ·
                    refine ⟨724903746581614119095005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3866153315101941968506693 724903746581614119095005)
                    ·
                      rfl

theorem cell23_4235235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 4].length) (baseStart_4235235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235235 prefixEnd_4235235 := by exact prefixLift 4235235
  have htrace : WordTrace (prefixWord ++ tailWord_4235235) baseStart_4235235 baseEnd_4235235 := by
    simpa [prefixWord, tailWord_4235235, baseEnd_4235235] using wordTrace_append hprefix tailTrace_4235235
  have hstable : (prefixWord ++ tailWord_4235235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235235).length < 2 ^ (prefixWord ++ tailWord_4235235).sum := by decide
  have hdescent : baseEnd_4235235 < baseStart_4235235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235242 : List Nat := [3, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_4235242 : Nat := 118140960795 + 4235242 * 2 ^ 59
def prefixEnd_4235242 : Nat := 4983230072969 + 3 ^ 40 * 4235242 * 2
def baseEnd_4235242 : Nat := 2174714834109423829897483

theorem tailTrace_4235242 : CollatzResearch.WordTrace tailWord_4235242 prefixEnd_4235242 2174714834109423829897483 := by
  unfold tailWord_4235242
  simp only [CollatzResearch.WordTrace]
  refine ⟨38617991530612257648030995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102981310748299353728082653 38617991530612257648030995)
  ·
    refine ⟨57926987295918386472046493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38617991530612257648030995 57926987295918386472046493)
    ·
      refine ⟨21722620235969394927017435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57926987295918386472046493 21722620235969394927017435)
      ·
        refine ⟨32583930353954092390526153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21722620235969394927017435 32583930353954092390526153)
        ·
          refine ⟨24437947765465569292894615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32583930353954092390526153 24437947765465569292894615)
          ·
            refine ⟨36656921648198353939341923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24437947765465569292894615 36656921648198353939341923)
            ·
              refine ⟨54985382472297530909012885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36656921648198353939341923 54985382472297530909012885)
              ·
                refine ⟨2577439803388946761359979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54985382472297530909012885 2577439803388946761359979)
                ·
                  refine ⟨3866159705083420142039969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2577439803388946761359979 3866159705083420142039969)
                  ·
                    refine ⟨2899619778812565106529977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3866159705083420142039969 2899619778812565106529977)
                    ·
                      refine ⟨2174714834109423829897483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899619778812565106529977 2174714834109423829897483)
                      ·
                        rfl

theorem cell23_4235242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_4235242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235242 prefixEnd_4235242 := by exact prefixLift 4235242
  have htrace : WordTrace (prefixWord ++ tailWord_4235242) baseStart_4235242 baseEnd_4235242 := by
    simpa [prefixWord, tailWord_4235242, baseEnd_4235242] using wordTrace_append hprefix tailTrace_4235242
  have hstable : (prefixWord ++ tailWord_4235242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235242).length < 2 ^ (prefixWord ++ tailWord_4235242).sum := by decide
  have hdescent : baseEnd_4235242 < baseStart_4235242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235244 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_4235244 : Nat := 118140960795 + 4235244 * 2 ^ 59
def prefixEnd_4235244 : Nat := 4983230072969 + 3 ^ 40 * 4235244 * 2
def baseEnd_4235244 : Nat := 724905287023577607357491

theorem tailTrace_4235244 : CollatzResearch.WordTrace tailWord_4235244 prefixEnd_4235244 724905287023577607357491 := by
  unfold tailWord_4235244
  simp only [CollatzResearch.WordTrace]
  refine ⟨77236019534220892466848393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102981359378961189955797857 77236019534220892466848393)
  ·
    refine ⟨57927014650665669350136295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77236019534220892466848393 57927014650665669350136295)
    ·
      refine ⟨86890521975998504025204443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57927014650665669350136295 86890521975998504025204443)
      ·
        refine ⟨130335782963997756037806665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86890521975998504025204443 130335782963997756037806665)
        ·
          refine ⟨97751837222998317028354999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130335782963997756037806665 97751837222998317028354999)
          ·
            refine ⟨146627755834497475542532499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97751837222998317028354999 146627755834497475542532499)
            ·
              refine ⟨219941633751746213313798749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146627755834497475542532499 219941633751746213313798749)
              ·
                refine ⟨82478112656904829992674531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 219941633751746213313798749 82478112656904829992674531)
                ·
                  refine ⟨123717168985357244989011797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82478112656904829992674531 123717168985357244989011797)
                  ·
                    refine ⟨724905287023577607357491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 123717168985357244989011797 724905287023577607357491)
                    ·
                      rfl

theorem cell23_4235244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_4235244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235244 prefixEnd_4235244 := by exact prefixLift 4235244
  have htrace : WordTrace (prefixWord ++ tailWord_4235244) baseStart_4235244 baseEnd_4235244 := by
    simpa [prefixWord, tailWord_4235244, baseEnd_4235244] using wordTrace_append hprefix tailTrace_4235244
  have hstable : (prefixWord ++ tailWord_4235244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235244).length < 2 ^ (prefixWord ++ tailWord_4235244).sum := by decide
  have hdescent : baseEnd_4235244 < baseStart_4235244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235245 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_4235245 : Nat := 118140960795 + 4235245 * 2 ^ 59
def prefixEnd_4235245 : Nat := 4983230072969 + 3 ^ 40 * 4235245 * 2
def baseEnd_4235245 : Nat := 2174716374551387318159969

theorem tailTrace_4235245 : CollatzResearch.WordTrace tailWord_4235245 prefixEnd_4235245 2174716374551387318159969 := by
  unfold tailWord_4235245
  simp only [CollatzResearch.WordTrace]
  refine ⟨154472075541438162104483189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102981383694292108069655459 154472075541438162104483189)
  ·
    refine ⟨14481757082009827697295299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154472075541438162104483189 14481757082009827697295299)
    ·
      refine ⟨21722635623014741545942949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14481757082009827697295299 21722635623014741545942949)
      ·
        refine ⟨4072994179315264039864303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21722635623014741545942949 4072994179315264039864303)
        ·
          refine ⟨6109491268972896059796455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4072994179315264039864303 6109491268972896059796455)
          ·
            refine ⟨9164236903459344089694683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6109491268972896059796455 9164236903459344089694683)
            ·
              refine ⟨13746355355189016134542025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9164236903459344089694683 13746355355189016134542025)
              ·
                refine ⟨10309766516391762100906519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13746355355189016134542025 10309766516391762100906519)
                ·
                  refine ⟨15464649774587643151359779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10309766516391762100906519 15464649774587643151359779)
                  ·
                    refine ⟨23196974661881464727039669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15464649774587643151359779 23196974661881464727039669)
                    ·
                      refine ⟨2174716374551387318159969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23196974661881464727039669 2174716374551387318159969)
                      ·
                        rfl

theorem cell23_4235245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_4235245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235245 prefixEnd_4235245 := by exact prefixLift 4235245
  have htrace : WordTrace (prefixWord ++ tailWord_4235245) baseStart_4235245 baseEnd_4235245 := by
    simpa [prefixWord, tailWord_4235245, baseEnd_4235245] using wordTrace_append hprefix tailTrace_4235245
  have hstable : (prefixWord ++ tailWord_4235245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235245).length < 2 ^ (prefixWord ++ tailWord_4235245).sum := by decide
  have hdescent : baseEnd_4235245 < baseStart_4235245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235262 : List Nat := [4, 2, 2, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_4235262 : Nat := 118140960795 + 4235262 * 2 ^ 59
def prefixEnd_4235262 : Nat := 4983230072969 + 3 ^ 40 * 4235262 * 2
def baseEnd_4235262 : Nat := 2174725103722513751647391

theorem tailTrace_4235262 : CollatzResearch.WordTrace tailWord_4235262 prefixEnd_4235262 2174725103722513751647391 := by
  unfold tailWord_4235262
  simp only [CollatzResearch.WordTrace]
  refine ⟨19309086947797071750981505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102981797054917716005234693 19309086947797071750981505)
  ·
    refine ⟨14481815210847803813236129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19309086947797071750981505 14481815210847803813236129)
    ·
      refine ⟨10861361408135852859927097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14481815210847803813236129 10861361408135852859927097)
      ·
        refine ⟨8146021056101889644945323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10861361408135852859927097 8146021056101889644945323)
        ·
          refine ⟨12219031584152834467417985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8146021056101889644945323 12219031584152834467417985)
          ·
            refine ⟨9164273688114625850563489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12219031584152834467417985 9164273688114625850563489)
            ·
              refine ⟨6873205266085969387922617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9164273688114625850563489 6873205266085969387922617)
              ·
                refine ⟨5154903949564477040941963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6873205266085969387922617 5154903949564477040941963)
                ·
                  refine ⟨7732355924346715561412945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5154903949564477040941963 7732355924346715561412945)
                  ·
                    refine ⟨5799266943260036671059709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7732355924346715561412945 5799266943260036671059709)
                    ·
                      refine ⟨2174725103722513751647391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5799266943260036671059709 2174725103722513751647391)
                      ·
                        rfl

theorem cell23_4235262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_4235262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235262 prefixEnd_4235262 := by exact prefixLift 4235262
  have htrace : WordTrace (prefixWord ++ tailWord_4235262) baseStart_4235262 baseEnd_4235262 := by
    simpa [prefixWord, tailWord_4235262, baseEnd_4235262] using wordTrace_append hprefix tailTrace_4235262
  have hstable : (prefixWord ++ tailWord_4235262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235262).length < 2 ^ (prefixWord ++ tailWord_4235262).sum := by decide
  have hdescent : baseEnd_4235262 < baseStart_4235262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235264 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_4235264 : Nat := 118140960795 + 4235264 * 2 ^ 59
def prefixEnd_4235264 : Nat := 4983230072969 + 3 ^ 40 * 4235264 * 2
def baseEnd_4235264 : Nat := 2174726130683822743822381

theorem tailTrace_4235264 : CollatzResearch.WordTrace tailWord_4235264 prefixEnd_4235264 2174726130683822743822381 := by
  unfold tailWord_4235264
  simp only [CollatzResearch.WordTrace]
  refine ⟨77236384264184664174712423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102981845685579552232949897 77236384264184664174712423)
  ·
    refine ⟨115854576396276996262068635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77236384264184664174712423 115854576396276996262068635)
    ·
      refine ⟨173781864594415494393102953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115854576396276996262068635 173781864594415494393102953)
      ·
        refine ⟨130336398445811620794827215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173781864594415494393102953 130336398445811620794827215)
        ·
          refine ⟨195504597668717431192240823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130336398445811620794827215 195504597668717431192240823)
          ·
            refine ⟨293256896503076146788361235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195504597668717431192240823 293256896503076146788361235)
            ·
              refine ⟨439885344754614220182541853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293256896503076146788361235 439885344754614220182541853)
              ·
                refine ⟨164957004282980332568453195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 439885344754614220182541853 164957004282980332568453195)
                ·
                  refine ⟨247435506424470498852679793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164957004282980332568453195 247435506424470498852679793)
                  ·
                    refine ⟨185576629818352874139509845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 247435506424470498852679793 185576629818352874139509845)
                    ·
                      refine ⟨2174726130683822743822381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 185576629818352874139509845 2174726130683822743822381)
                      ·
                        rfl

theorem cell23_4235264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_4235264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235264 prefixEnd_4235264 := by exact prefixLift 4235264
  have htrace : WordTrace (prefixWord ++ tailWord_4235264) baseStart_4235264 baseEnd_4235264 := by
    simpa [prefixWord, tailWord_4235264, baseEnd_4235264] using wordTrace_append hprefix tailTrace_4235264
  have hstable : (prefixWord ++ tailWord_4235264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235264).length < 2 ^ (prefixWord ++ tailWord_4235264).sum := by decide
  have hdescent : baseEnd_4235264 < baseStart_4235264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235270 : List Nat := [6, 2, 1, 2, 1, 2, 1, 3, 1, 1, 3]
def baseStart_4235270 : Nat := 118140960795 + 4235270 * 2 ^ 59
def prefixEnd_4235270 : Nat := 4983230072969 + 3 ^ 40 * 4235270 * 2
def baseEnd_4235270 : Nat := 2174729211567749720347355

theorem tailTrace_4235270 : CollatzResearch.WordTrace tailWord_4235270 prefixEnd_4235270 2174729211567749720347355 := by
  unfold tailWord_4235270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4827280855198362230441977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 102981991577565060916095509 4827280855198362230441977)
  ·
    refine ⟨3620460641398771672831483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4827280855198362230441977 3620460641398771672831483)
    ·
      refine ⟨5430690962098157509247225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3620460641398771672831483 5430690962098157509247225)
      ·
        refine ⟨4073018221573618131935419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5430690962098157509247225 4073018221573618131935419)
        ·
          refine ⟨6109527332360427197903129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4073018221573618131935419 6109527332360427197903129)
          ·
            refine ⟨4582145499270320398427347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6109527332360427197903129 4582145499270320398427347)
            ·
              refine ⟨6873218248905480597641021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4582145499270320398427347 6873218248905480597641021)
              ·
                refine ⟨2577456843339555224115383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6873218248905480597641021 2577456843339555224115383)
                ·
                  refine ⟨3866185265009332836173075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2577456843339555224115383 3866185265009332836173075)
                  ·
                    refine ⟨5799277897513999254259613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3866185265009332836173075 5799277897513999254259613)
                    ·
                      refine ⟨2174729211567749720347355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5799277897513999254259613 2174729211567749720347355)
                      ·
                        rfl

theorem cell23_4235270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_4235270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235270 prefixEnd_4235270 := by exact prefixLift 4235270
  have htrace : WordTrace (prefixWord ++ tailWord_4235270) baseStart_4235270 baseEnd_4235270 := by
    simpa [prefixWord, tailWord_4235270, baseEnd_4235270] using wordTrace_append hprefix tailTrace_4235270
  have hstable : (prefixWord ++ tailWord_4235270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235270).length < 2 ^ (prefixWord ++ tailWord_4235270).sum := by decide
  have hdescent : baseEnd_4235270 < baseStart_4235270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235271 : List Nat := [1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_4235271 : Nat := 118140960795 + 4235271 * 2 ^ 59
def prefixEnd_4235271 : Nat := 4983230072969 + 3 ^ 40 * 4235271 * 2
def baseEnd_4235271 : Nat := 2174729725048404216434849

theorem tailTrace_4235271 : CollatzResearch.WordTrace tailWord_4235271 prefixEnd_4235271 2174729725048404216434849 := by
  unfold tailWord_4235271
  simp only [CollatzResearch.WordTrace]
  refine ⟨154473023839343968544929667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102982015892895979029953111 154473023839343968544929667)
  ·
    refine ⟨231709535759015952817394501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154473023839343968544929667 231709535759015952817394501)
    ·
      refine ⟨43445537954815491153261469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231709535759015952817394501 43445537954815491153261469)
      ·
        refine ⟨16292076733055809182473051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43445537954815491153261469 16292076733055809182473051)
        ·
          refine ⟨24438115099583713773709577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16292076733055809182473051 24438115099583713773709577)
          ·
            refine ⟨18328586324687785330282183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24438115099583713773709577 18328586324687785330282183)
            ·
              refine ⟨27492879487031677995423275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18328586324687785330282183 27492879487031677995423275)
              ·
                refine ⟨41239319230547516993134913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27492879487031677995423275 41239319230547516993134913)
                ·
                  refine ⟨30929489422910637744851185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41239319230547516993134913 30929489422910637744851185)
                  ·
                    refine ⟨23197117067182978308638389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30929489422910637744851185 23197117067182978308638389)
                    ·
                      refine ⟨2174729725048404216434849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23197117067182978308638389 2174729725048404216434849)
                      ·
                        rfl

theorem cell23_4235271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_4235271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235271 prefixEnd_4235271 := by exact prefixLift 4235271
  have htrace : WordTrace (prefixWord ++ tailWord_4235271) baseStart_4235271 baseEnd_4235271 := by
    simpa [prefixWord, tailWord_4235271, baseEnd_4235271] using wordTrace_append hprefix tailTrace_4235271
  have hstable : (prefixWord ++ tailWord_4235271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235271).length < 2 ^ (prefixWord ++ tailWord_4235271).sum := by decide
  have hdescent : baseEnd_4235271 < baseStart_4235271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235318 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_4235318 : Nat := 118140960795 + 4235318 * 2 ^ 59
def prefixEnd_4235318 : Nat := 4983230072969 + 3 ^ 40 * 4235318 * 2
def baseEnd_4235318 : Nat := 2174753858639165532547133

theorem tailTrace_4235318 : CollatzResearch.WordTrace tailWord_4235318 prefixEnd_4235318 2174753858639165532547133 := by
  unfold tailWord_4235318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9654671129385855973243163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102983158713449130381260405 9654671129385855973243163)
  ·
    refine ⟨14482006694078783959864745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9654671129385855973243163 14482006694078783959864745)
    ·
      refine ⟨10861505020559087969898559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14482006694078783959864745 10861505020559087969898559)
      ·
        refine ⟨16292257530838631954847839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10861505020559087969898559 16292257530838631954847839)
        ·
          refine ⟨24438386296257947932271759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16292257530838631954847839 24438386296257947932271759)
          ·
            refine ⟨36657579444386921898407639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24438386296257947932271759 36657579444386921898407639)
            ·
              refine ⟨54986369166580382847611459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36657579444386921898407639 54986369166580382847611459)
              ·
                refine ⟨82479553749870574271417189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54986369166580382847611459 82479553749870574271417189)
                ·
                  refine ⟨15464916328100732675890723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82479553749870574271417189 15464916328100732675890723)
                  ·
                    refine ⟨23197374492151099013836085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15464916328100732675890723 23197374492151099013836085)
                    ·
                      refine ⟨2174753858639165532547133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23197374492151099013836085 2174753858639165532547133)
                      ·
                        rfl

theorem cell23_4235318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_4235318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235318 prefixEnd_4235318 := by exact prefixLift 4235318
  have htrace : WordTrace (prefixWord ++ tailWord_4235318) baseStart_4235318 baseEnd_4235318 := by
    simpa [prefixWord, tailWord_4235318, baseEnd_4235318] using wordTrace_append hprefix tailTrace_4235318
  have hstable : (prefixWord ++ tailWord_4235318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235318).length < 2 ^ (prefixWord ++ tailWord_4235318).sum := by decide
  have hdescent : baseEnd_4235318 < baseStart_4235318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235331 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 3]
def baseStart_4235331 : Nat := 118140960795 + 4235331 * 2 ^ 59
def prefixEnd_4235331 : Nat := 4983230072969 + 3 ^ 40 * 4235331 * 2
def baseEnd_4235331 : Nat := 2174760533887673981684573

theorem tailTrace_4235331 : CollatzResearch.WordTrace tailWord_4235331 prefixEnd_4235331 2174760533887673981684573 := by
  unfold tailWord_4235331
  simp only [CollatzResearch.WordTrace]
  refine ⟨154475212219126598792113847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102983474812751065861409231 154475212219126598792113847)
  ·
    refine ⟨231712818328689898188170771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154475212219126598792113847 231712818328689898188170771)
    ·
      refine ⟨347569227493034847282256157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231712818328689898188170771 347569227493034847282256157)
      ·
        refine ⟨130338460309888067730846059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347569227493034847282256157 130338460309888067730846059)
        ·
          refine ⟨195507690464832101596269089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130338460309888067730846059 195507690464832101596269089)
          ·
            refine ⟨146630767848624076197201817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195507690464832101596269089 146630767848624076197201817)
            ·
              refine ⟨109973075886468057147901363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146630767848624076197201817 109973075886468057147901363)
              ·
                refine ⟨164959613829702085721852045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109973075886468057147901363 164959613829702085721852045)
                ·
                  refine ⟨61859855186138282145694517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 164959613829702085721852045 61859855186138282145694517)
                  ·
                    refine ⟨5799361423700463951158861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61859855186138282145694517 5799361423700463951158861)
                    ·
                      refine ⟨2174760533887673981684573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5799361423700463951158861 2174760533887673981684573)
                      ·
                        rfl

theorem cell23_4235331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_4235331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235331 prefixEnd_4235331 := by exact prefixLift 4235331
  have htrace : WordTrace (prefixWord ++ tailWord_4235331) baseStart_4235331 baseEnd_4235331 := by
    simpa [prefixWord, tailWord_4235331, baseEnd_4235331] using wordTrace_append hprefix tailTrace_4235331
  have hstable : (prefixWord ++ tailWord_4235331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235331).length < 2 ^ (prefixWord ++ tailWord_4235331).sum := by decide
  have hdescent : baseEnd_4235331 < baseStart_4235331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235338 : List Nat := [3, 1, 2, 1, 1, 2, 1, 7, 5]
def baseStart_4235338 : Nat := 118140960795 + 4235338 * 2 ^ 59
def prefixEnd_4235338 : Nat := 4983230072969 + 3 ^ 40 * 4235338 * 2
def baseEnd_4235338 : Nat := 241640458694695050477449

theorem tailTrace_4235338 : CollatzResearch.WordTrace tailWord_4235338 prefixEnd_4235338 241640458694695050477449 := by
  unfold tailWord_4235338
  simp only [CollatzResearch.WordTrace]
  refine ⟨38618866882525309746904667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102983645020067492658412445 38618866882525309746904667)
  ·
    refine ⟨57928300323787964620357001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38618866882525309746904667 57928300323787964620357001)
    ·
      refine ⟨43446225242840973465267751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57928300323787964620357001 43446225242840973465267751)
      ·
        refine ⟨65169337864261460197901627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43446225242840973465267751 65169337864261460197901627)
        ·
          refine ⟨97754006796392190296852441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65169337864261460197901627 97754006796392190296852441)
          ·
            refine ⟨73315505097294142722639331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97754006796392190296852441 73315505097294142722639331)
            ·
              refine ⟨109973257645941214083958997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73315505097294142722639331 109973257645941214083958997)
              ·
                refine ⟨2577498226076747205092789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 109973257645941214083958997 2577498226076747205092789)
                ·
                  refine ⟨241640458694695050477449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2577498226076747205092789 241640458694695050477449)
                  ·
                    rfl

theorem cell23_4235338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 7, 5].length) (baseStart_4235338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235338 prefixEnd_4235338 := by exact prefixLift 4235338
  have htrace : WordTrace (prefixWord ++ tailWord_4235338) baseStart_4235338 baseEnd_4235338 := by
    simpa [prefixWord, tailWord_4235338, baseEnd_4235338] using wordTrace_append hprefix tailTrace_4235338
  have hstable : (prefixWord ++ tailWord_4235338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235338).length < 2 ^ (prefixWord ++ tailWord_4235338).sum := by decide
  have hdescent : baseEnd_4235338 < baseStart_4235338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235348 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_4235348 : Nat := 118140960795 + 4235348 * 2 ^ 59
def prefixEnd_4235348 : Nat := 4983230072969 + 3 ^ 40 * 4235348 * 2
def baseEnd_4235348 : Nat := 2174769263058800415171995

theorem tailTrace_4235348 : CollatzResearch.WordTrace tailWord_4235348 prefixEnd_4235348 2174769263058800415171995 := by
  unfold tailWord_4235348
  simp only [CollatzResearch.WordTrace]
  refine ⟨77237916130032505347741349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102983888173376673796988465 77237916130032505347741349)
  ·
    refine ⟨14482109274381094752701503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77237916130032505347741349 14482109274381094752701503)
    ·
      refine ⟨21723163911571642129052255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14482109274381094752701503 21723163911571642129052255)
      ·
        refine ⟨32584745867357463193578383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21723163911571642129052255 32584745867357463193578383)
        ·
          refine ⟨48877118801036194790367575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32584745867357463193578383 48877118801036194790367575)
          ·
            refine ⟨73315678201554292185551363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48877118801036194790367575 73315678201554292185551363)
            ·
              refine ⟨109973517302331438278327045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73315678201554292185551363 109973517302331438278327045)
              ·
                refine ⟨20620034494187144677186321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109973517302331438278327045 20620034494187144677186321)
                ·
                  refine ⟨15465025870640358507889741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20620034494187144677186321 15465025870640358507889741)
                  ·
                    refine ⟨5799384701490134440458653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15465025870640358507889741 5799384701490134440458653)
                    ·
                      refine ⟨2174769263058800415171995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5799384701490134440458653 2174769263058800415171995)
                      ·
                        rfl

theorem cell23_4235348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_4235348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235348 prefixEnd_4235348 := by exact prefixLift 4235348
  have htrace : WordTrace (prefixWord ++ tailWord_4235348) baseStart_4235348 baseEnd_4235348 := by
    simpa [prefixWord, tailWord_4235348, baseEnd_4235348] using wordTrace_append hprefix tailTrace_4235348
  have hstable : (prefixWord ++ tailWord_4235348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235348).length < 2 ^ (prefixWord ++ tailWord_4235348).sum := by decide
  have hdescent : baseEnd_4235348 < baseStart_4235348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235385 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 2, 5]
def baseStart_4235385 : Nat := 118140960795 + 4235385 * 2 ^ 59
def prefixEnd_4235385 : Nat := 4983230072969 + 3 ^ 40 * 4235385 * 2
def baseEnd_4235385 : Nat := 724929420614338923469775

theorem tailTrace_4235385 : CollatzResearch.WordTrace tailWord_4235385 prefixEnd_4235385 724929420614338923469775 := by
  unfold tailWord_4235385
  simp only [CollatzResearch.WordTrace]
  refine ⟨154477181760930966014579609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102984787840620644009719739 154477181760930966014579609)
  ·
    refine ⟨115857886320698224510934707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154477181760930966014579609 115857886320698224510934707)
    ·
      refine ⟨173786829481047336766402061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115857886320698224510934707 173786829481047336766402061)
      ·
        refine ⟨65170061055392751287400773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173786829481047336766402061 65170061055392751287400773)
        ·
          refine ⟨12219386447886140866387645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65170061055392751287400773 12219386447886140866387645)
          ·
            refine ⟨4582269917957302824895367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12219386447886140866387645 4582269917957302824895367)
            ·
              refine ⟨6873404876935954237343051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4582269917957302824895367 6873404876935954237343051)
              ·
                refine ⟨10310107315403931356014577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6873404876935954237343051 10310107315403931356014577)
                ·
                  refine ⟨7732580486552948517010933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10310107315403931356014577 7732580486552948517010933)
                  ·
                    refine ⟨724929420614338923469775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7732580486552948517010933 724929420614338923469775)
                    ·
                      rfl

theorem cell23_4235385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 5].length) (baseStart_4235385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235385 prefixEnd_4235385 := by exact prefixLift 4235385
  have htrace : WordTrace (prefixWord ++ tailWord_4235385) baseStart_4235385 baseEnd_4235385 := by
    simpa [prefixWord, tailWord_4235385, baseEnd_4235385] using wordTrace_append hprefix tailTrace_4235385
  have hstable : (prefixWord ++ tailWord_4235385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235385).length < 2 ^ (prefixWord ++ tailWord_4235385).sum := by decide
  have hdescent : baseEnd_4235385 < baseStart_4235385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235388 : List Nat := [2, 2, 2, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_4235388 : Nat := 118140960795 + 4235388 * 2 ^ 59
def prefixEnd_4235388 : Nat := 4983230072969 + 3 ^ 40 * 4235388 * 2
def baseEnd_4235388 : Nat := 2174789802284980258671811

theorem tailTrace_4235388 : CollatzResearch.WordTrace tailWord_4235388 prefixEnd_4235388 2174789802284980258671811 := by
  unfold tailWord_4235388
  simp only [CollatzResearch.WordTrace]
  refine ⟨77238645589960048763469409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102984860786613398351292545 77238645589960048763469409)
  ·
    refine ⟨57928984192470036572602057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77238645589960048763469409 57928984192470036572602057)
    ·
      refine ⟨43446738144352527429451543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57928984192470036572602057 43446738144352527429451543)
      ·
        refine ⟨65170107216528791144177315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43446738144352527429451543 65170107216528791144177315)
        ·
          refine ⟨97755160824793186716265973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65170107216528791144177315 97755160824793186716265973)
          ·
            refine ⟨9164546327324361254649935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97755160824793186716265973 9164546327324361254649935)
            ·
              refine ⟨13746819490986541881974903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9164546327324361254649935 13746819490986541881974903)
              ·
                refine ⟨20620229236479812822962355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13746819490986541881974903 20620229236479812822962355)
                ·
                  refine ⟨30930343854719719234443533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20620229236479812822962355 30930343854719719234443533)
                  ·
                    refine ⟨11598878945519894712916325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30930343854719719234443533 11598878945519894712916325)
                    ·
                      refine ⟨2174789802284980258671811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11598878945519894712916325 2174789802284980258671811)
                      ·
                        rfl

theorem cell23_4235388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_4235388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235388 prefixEnd_4235388 := by exact prefixLift 4235388
  have htrace : WordTrace (prefixWord ++ tailWord_4235388) baseStart_4235388 baseEnd_4235388 := by
    simpa [prefixWord, tailWord_4235388, baseEnd_4235388] using wordTrace_append hprefix tailTrace_4235388
  have hstable : (prefixWord ++ tailWord_4235388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235388).length < 2 ^ (prefixWord ++ tailWord_4235388).sum := by decide
  have hdescent : baseEnd_4235388 < baseStart_4235388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235401 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_4235401 : Nat := 118140960795 + 4235401 * 2 ^ 59
def prefixEnd_4235401 : Nat := 4983230072969 + 3 ^ 40 * 4235401 * 2
def baseEnd_4235401 : Nat := 2174796477533488707809251

theorem tailTrace_4235401 : CollatzResearch.WordTrace tailWord_4235401 prefixEnd_4235401 2174796477533488707809251 := by
  unfold tailWord_4235401
  simp only [CollatzResearch.WordTrace]
  refine ⟨154477765328873000747162057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102985176885915333831441371 154477765328873000747162057)
  ·
    refine ⟨115858323996654750560371543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154477765328873000747162057 115858323996654750560371543)
    ·
      refine ⟨173787485994982125840557315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115858323996654750560371543 173787485994982125840557315)
      ·
        refine ⟨260681228992473188760835973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173787485994982125840557315 260681228992473188760835973)
        ·
          refine ⟨48877730436088722892656745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 260681228992473188760835973 48877730436088722892656745)
          ·
            refine ⟨36658297827066542169492559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48877730436088722892656745 36658297827066542169492559)
            ·
              refine ⟨54987446740599813254238839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36658297827066542169492559 54987446740599813254238839)
              ·
                refine ⟨82481170110899719881358259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54987446740599813254238839 82481170110899719881358259)
                ·
                  refine ⟨123721755166349579822037389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82481170110899719881358259 123721755166349579822037389)
                  ·
                    refine ⟨46395658187381092433264021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 123721755166349579822037389 46395658187381092433264021)
                    ·
                      refine ⟨2174796477533488707809251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46395658187381092433264021 2174796477533488707809251)
                      ·
                        rfl

theorem cell23_4235401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_4235401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235401 prefixEnd_4235401 := by exact prefixLift 4235401
  have htrace : WordTrace (prefixWord ++ tailWord_4235401) baseStart_4235401 baseEnd_4235401 := by
    simpa [prefixWord, tailWord_4235401, baseEnd_4235401] using wordTrace_append hprefix tailTrace_4235401
  have hstable : (prefixWord ++ tailWord_4235401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235401).length < 2 ^ (prefixWord ++ tailWord_4235401).sum := by decide
  have hdescent : baseEnd_4235401 < baseStart_4235401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235408 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 3]
def baseStart_4235408 : Nat := 118140960795 + 4235408 * 2 ^ 59
def prefixEnd_4235408 : Nat := 4983230072969 + 3 ^ 40 * 4235408 * 2
def baseEnd_4235408 : Nat := 2174800071898070180421719

theorem tailTrace_4235408 : CollatzResearch.WordTrace tailWord_4235408 prefixEnd_4235408 2174800071898070180421719 := by
  unfold tailWord_4235408
  simp only [CollatzResearch.WordTrace]
  refine ⟨77239010319923820471333439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102985347093231760628444585 77239010319923820471333439)
  ·
    refine ⟨115858515479885730707000159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77239010319923820471333439 115858515479885730707000159)
    ·
      refine ⟨173787773219828596060500239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115858515479885730707000159 173787773219828596060500239)
      ·
        refine ⟨260681659829742894090750359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173787773219828596060500239 260681659829742894090750359)
        ·
          refine ⟨391022489744614341136125539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260681659829742894090750359 391022489744614341136125539)
          ·
            refine ⟨586533734616921511704188309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391022489744614341136125539 586533734616921511704188309)
            ·
              refine ⟨27493768810168195861133827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 586533734616921511704188309 27493768810168195861133827)
              ·
                refine ⟨41240653215252293791700741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27493768810168195861133827 41240653215252293791700741)
                ·
                  refine ⟨7732622477859805085943889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41240653215252293791700741 7732622477859805085943889)
                  ·
                    refine ⟨5799466858394853814457917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7732622477859805085943889 5799466858394853814457917)
                    ·
                      refine ⟨2174800071898070180421719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5799466858394853814457917 2174800071898070180421719)
                      ·
                        rfl

theorem cell23_4235408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 3].length) (baseStart_4235408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235408 prefixEnd_4235408 := by exact prefixLift 4235408
  have htrace : WordTrace (prefixWord ++ tailWord_4235408) baseStart_4235408 baseEnd_4235408 := by
    simpa [prefixWord, tailWord_4235408, baseEnd_4235408] using wordTrace_append hprefix tailTrace_4235408
  have hstable : (prefixWord ++ tailWord_4235408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235408).length < 2 ^ (prefixWord ++ tailWord_4235408).sum := by decide
  have hdescent : baseEnd_4235408 < baseStart_4235408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235488 : List Nat := [2, 1, 1, 3, 1, 3, 2, 3, 1, 6]
def baseStart_4235488 : Nat := 118140960795 + 4235488 * 2 ^ 59
def prefixEnd_4235488 : Nat := 4983230072969 + 3 ^ 40 * 4235488 * 2
def baseEnd_4235488 : Nat := 724947050116809955807117

theorem tailTrace_4235488 : CollatzResearch.WordTrace tailWord_4235488 prefixEnd_4235488 724947050116809955807117 := by
  unfold tailWord_4235488
  simp only [CollatzResearch.WordTrace]
  refine ⟨77240469239778907302789559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102987292319705209737052745 77240469239778907302789559)
  ·
    refine ⟨115860703859668360954184339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77240469239778907302789559 115860703859668360954184339)
    ·
      refine ⟨173791055789502541431276509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115860703859668360954184339 173791055789502541431276509)
      ·
        refine ⟨65171645921063453036728691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173791055789502541431276509 65171645921063453036728691)
        ·
          refine ⟨97757468881595179555093037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65171645921063453036728691 97757468881595179555093037)
          ·
            refine ⟨36659050830598192333159889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97757468881595179555093037 36659050830598192333159889)
            ·
              refine ⟨27494288122948644249869917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36659050830598192333159889 27494288122948644249869917)
              ·
                refine ⟨10310358046105741593701219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27494288122948644249869917 10310358046105741593701219)
                ·
                  refine ⟨15465537069158612390551829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10310358046105741593701219 15465537069158612390551829)
                  ·
                    refine ⟨724947050116809955807117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15465537069158612390551829 724947050116809955807117)
                    ·
                      rfl

theorem cell23_4235488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_4235488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235488 prefixEnd_4235488 := by exact prefixLift 4235488
  have htrace : WordTrace (prefixWord ++ tailWord_4235488) baseStart_4235488 baseEnd_4235488 := by
    simpa [prefixWord, tailWord_4235488, baseEnd_4235488] using wordTrace_append hprefix tailTrace_4235488
  have hstable : (prefixWord ++ tailWord_4235488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235488).length < 2 ^ (prefixWord ++ tailWord_4235488).sum := by decide
  have hdescent : baseEnd_4235488 < baseStart_4235488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235548 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_4235548 : Nat := 118140960795 + 4235548 * 2 ^ 59
def prefixEnd_4235548 : Nat := 4983230072969 + 3 ^ 40 * 4235548 * 2
def baseEnd_4235548 : Nat := 724957319729899877557025

theorem tailTrace_4235548 : CollatzResearch.WordTrace tailWord_4235548 prefixEnd_4235548 724957319729899877557025 := by
  unfold tailWord_4235548
  simp only [CollatzResearch.WordTrace]
  refine ⟨77241563429670222426381649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102988751239560296568508865 77241563429670222426381649)
  ·
    refine ⟨57931172572252666819786237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77241563429670222426381649 57931172572252666819786237)
    ·
      refine ⟨21724189714594750057419839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57931172572252666819786237 21724189714594750057419839)
      ·
        refine ⟨32586284571892125086129759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21724189714594750057419839 32586284571892125086129759)
        ·
          refine ⟨48879426857838187629194639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32586284571892125086129759 48879426857838187629194639)
          ·
            refine ⟨73319140286757281443791959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48879426857838187629194639 73319140286757281443791959)
            ·
              refine ⟨109978710430135922165687939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73319140286757281443791959 109978710430135922165687939)
              ·
                refine ⟨164968065645203883248531909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109978710430135922165687939 164968065645203883248531909)
                ·
                  refine ⟨30931512308475728109099733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164968065645203883248531909 30931512308475728109099733)
                  ·
                    refine ⟨724957319729899877557025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30931512308475728109099733 724957319729899877557025)
                    ·
                      rfl

theorem cell23_4235548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_4235548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235548 prefixEnd_4235548 := by exact prefixLift 4235548
  have htrace : WordTrace (prefixWord ++ tailWord_4235548) baseStart_4235548 baseEnd_4235548 := by
    simpa [prefixWord, tailWord_4235548, baseEnd_4235548] using wordTrace_append hprefix tailTrace_4235548
  have hstable : (prefixWord ++ tailWord_4235548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235548).length < 2 ^ (prefixWord ++ tailWord_4235548).sum := by decide
  have hdescent : baseEnd_4235548 < baseStart_4235548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235566 : List Nat := [4, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4235566 : Nat := 118140960795 + 4235566 * 2 ^ 59
def prefixEnd_4235566 : Nat := 4983230072969 + 3 ^ 40 * 4235566 * 2
def baseEnd_4235566 : Nat := 2174881201841480562245993

theorem tailTrace_4235566 : CollatzResearch.WordTrace tailWord_4235566 prefixEnd_4235566 2174881201841480562245993 := by
  unfold tailWord_4235566
  simp only [CollatzResearch.WordTrace]
  refine ⟨19310472921659404240864819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102989188915516822617945701 19310472921659404240864819)
  ·
    refine ⟨28965709382489106361297229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19310472921659404240864819 28965709382489106361297229)
    ·
      refine ⟨10862141018433414885486461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28965709382489106361297229 10862141018433414885486461)
      ·
        refine ⟨4073302881912530582057423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10862141018433414885486461 4073302881912530582057423)
        ·
          refine ⟨6109954322868795873086135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4073302881912530582057423 6109954322868795873086135)
          ·
            refine ⟨9164931484303193809629203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6109954322868795873086135 9164931484303193809629203)
            ·
              refine ⟨13747397226454790714443805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9164931484303193809629203 13747397226454790714443805)
              ·
                refine ⟨5155273959920546517916427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13747397226454790714443805 5155273959920546517916427)
                ·
                  refine ⟨7732910939880819776874641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5155273959920546517916427 7732910939880819776874641)
                  ·
                    refine ⟨5799683204910614832655981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7732910939880819776874641 5799683204910614832655981)
                    ·
                      refine ⟨2174881201841480562245993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5799683204910614832655981 2174881201841480562245993)
                      ·
                        rfl

theorem cell23_4235566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4235566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235566 prefixEnd_4235566 := by exact prefixLift 4235566
  have htrace : WordTrace (prefixWord ++ tailWord_4235566) baseStart_4235566 baseEnd_4235566 := by
    simpa [prefixWord, tailWord_4235566, baseEnd_4235566] using wordTrace_append hprefix tailTrace_4235566
  have hstable : (prefixWord ++ tailWord_4235566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235566).length < 2 ^ (prefixWord ++ tailWord_4235566).sum := by decide
  have hdescent : baseEnd_4235566 < baseStart_4235566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235568 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 4]
def baseStart_4235568 : Nat := 118140960795 + 4235568 * 2 ^ 59
def prefixEnd_4235568 : Nat := 4983230072969 + 3 ^ 40 * 4235568 * 2
def baseEnd_4235568 : Nat := 2174882228802789554420983

theorem tailTrace_4235568 : CollatzResearch.WordTrace tailWord_4235568 prefixEnd_4235568 2174882228802789554420983 := by
  unfold tailWord_4235568
  simp only [CollatzResearch.WordTrace]
  refine ⟨77241928159633994134245679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102989237546178658845660905 77241928159633994134245679)
  ·
    refine ⟨115862892239450991201368519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77241928159633994134245679 115862892239450991201368519)
    ·
      refine ⟨173794338359176486802052779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115862892239450991201368519 173794338359176486802052779)
      ·
        refine ⟨260691507538764730203079169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173794338359176486802052779 260691507538764730203079169)
        ·
          refine ⟨195518630654073547652309377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260691507538764730203079169 195518630654073547652309377)
          ·
            refine ⟨146638972990555160739232033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195518630654073547652309377 146638972990555160739232033)
            ·
              refine ⟨109979229742916370554424025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146638972990555160739232033 109979229742916370554424025)
              ·
                refine ⟨82484422307187277915818019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109979229742916370554424025 82484422307187277915818019)
                ·
                  refine ⟨123726633460780916873727029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82484422307187277915818019 123726633460780916873727029)
                  ·
                    refine ⟨11599371886948210956911909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 123726633460780916873727029 11599371886948210956911909)
                    ·
                      refine ⟨2174882228802789554420983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11599371886948210956911909 2174882228802789554420983)
                      ·
                        rfl

theorem cell23_4235568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_4235568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235568 prefixEnd_4235568 := by exact prefixLift 4235568
  have htrace : WordTrace (prefixWord ++ tailWord_4235568) baseStart_4235568 baseEnd_4235568 := by
    simpa [prefixWord, tailWord_4235568, baseEnd_4235568] using wordTrace_append hprefix tailTrace_4235568
  have hstable : (prefixWord ++ tailWord_4235568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235568).length < 2 ^ (prefixWord ++ tailWord_4235568).sum := by decide
  have hdescent : baseEnd_4235568 < baseStart_4235568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235608 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 9]
def baseStart_4235608 : Nat := 118140960795 + 4235608 * 2 ^ 59
def prefixEnd_4235608 : Nat := 4983230072969 + 3 ^ 40 * 4235608 * 2
def baseEnd_4235608 : Nat := 241655863114329933102311

theorem tailTrace_4235608 : CollatzResearch.WordTrace tailWord_4235608 prefixEnd_4235608 241655863114329933102311 := by
  unfold tailWord_4235608
  simp only [CollatzResearch.WordTrace]
  refine ⟨77242657619561537549973739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102990210159415383399964985 77242657619561537549973739)
  ·
    refine ⟨115863986429342306324960609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77242657619561537549973739 115863986429342306324960609)
    ·
      refine ⟨86897989822006729743720457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115863986429342306324960609 86897989822006729743720457)
      ·
        refine ⟨65173492366505047307790343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86897989822006729743720457 65173492366505047307790343)
        ·
          refine ⟨97760238549757570961685515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65173492366505047307790343 97760238549757570961685515)
          ·
            refine ⟨146640357824636356442528273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97760238549757570961685515 146640357824636356442528273)
            ·
              refine ⟨109980268368477267331896205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146640357824636356442528273 109980268368477267331896205)
              ·
                refine ⟨41242600638178975249461077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109980268368477267331896205 41242600638178975249461077)
                ·
                  refine ⟨241655863114329933102311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41242600638178975249461077 241655863114329933102311)
                  ·
                    rfl

theorem cell23_4235608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 9].length) (baseStart_4235608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235608 prefixEnd_4235608 := by exact prefixLift 4235608
  have htrace : WordTrace (prefixWord ++ tailWord_4235608) baseStart_4235608 baseEnd_4235608 := by
    simpa [prefixWord, tailWord_4235608, baseEnd_4235608] using wordTrace_append hprefix tailTrace_4235608
  have hstable : (prefixWord ++ tailWord_4235608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235608).length < 2 ^ (prefixWord ++ tailWord_4235608).sum := by decide
  have hdescent : baseEnd_4235608 < baseStart_4235608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235655 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 4, 5]
def baseStart_4235655 : Nat := 118140960795 + 4235655 * 2 ^ 59
def prefixEnd_4235655 : Nat := 4983230072969 + 3 ^ 40 * 4235655 * 2
def baseEnd_4235655 : Nat := 724975633873243571344361

theorem tailTrace_4235655 : CollatzResearch.WordTrace tailWord_4235655 prefixEnd_4235655 724975633873243571344361 := by
  unfold tailWord_4235655
  simp only [CollatzResearch.WordTrace]
  refine ⟨154487029469952802126908419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102991352979968534751272279 154487029469952802126908419)
  ·
    refine ⟨231730544204929203190362629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154487029469952802126908419 231730544204929203190362629)
    ·
      refine ⟨43449477038424225598192993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231730544204929203190362629 43449477038424225598192993)
      ·
        refine ⟨32587107778818169198644745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43449477038424225598192993 32587107778818169198644745)
        ·
          refine ⟨24440330834113626898983559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32587107778818169198644745 24440330834113626898983559)
          ·
            refine ⟨36660496251170440348475339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24440330834113626898983559 36660496251170440348475339)
            ·
              refine ⟨54990744376755660522713009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36660496251170440348475339 54990744376755660522713009)
              ·
                refine ⟨41243058282566745392034757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54990744376755660522713009 41243058282566745392034757)
                ·
                  refine ⟨7733073427981264761006517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41243058282566745392034757 7733073427981264761006517)
                  ·
                    refine ⟨724975633873243571344361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7733073427981264761006517 724975633873243571344361)
                    ·
                      rfl

theorem cell23_4235655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_4235655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235655 prefixEnd_4235655 := by exact prefixLift 4235655
  have htrace : WordTrace (prefixWord ++ tailWord_4235655) baseStart_4235655 baseEnd_4235655 := by
    simpa [prefixWord, tailWord_4235655, baseEnd_4235655] using wordTrace_append hprefix tailTrace_4235655
  have hstable : (prefixWord ++ tailWord_4235655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235655).length < 2 ^ (prefixWord ++ tailWord_4235655).sum := by decide
  have hdescent : baseEnd_4235655 < baseStart_4235655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235670 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4235670 : Nat := 118140960795 + 4235670 * 2 ^ 59
def prefixEnd_4235670 : Nat := 4983230072969 + 3 ^ 40 * 4235670 * 2
def baseEnd_4235670 : Nat := 2174934603829548155345515

theorem tailTrace_4235670 : CollatzResearch.WordTrace tailWord_4235670 prefixEnd_4235670 2174934603829548155345515 := by
  unfold tailWord_4235670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9655473535306153730544029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102991717709932306459136309 9655473535306153730544029)
  ·
    refine ⟨3620802575739807648954011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9655473535306153730544029 3620802575739807648954011)
    ·
      refine ⟨5431203863609711473431017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3620802575739807648954011 5431203863609711473431017)
      ·
        refine ⟨4073402897707283605073263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5431203863609711473431017 4073402897707283605073263)
        ·
          refine ⟨6110104346560925407609895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4073402897707283605073263 6110104346560925407609895)
          ·
            refine ⟨9165156519841388111414843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6110104346560925407609895 9165156519841388111414843)
            ·
              refine ⟨13747734779762082167122265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9165156519841388111414843 13747734779762082167122265)
              ·
                refine ⟨10310801084821561625341699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13747734779762082167122265 10310801084821561625341699)
                ·
                  refine ⟨15466201627232342438012549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10310801084821561625341699 15466201627232342438012549)
                  ·
                    refine ⟨2899912805106064207127353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15466201627232342438012549 2899912805106064207127353)
                    ·
                      refine ⟨2174934603829548155345515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899912805106064207127353 2174934603829548155345515)
                      ·
                        rfl

theorem cell23_4235670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4235670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235670 prefixEnd_4235670 := by exact prefixLift 4235670
  have htrace : WordTrace (prefixWord ++ tailWord_4235670) baseStart_4235670 baseEnd_4235670 := by
    simpa [prefixWord, tailWord_4235670, baseEnd_4235670] using wordTrace_append hprefix tailTrace_4235670
  have hstable : (prefixWord ++ tailWord_4235670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235670).length < 2 ^ (prefixWord ++ tailWord_4235670).sum := by decide
  have hdescent : baseEnd_4235670 < baseStart_4235670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235672 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 2, 5]
def baseStart_4235672 : Nat := 118140960795 + 4235672 * 2 ^ 59
def prefixEnd_4235672 : Nat := 4983230072969 + 3 ^ 40 * 4235672 * 2
def baseEnd_4235672 : Nat := 724978543596952382506835

theorem tailTrace_4235672 : CollatzResearch.WordTrace tailWord_4235672 prefixEnd_4235672 724978543596952382506835 := by
  unfold tailWord_4235672
  simp only [CollatzResearch.WordTrace]
  refine ⟨77243824755445607015138635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102991766340594142686851513 77243824755445607015138635)
  ·
    refine ⟨115865737133168410522707953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77243824755445607015138635 115865737133168410522707953)
    ·
      refine ⟨86899302849876307892030965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115865737133168410522707953 86899302849876307892030965)
      ·
        refine ⟨8146809642175903864877903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86899302849876307892030965 8146809642175903864877903)
        ·
          refine ⟨12220214463263855797316855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8146809642175903864877903 12220214463263855797316855)
          ·
            refine ⟨18330321694895783695975283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12220214463263855797316855 18330321694895783695975283)
            ·
              refine ⟨27495482542343675543962925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18330321694895783695975283 27495482542343675543962925)
              ·
                refine ⟨10310805953378878328986097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27495482542343675543962925 10310805953378878328986097)
                ·
                  refine ⟨7733104465034158746739573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10310805953378878328986097 7733104465034158746739573)
                  ·
                    refine ⟨724978543596952382506835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7733104465034158746739573 724978543596952382506835)
                    ·
                      rfl

theorem cell23_4235672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_4235672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235672 prefixEnd_4235672 := by exact prefixLift 4235672
  have htrace : WordTrace (prefixWord ++ tailWord_4235672) baseStart_4235672 baseEnd_4235672 := by
    simpa [prefixWord, tailWord_4235672, baseEnd_4235672] using wordTrace_append hprefix tailTrace_4235672
  have hstable : (prefixWord ++ tailWord_4235672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235672).length < 2 ^ (prefixWord ++ tailWord_4235672).sum := by decide
  have hdescent : baseEnd_4235672 < baseStart_4235672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235692 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 2, 4, 2]
def baseStart_4235692 : Nat := 118140960795 + 4235692 * 2 ^ 59
def prefixEnd_4235692 : Nat := 4983230072969 + 3 ^ 40 * 4235692 * 2
def baseEnd_4235692 : Nat := 2174945900403947069270413

theorem tailTrace_4235692 : CollatzResearch.WordTrace tailWord_4235692 prefixEnd_4235692 2174945900403947069270413 := by
  unfold tailWord_4235692
  simp only [CollatzResearch.WordTrace]
  refine ⟨77244189485409378723002665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102992252647212504964003553 77244189485409378723002665)
  ·
    refine ⟨57933142114057034042251999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77244189485409378723002665 57933142114057034042251999)
    ·
      refine ⟨86899713171085551063377999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57933142114057034042251999 86899713171085551063377999)
      ·
        refine ⟨130349569756628326595066999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86899713171085551063377999 130349569756628326595066999)
        ·
          refine ⟨195524354634942489892600499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130349569756628326595066999 195524354634942489892600499)
          ·
            refine ⟨293286531952413734838900749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195524354634942489892600499 293286531952413734838900749)
            ·
              refine ⟨109982449482155150564587781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293286531952413734838900749 109982449482155150564587781)
              ·
                refine ⟨20621709277904090730860209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109982449482155150564587781 20621709277904090730860209)
                ·
                  refine ⟨15466281958428068048145157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20621709277904090730860209 15466281958428068048145157)
                  ·
                    refine ⟨2899927867205262759027217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15466281958428068048145157 2899927867205262759027217)
                    ·
                      refine ⟨2174945900403947069270413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899927867205262759027217 2174945900403947069270413)
                      ·
                        rfl

theorem cell23_4235692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 4, 2].length) (baseStart_4235692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235692 prefixEnd_4235692 := by exact prefixLift 4235692
  have htrace : WordTrace (prefixWord ++ tailWord_4235692) baseStart_4235692 baseEnd_4235692 := by
    simpa [prefixWord, tailWord_4235692, baseEnd_4235692] using wordTrace_append hprefix tailTrace_4235692
  have hstable : (prefixWord ++ tailWord_4235692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235692).length < 2 ^ (prefixWord ++ tailWord_4235692).sum := by decide
  have hdescent : baseEnd_4235692 < baseStart_4235692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235693 : List Nat := [1, 5, 2, 2, 2, 2, 2, 2, 5]
def baseStart_4235693 : Nat := 118140960795 + 4235693 * 2 ^ 59
def prefixEnd_4235693 : Nat := 4983230072969 + 3 ^ 40 * 4235693 * 2
def baseEnd_4235693 : Nat := 241660712653844618373101

theorem tailTrace_4235693 : CollatzResearch.WordTrace tailWord_4235693 prefixEnd_4235693 241660712653844618373101 := by
  unfold tailWord_4235693
  simp only [CollatzResearch.WordTrace]
  refine ⟨154488415443815134616791733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102992276962543423077861155 154488415443815134616791733)
  ·
    refine ⟨14483288947857668870324225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154488415443815134616791733 14483288947857668870324225)
    ·
      refine ⟨10862466710893251652743169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14483288947857668870324225 10862466710893251652743169)
      ·
        refine ⟨8146850033169938739557377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10862466710893251652743169 8146850033169938739557377)
        ·
          refine ⟨6110137524877454054668033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8146850033169938739557377 6110137524877454054668033)
          ·
            refine ⟨4582603143658090541001025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6110137524877454054668033 4582603143658090541001025)
            ·
              refine ⟨3436952357743567905750769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4582603143658090541001025 3436952357743567905750769)
              ·
                refine ⟨2577714268307675929313077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3436952357743567905750769 2577714268307675929313077)
                ·
                  refine ⟨241660712653844618373101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2577714268307675929313077 241660712653844618373101)
                  ·
                    rfl

theorem cell23_4235693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_4235693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235693 prefixEnd_4235693 := by exact prefixLift 4235693
  have htrace : WordTrace (prefixWord ++ tailWord_4235693) baseStart_4235693 baseEnd_4235693 := by
    simpa [prefixWord, tailWord_4235693, baseEnd_4235693] using wordTrace_append hprefix tailTrace_4235693
  have hstable : (prefixWord ++ tailWord_4235693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235693).length < 2 ^ (prefixWord ++ tailWord_4235693).sum := by decide
  have hdescent : baseEnd_4235693 < baseStart_4235693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235695 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 3]
def baseStart_4235695 : Nat := 118140960795 + 4235695 * 2 ^ 59
def prefixEnd_4235695 : Nat := 4983230072969 + 3 ^ 40 * 4235695 * 2
def baseEnd_4235695 : Nat := 2174947440845910557532899

theorem tailTrace_4235695 : CollatzResearch.WordTrace tailWord_4235695 prefixEnd_4235695 2174947440845910557532899 := by
  unfold tailWord_4235695
  simp only [CollatzResearch.WordTrace]
  refine ⟨154488488389807888958364539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102992325593205259305576359 154488488389807888958364539)
  ·
    refine ⟨231732732584711833437546809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154488488389807888958364539 231732732584711833437546809)
    ·
      refine ⟨173799549438533875078160107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231732732584711833437546809 173799549438533875078160107)
      ·
        refine ⟨260699324157800812617240161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173799549438533875078160107 260699324157800812617240161)
        ·
          refine ⟨195524493118350609462930121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260699324157800812617240161 195524493118350609462930121)
          ·
            refine ⟨146643369838762957097197591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195524493118350609462930121 146643369838762957097197591)
            ·
              refine ⟨219965054758144435645796387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146643369838762957097197591 219965054758144435645796387)
              ·
                refine ⟨329947582137216653468694581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 219965054758144435645796387 329947582137216653468694581)
                ·
                  refine ⟨30932585825364061262690117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 329947582137216653468694581 30932585825364061262690117)
                  ·
                    refine ⟨5799859842255761486754397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30932585825364061262690117 5799859842255761486754397)
                    ·
                      refine ⟨2174947440845910557532899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5799859842255761486754397 2174947440845910557532899)
                      ·
                        rfl

theorem cell23_4235695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 3].length) (baseStart_4235695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235695 prefixEnd_4235695 := by exact prefixLift 4235695
  have htrace : WordTrace (prefixWord ++ tailWord_4235695) baseStart_4235695 baseEnd_4235695 := by
    simpa [prefixWord, tailWord_4235695, baseEnd_4235695] using wordTrace_append hprefix tailTrace_4235695
  have hstable : (prefixWord ++ tailWord_4235695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235695).length < 2 ^ (prefixWord ++ tailWord_4235695).sum := by decide
  have hdescent : baseEnd_4235695 < baseStart_4235695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235709 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 2, 4, 2]
def baseStart_4235709 : Nat := 118140960795 + 4235709 * 2 ^ 59
def prefixEnd_4235709 : Nat := 4983230072969 + 3 ^ 40 * 4235709 * 2
def baseEnd_4235709 : Nat := 2174954629575073502757835

theorem tailTrace_4235709 : CollatzResearch.WordTrace tailWord_4235709 prefixEnd_4235709 2174954629575073502757835 := by
  unfold tailWord_4235709
  simp only [CollatzResearch.WordTrace]
  refine ⟨154488999011757169349374181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102992666007838112899582787 154488999011757169349374181)
  ·
    refine ⟨28966687314704469253007659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154488999011757169349374181 28966687314704469253007659)
    ·
      refine ⟨43450030972056703879511489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28966687314704469253007659 43450030972056703879511489)
      ·
        refine ⟨32587523229042527909633617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43450030972056703879511489 32587523229042527909633617)
        ·
          refine ⟨24440642421781895932225213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32587523229042527909633617 24440642421781895932225213)
          ·
            refine ⟨9165240908168210974584455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24440642421781895932225213 9165240908168210974584455)
            ·
              refine ⟨13747861362252316461876683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9165240908168210974584455 13747861362252316461876683)
              ·
                refine ⟨20621792043378474692815025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13747861362252316461876683 20621792043378474692815025)
                ·
                  refine ⟨15466344032533856019611269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20621792043378474692815025 15466344032533856019611269)
                  ·
                    refine ⟨2899939506100098003677113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15466344032533856019611269 2899939506100098003677113)
                    ·
                      refine ⟨2174954629575073502757835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2899939506100098003677113 2174954629575073502757835)
                      ·
                        rfl

theorem cell23_4235709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_4235709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235709 prefixEnd_4235709 := by exact prefixLift 4235709
  have htrace : WordTrace (prefixWord ++ tailWord_4235709) baseStart_4235709 baseEnd_4235709 := by
    simpa [prefixWord, tailWord_4235709, baseEnd_4235709] using wordTrace_append hprefix tailTrace_4235709
  have hstable : (prefixWord ++ tailWord_4235709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235709).length < 2 ^ (prefixWord ++ tailWord_4235709).sum := by decide
  have hdescent : baseEnd_4235709 < baseStart_4235709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235796 : List Nat := [2, 4, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_4235796 : Nat := 118140960795 + 4235796 * 2 ^ 59
def prefixEnd_4235796 : Nat := 4983230072969 + 3 ^ 40 * 4235796 * 2
def baseEnd_4235796 : Nat := 724999767464004887456645

theorem tailTrace_4235796 : CollatzResearch.WordTrace tailWord_4235796 prefixEnd_4235796 724999767464004887456645 := by
  unfold tailWord_4235796
  simp only [CollatzResearch.WordTrace]
  refine ⟨77246086081220991603895621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102994781441627988805194161 77246086081220991603895621)
  ·
    refine ⟨14483641140228935925730429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77246086081220991603895621 14483641140228935925730429)
    ·
      refine ⟨5431365427585850972148911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14483641140228935925730429 5431365427585850972148911)
      ·
        refine ⟨8147048141378776458223367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5431365427585850972148911 8147048141378776458223367)
        ·
          refine ⟨12220572212068164687335051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8147048141378776458223367 12220572212068164687335051)
          ·
            refine ⟨18330858318102247031002577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12220572212068164687335051 18330858318102247031002577)
            ·
              refine ⟨13748143738576685273251933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18330858318102247031002577 13748143738576685273251933)
              ·
                refine ⟨5155553901966256977469475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13748143738576685273251933 5155553901966256977469475)
                ·
                  refine ⟨7733330852949385466204213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5155553901966256977469475 7733330852949385466204213)
                  ·
                    refine ⟨724999767464004887456645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7733330852949385466204213 724999767464004887456645)
                    ·
                      rfl

theorem cell23_4235796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_4235796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235796 prefixEnd_4235796 := by exact prefixLift 4235796
  have htrace : WordTrace (prefixWord ++ tailWord_4235796) baseStart_4235796 baseEnd_4235796 := by
    simpa [prefixWord, tailWord_4235796, baseEnd_4235796] using wordTrace_append hprefix tailTrace_4235796
  have hstable : (prefixWord ++ tailWord_4235796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235796).length < 2 ^ (prefixWord ++ tailWord_4235796).sum := by decide
  have hdescent : baseEnd_4235796 < baseStart_4235796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235802 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_4235802 : Nat := 118140960795 + 4235802 * 2 ^ 59
def prefixEnd_4235802 : Nat := 4983230072969 + 3 ^ 40 * 4235802 * 2
def baseEnd_4235802 : Nat := 2175002383275941638894907

theorem tailTrace_4235802 : CollatzResearch.WordTrace tailWord_4235802 prefixEnd_4235802 2175002383275941638894907 := by
  unfold tailWord_4235802
  simp only [CollatzResearch.WordTrace]
  refine ⟨38623097750105061558127415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102994927333613497488339773 38623097750105061558127415)
  ·
    refine ⟨57934646625157592337191123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38623097750105061558127415 57934646625157592337191123)
    ·
      refine ⟨86901969937736388505786685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57934646625157592337191123 86901969937736388505786685)
      ·
        refine ⟨32588238726651145689670007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86901969937736388505786685 32588238726651145689670007)
        ·
          refine ⟨48882358089976718534505011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32588238726651145689670007 48882358089976718534505011)
          ·
            refine ⟨73323537134965077801757517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48882358089976718534505011 73323537134965077801757517)
            ·
              refine ⟨27496326425611904175659069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73323537134965077801757517 27496326425611904175659069)
              ·
                refine ⟨10311122409604464065872151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27496326425611904175659069 10311122409604464065872151)
                ·
                  refine ⟨15466683614406696098808227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10311122409604464065872151 15466683614406696098808227)
                  ·
                    refine ⟨23200025421610044148212341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15466683614406696098808227 23200025421610044148212341)
                    ·
                      refine ⟨2175002383275941638894907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23200025421610044148212341 2175002383275941638894907)
                      ·
                        rfl

theorem cell23_4235802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_4235802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235802 prefixEnd_4235802 := by exact prefixLift 4235802
  have htrace : WordTrace (prefixWord ++ tailWord_4235802) baseStart_4235802 baseEnd_4235802 := by
    simpa [prefixWord, tailWord_4235802, baseEnd_4235802] using wordTrace_append hprefix tailTrace_4235802
  have hstable : (prefixWord ++ tailWord_4235802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235802).length < 2 ^ (prefixWord ++ tailWord_4235802).sum := by decide
  have hdescent : baseEnd_4235802 < baseStart_4235802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235809 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 2, 4]
def baseStart_4235809 : Nat := 118140960795 + 4235809 * 2 ^ 59
def prefixEnd_4235809 : Nat := 4983230072969 + 3 ^ 40 * 4235809 * 2
def baseEnd_4235809 : Nat := 725001992546841037169125

theorem tailTrace_4235809 : CollatzResearch.WordTrace tailWord_4235809 prefixEnd_4235809 725001992546841037169125 := by
  unfold tailWord_4235809
  simp only [CollatzResearch.WordTrace]
  refine ⟨154492646311394886428014481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102995097540929924285342987 154492646311394886428014481)
  ·
    refine ⟨115869484733546164821010861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154492646311394886428014481 115869484733546164821010861)
    ·
      refine ⟨43451056775079811807879073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115869484733546164821010861 43451056775079811807879073)
      ·
        refine ⟨32588292581309858855909305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43451056775079811807879073 32588292581309858855909305)
        ·
          refine ⟨24441219435982394141931979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32588292581309858855909305 24441219435982394141931979)
          ·
            refine ⟨36661829153973591212897969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24441219435982394141931979 36661829153973591212897969)
            ·
              refine ⟨27496371865480193409673477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36661829153973591212897969 27496371865480193409673477)
              ·
                refine ⟨5155569724777536264313777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27496371865480193409673477 5155569724777536264313777)
                ·
                  refine ⟨3866677293583152198235333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5155569724777536264313777 3866677293583152198235333)
                  ·
                    refine ⟨725001992546841037169125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3866677293583152198235333 725001992546841037169125)
                    ·
                      rfl

theorem cell23_4235809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_4235809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235809 prefixEnd_4235809 := by exact prefixLift 4235809
  have htrace : WordTrace (prefixWord ++ tailWord_4235809) baseStart_4235809 baseEnd_4235809 := by
    simpa [prefixWord, tailWord_4235809, baseEnd_4235809] using wordTrace_append hprefix tailTrace_4235809
  have hstable : (prefixWord ++ tailWord_4235809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235809).length < 2 ^ (prefixWord ++ tailWord_4235809).sum := by decide
  have hdescent : baseEnd_4235809 < baseStart_4235809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235826 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 2, 4]
def baseStart_4235826 : Nat := 118140960795 + 4235826 * 2 ^ 59
def prefixEnd_4235826 : Nat := 4983230072969 + 3 ^ 40 * 4235826 * 2
def baseEnd_4235826 : Nat := 725004902270549848331599

theorem tailTrace_4235826 : CollatzResearch.WordTrace tailWord_4235826 prefixEnd_4235826 725004902270549848331599 := by
  unfold tailWord_4235826
  simp only [CollatzResearch.WordTrace]
  refine ⟨38623316588083324582845833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102995510901555532220922221 38623316588083324582845833)
  ·
    refine ⟨28967487441062493437134375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38623316588083324582845833 28967487441062493437134375)
    ·
      refine ⟨43451231161593740155701563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28967487441062493437134375 43451231161593740155701563)
      ·
        refine ⟨65176846742390610233552345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43451231161593740155701563 65176846742390610233552345)
        ·
          refine ⟨48882635056792957675164259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65176846742390610233552345 48882635056792957675164259)
          ·
            refine ⟨73323952585189436512746389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48882635056792957675164259 73323952585189436512746389)
            ·
              refine ⟨3437060277430754836534987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 73323952585189436512746389 3437060277430754836534987)
              ·
                refine ⟨5155590416146132254802481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3437060277430754836534987 5155590416146132254802481)
                ·
                  refine ⟨3866692812109599191101861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5155590416146132254802481 3866692812109599191101861)
                  ·
                    refine ⟨725004902270549848331599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3866692812109599191101861 725004902270549848331599)
                    ·
                      rfl

theorem cell23_4235826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_4235826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235826 prefixEnd_4235826 := by exact prefixLift 4235826
  have htrace : WordTrace (prefixWord ++ tailWord_4235826) baseStart_4235826 baseEnd_4235826 := by
    simpa [prefixWord, tailWord_4235826, baseEnd_4235826] using wordTrace_append hprefix tailTrace_4235826
  have hstable : (prefixWord ++ tailWord_4235826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235826).length < 2 ^ (prefixWord ++ tailWord_4235826).sum := by decide
  have hdescent : baseEnd_4235826 < baseStart_4235826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235836 : List Nat := [2, 2, 2, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_4235836 : Nat := 118140960795 + 4235836 * 2 ^ 59
def prefixEnd_4235836 : Nat := 4983230072969 + 3 ^ 40 * 4235836 * 2
def baseEnd_4235836 : Nat := 2175019841618194505869751

theorem tailTrace_4235836 : CollatzResearch.WordTrace tailWord_4235836 prefixEnd_4235836 2175019841618194505869751 := by
  unfold tailWord_4235836
  simp only [CollatzResearch.WordTrace]
  refine ⟨77246815541148535019623681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102995754054864713359498241 77246815541148535019623681)
  ·
    refine ⟨57935111655861401264717761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77246815541148535019623681 57935111655861401264717761)
    ·
      refine ⟨43451333741896050948538321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57935111655861401264717761 43451333741896050948538321)
      ·
        refine ⟨32588500306422038211403741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43451333741896050948538321 32588500306422038211403741)
        ·
          refine ⟨12220687614908264329276403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32588500306422038211403741 12220687614908264329276403)
          ·
            refine ⟨18331031422362396493914605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12220687614908264329276403 18331031422362396493914605)
            ·
              refine ⟨6874136783385898685217977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18331031422362396493914605 6874136783385898685217977)
              ·
                refine ⟨5155602587539424013913483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6874136783385898685217977 5155602587539424013913483)
                ·
                  refine ⟨7733403881309136020870225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5155602587539424013913483 7733403881309136020870225)
                  ·
                    refine ⟨5800052910981852015652669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7733403881309136020870225 5800052910981852015652669)
                    ·
                      refine ⟨2175019841618194505869751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5800052910981852015652669 2175019841618194505869751)
                      ·
                        rfl

theorem cell23_4235836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_4235836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235836 prefixEnd_4235836 := by exact prefixLift 4235836
  have htrace : WordTrace (prefixWord ++ tailWord_4235836) baseStart_4235836 baseEnd_4235836 := by
    simpa [prefixWord, tailWord_4235836, baseEnd_4235836] using wordTrace_append hprefix tailTrace_4235836
  have hstable : (prefixWord ++ tailWord_4235836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235836).length < 2 ^ (prefixWord ++ tailWord_4235836).sum := by decide
  have hdescent : baseEnd_4235836 < baseStart_4235836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235846 : List Nat := [6, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4]
def baseStart_4235846 : Nat := 118140960795 + 4235846 * 2 ^ 59
def prefixEnd_4235846 : Nat := 4983230072969 + 3 ^ 40 * 4235846 * 2
def baseEnd_4235846 : Nat := 2175024976424739466744705

theorem tailTrace_4235846 : CollatzResearch.WordTrace tailWord_4235846 prefixEnd_4235846 2175024976424739466744705 := by
  unfold tailWord_4235846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4827937369133151304597231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 102995997208173894498074261 4827937369133151304597231)
  ·
    refine ⟨7241906053699726956895847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4827937369133151304597231 7241906053699726956895847)
    ·
      refine ⟨10862859080549590435343771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7241906053699726956895847 10862859080549590435343771)
      ·
        refine ⟨16294288620824385653015657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10862859080549590435343771 16294288620824385653015657)
        ·
          refine ⟨12220716465618289239761743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16294288620824385653015657 12220716465618289239761743)
          ·
            refine ⟨18331074698427433859642615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12220716465618289239761743 18331074698427433859642615)
            ·
              refine ⟨27496612047641150789463923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18331074698427433859642615 27496612047641150789463923)
              ·
                refine ⟨41244918071461726184195885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27496612047641150789463923 41244918071461726184195885)
                ·
                  refine ⟨15466844276798147319073457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41244918071461726184195885 15466844276798147319073457)
                  ·
                    refine ⟨11600133207598610489305093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15466844276798147319073457 11600133207598610489305093)
                    ·
                      refine ⟨2175024976424739466744705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11600133207598610489305093 2175024976424739466744705)
                      ·
                        rfl

theorem cell23_4235846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_4235846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235846 prefixEnd_4235846 := by exact prefixLift 4235846
  have htrace : WordTrace (prefixWord ++ tailWord_4235846) baseStart_4235846 baseEnd_4235846 := by
    simpa [prefixWord, tailWord_4235846, baseEnd_4235846] using wordTrace_append hprefix tailTrace_4235846
  have hstable : (prefixWord ++ tailWord_4235846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235846).length < 2 ^ (prefixWord ++ tailWord_4235846).sum := by decide
  have hdescent : baseEnd_4235846 < baseStart_4235846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235872 : List Nat := [2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 4]
def baseStart_4235872 : Nat := 118140960795 + 4235872 * 2 ^ 59
def prefixEnd_4235872 : Nat := 4983230072969 + 3 ^ 40 * 4235872 * 2
def baseEnd_4235872 : Nat := 2175038326921756365019585

theorem tailTrace_4235872 : CollatzResearch.WordTrace tailWord_4235872 prefixEnd_4235872 2175038326921756365019585 := by
  unfold tailWord_4235872
  simp only [CollatzResearch.WordTrace]
  refine ⟨77247472055083324093778935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102996629406777765458371913 77247472055083324093778935)
  ·
    refine ⟨115871208082624986140668403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77247472055083324093778935 115871208082624986140668403)
    ·
      refine ⟨173806812123937479211002605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115871208082624986140668403 173806812123937479211002605)
      ·
        refine ⟨65177554546476554704125977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173806812123937479211002605 65177554546476554704125977)
        ·
          refine ⟨48883165909857416028094483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65177554546476554704125977 48883165909857416028094483)
          ·
            refine ⟨73324748864786124042141725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48883165909857416028094483 73324748864786124042141725)
            ·
              refine ⟨27496780824294796515803147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73324748864786124042141725 27496780824294796515803147)
              ·
                refine ⟨41245171236442194773704721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27496780824294796515803147 41245171236442194773704721)
                ·
                  refine ⟨30933878427331646080278541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41245171236442194773704721 30933878427331646080278541)
                  ·
                    refine ⟨11600204410249367280104453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30933878427331646080278541 11600204410249367280104453)
                    ·
                      refine ⟨2175038326921756365019585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11600204410249367280104453 2175038326921756365019585)
                      ·
                        rfl

theorem cell23_4235872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_4235872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235872 prefixEnd_4235872 := by exact prefixLift 4235872
  have htrace : WordTrace (prefixWord ++ tailWord_4235872) baseStart_4235872 baseEnd_4235872 := by
    simpa [prefixWord, tailWord_4235872, baseEnd_4235872] using wordTrace_append hprefix tailTrace_4235872
  have hstable : (prefixWord ++ tailWord_4235872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235872).length < 2 ^ (prefixWord ++ tailWord_4235872).sum := by decide
  have hdescent : baseEnd_4235872 < baseStart_4235872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235929 : List Nat := [1, 2, 1, 2, 1, 2, 3, 6, 5]
def baseStart_4235929 : Nat := 118140960795 + 4235929 * 2 ^ 59
def prefixEnd_4235929 : Nat := 4983230072969 + 3 ^ 40 * 4235929 * 2
def baseEnd_4235929 : Nat := 241674177257673626889647

theorem tailTrace_4235929 : CollatzResearch.WordTrace tailWord_4235929 prefixEnd_4235929 241674177257673626889647 := by
  unfold tailWord_4235929
  simp only [CollatzResearch.WordTrace]
  refine ⟨154497023070960146922382841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102998015380640097948255227 154497023070960146922382841)
  ·
    refine ⟨115872767303220110191787131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154497023070960146922382841 115872767303220110191787131)
    ·
      refine ⟨173809150954830165287680697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115872767303220110191787131 173809150954830165287680697)
      ·
        refine ⟨130356863216122623965760523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173809150954830165287680697 130356863216122623965760523)
        ·
          refine ⟨195535294824183935948640785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130356863216122623965760523 195535294824183935948640785)
          ·
            refine ⟨146651471118137951961480589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195535294824183935948640785 146651471118137951961480589)
            ·
              refine ⟨54994301669301731985555221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 146651471118137951961480589 54994301669301731985555221)
              ·
                refine ⟨2577857890748518686822901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54994301669301731985555221 2577857890748518686822901)
                ·
                  refine ⟨241674177257673626889647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2577857890748518686822901 241674177257673626889647)
                  ·
                    rfl

theorem cell23_4235929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 6, 5].length) (baseStart_4235929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235929 prefixEnd_4235929 := by exact prefixLift 4235929
  have htrace : WordTrace (prefixWord ++ tailWord_4235929) baseStart_4235929 baseEnd_4235929 := by
    simpa [prefixWord, tailWord_4235929, baseEnd_4235929] using wordTrace_append hprefix tailTrace_4235929
  have hstable : (prefixWord ++ tailWord_4235929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235929).length < 2 ^ (prefixWord ++ tailWord_4235929).sum := by decide
  have hdescent : baseEnd_4235929 < baseStart_4235929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235940 : List Nat := [2, 3, 1, 2, 2, 1, 5, 1, 2, 2, 2]
def baseStart_4235940 : Nat := 118140960795 + 4235940 * 2 ^ 59
def prefixEnd_4235940 : Nat := 4983230072969 + 3 ^ 40 * 4235940 * 2
def baseEnd_4235940 : Nat := 2175073243606262098969273

theorem tailTrace_4235940 : CollatzResearch.WordTrace tailWord_4235940 prefixEnd_4235940 2175073243606262098969273 := by
  unfold tailWord_4235940
  simp only [CollatzResearch.WordTrace]
  refine ⟨77248712136960147900516637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102998282849280197200688849 77248712136960147900516637)
  ·
    refine ⟨28968267051360055462693739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77248712136960147900516637 28968267051360055462693739)
    ·
      refine ⟨43452400577040083194040609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28968267051360055462693739 43452400577040083194040609)
      ·
        refine ⟨32589300432780062395530457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43452400577040083194040609 32589300432780062395530457)
        ·
          refine ⟨24441975324585046796647843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32589300432780062395530457 24441975324585046796647843)
          ·
            refine ⟨36662962986877570194971765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24441975324585046796647843 36662962986877570194971765)
            ·
              refine ⟨3437152780019772205778603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36662962986877570194971765 3437152780019772205778603)
              ·
                refine ⟨5155729170029658308667905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3437152780019772205778603 5155729170029658308667905)
                ·
                  refine ⟨3866796877522243731500929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5155729170029658308667905 3866796877522243731500929)
                  ·
                    refine ⟨2900097658141682798625697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3866796877522243731500929 2900097658141682798625697)
                    ·
                      refine ⟨2175073243606262098969273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2900097658141682798625697 2175073243606262098969273)
                      ·
                        rfl

theorem cell23_4235940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_4235940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235940 prefixEnd_4235940 := by exact prefixLift 4235940
  have htrace : WordTrace (prefixWord ++ tailWord_4235940) baseStart_4235940 baseEnd_4235940 := by
    simpa [prefixWord, tailWord_4235940, baseEnd_4235940] using wordTrace_append hprefix tailTrace_4235940
  have hstable : (prefixWord ++ tailWord_4235940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235940).length < 2 ^ (prefixWord ++ tailWord_4235940).sum := by decide
  have hdescent : baseEnd_4235940 < baseStart_4235940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235952 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_4235952 : Nat := 118140960795 + 4235952 * 2 ^ 59
def prefixEnd_4235952 : Nat := 4983230072969 + 3 ^ 40 * 4235952 * 2
def baseEnd_4235952 : Nat := 2175079405374116052019217

theorem tailTrace_4235952 : CollatzResearch.WordTrace tailWord_4235952 prefixEnd_4235952 2175079405374116052019217 := by
  unfold tailWord_4235952
  simp only [CollatzResearch.WordTrace]
  refine ⟨77248930974938410925235055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102998574633251214566980073 77248930974938410925235055)
  ·
    refine ⟨115873396462407616387852583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77248930974938410925235055 115873396462407616387852583)
    ·
      refine ⟨173810094693611424581778875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115873396462407616387852583 173810094693611424581778875)
      ·
        refine ⟨260715142040417136872668313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173810094693611424581778875 260715142040417136872668313)
        ·
          refine ⟨195536356530312852654501235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260715142040417136872668313 195536356530312852654501235)
          ·
            refine ⟨293304534795469278981751853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195536356530312852654501235 293304534795469278981751853)
            ·
              refine ⟨109989200548300979618156945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 293304534795469278981751853 109989200548300979618156945)
              ·
                refine ⟨82491900411225734713617709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109989200548300979618156945 82491900411225734713617709)
                ·
                  refine ⟨30934462654209650517606641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82491900411225734713617709 30934462654209650517606641)
                  ·
                    refine ⟨23200846990657237888204981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30934462654209650517606641 23200846990657237888204981)
                    ·
                      refine ⟨2175079405374116052019217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23200846990657237888204981 2175079405374116052019217)
                      ·
                        rfl

theorem cell23_4235952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_4235952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235952 prefixEnd_4235952 := by exact prefixLift 4235952
  have htrace : WordTrace (prefixWord ++ tailWord_4235952) baseStart_4235952 baseEnd_4235952 := by
    simpa [prefixWord, tailWord_4235952, baseEnd_4235952] using wordTrace_append hprefix tailTrace_4235952
  have hstable : (prefixWord ++ tailWord_4235952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235952).length < 2 ^ (prefixWord ++ tailWord_4235952).sum := by decide
  have hdescent : baseEnd_4235952 < baseStart_4235952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4235986 : List Nat := [3, 2, 2, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_4235986 : Nat := 118140960795 + 4235986 * 2 ^ 59
def prefixEnd_4235986 : Nat := 4983230072969 + 3 ^ 40 * 4235986 * 2
def baseEnd_4235986 : Nat := 2175096863716368918994061

theorem tailTrace_4235986 : CollatzResearch.WordTrace tailWord_4235986 prefixEnd_4235986 2175096863716368918994061 := by
  unfold tailWord_4235986
  simp only [CollatzResearch.WordTrace]
  refine ⟨38624775507938411414301953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102999401354502430438138541 38624775507938411414301953)
  ·
    refine ⟨28968581630953808560726465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38624775507938411414301953 28968581630953808560726465)
    ·
      refine ⟨21726436223215356420544849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28968581630953808560726465 21726436223215356420544849)
      ·
        refine ⟨16294827167411517315408637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21726436223215356420544849 16294827167411517315408637)
        ·
          refine ⟨6110560187779318993278239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16294827167411517315408637 6110560187779318993278239)
          ·
            refine ⟨9165840281668978489917359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6110560187779318993278239 9165840281668978489917359)
            ·
              refine ⟨13748760422503467734876039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9165840281668978489917359 13748760422503467734876039)
              ·
                refine ⟨20623140633755201602314059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13748760422503467734876039 20623140633755201602314059)
                ·
                  refine ⟨30934710950632802403471089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20623140633755201602314059 30934710950632802403471089)
                  ·
                    refine ⟨23201033212974601802603317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30934710950632802403471089 23201033212974601802603317)
                    ·
                      refine ⟨2175096863716368918994061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23201033212974601802603317 2175096863716368918994061)
                      ·
                        rfl

theorem cell23_4235986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_4235986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4235986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4235986 prefixEnd_4235986 := by exact prefixLift 4235986
  have htrace : WordTrace (prefixWord ++ tailWord_4235986) baseStart_4235986 baseEnd_4235986 := by
    simpa [prefixWord, tailWord_4235986, baseEnd_4235986] using wordTrace_append hprefix tailTrace_4235986
  have hstable : (prefixWord ++ tailWord_4235986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4235986).length < 2 ^ (prefixWord ++ tailWord_4235986).sum := by decide
  have hdescent : baseEnd_4235986 < baseStart_4235986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4235986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236016 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 3]
def baseStart_4236016 : Nat := 118140960795 + 4236016 * 2 ^ 59
def prefixEnd_4236016 : Nat := 4983230072969 + 3 ^ 40 * 4236016 * 2
def baseEnd_4236016 : Nat := 2175112268136003801618923

theorem tailTrace_4236016 : CollatzResearch.WordTrace tailWord_4236016 prefixEnd_4236016 2175112268136003801618923 := by
  unfold tailWord_4236016
  simp only [CollatzResearch.WordTrace]
  refine ⟨77250098110822480390399951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103000130814429973853866601 77250098110822480390399951)
  ·
    refine ⟨115875147166233720585599927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77250098110822480390399951 115875147166233720585599927)
    ·
      refine ⟨173812720749350580878399891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115875147166233720585599927 173812720749350580878399891)
      ·
        refine ⟨260719081124025871317599837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173812720749350580878399891 260719081124025871317599837)
        ·
          refine ⟨97769655421509701744099939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260719081124025871317599837 97769655421509701744099939)
          ·
            refine ⟨146654483132264552616149909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97769655421509701744099939 146654483132264552616149909)
            ·
              refine ⟨6874428896824900903882027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 146654483132264552616149909 6874428896824900903882027)
              ·
                refine ⟨10311643345237351355823041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6874428896824900903882027 10311643345237351355823041)
                ·
                  refine ⟨7733732508928013516867281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10311643345237351355823041 7733732508928013516867281)
                  ·
                    refine ⟨5800299381696010137650461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7733732508928013516867281 5800299381696010137650461)
                    ·
                      refine ⟨2175112268136003801618923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5800299381696010137650461 2175112268136003801618923)
                      ·
                        rfl

theorem cell23_4236016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 3].length) (baseStart_4236016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236016 prefixEnd_4236016 := by exact prefixLift 4236016
  have htrace : WordTrace (prefixWord ++ tailWord_4236016) baseStart_4236016 baseEnd_4236016 := by
    simpa [prefixWord, tailWord_4236016, baseEnd_4236016] using wordTrace_append hprefix tailTrace_4236016
  have hstable : (prefixWord ++ tailWord_4236016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236016).length < 2 ^ (prefixWord ++ tailWord_4236016).sum := by decide
  have hdescent : baseEnd_4236016 < baseStart_4236016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236036 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 6]
def baseStart_4236036 : Nat := 118140960795 + 4236036 * 2 ^ 59
def prefixEnd_4236036 : Nat := 4983230072969 + 3 ^ 40 * 4236036 * 2
def baseEnd_4236036 : Nat := 241680281972121524818759

theorem tailTrace_4236036 : CollatzResearch.WordTrace tailWord_4236036 prefixEnd_4236036 241680281972121524818759 := by
  unfold tailWord_4236036
  simp only [CollatzResearch.WordTrace]
  refine ⟨77250462840786252098263981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103000617121048336131018641 77250462840786252098263981)
  ·
    refine ⟨28968923565294844536848993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77250462840786252098263981 28968923565294844536848993)
    ·
      refine ⟨21726692673971133402636745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28968923565294844536848993 21726692673971133402636745)
      ·
        refine ⟨16295019505478350051977559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21726692673971133402636745 16295019505478350051977559)
        ·
          refine ⟨24442529258217525077966339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16295019505478350051977559 24442529258217525077966339)
          ·
            refine ⟨36663793887326287616949509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24442529258217525077966339 36663793887326287616949509)
            ·
              refine ⟨6874461353873678928178033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36663793887326287616949509 6874461353873678928178033)
              ·
                refine ⟨5155846015405259196133525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6874461353873678928178033 5155846015405259196133525)
                ·
                  refine ⟨241680281972121524818759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5155846015405259196133525 241680281972121524818759)
                  ·
                    rfl

theorem cell23_4236036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_4236036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236036 prefixEnd_4236036 := by exact prefixLift 4236036
  have htrace : WordTrace (prefixWord ++ tailWord_4236036) baseStart_4236036 baseEnd_4236036 := by
    simpa [prefixWord, tailWord_4236036, baseEnd_4236036] using wordTrace_append hprefix tailTrace_4236036
  have hstable : (prefixWord ++ tailWord_4236036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236036).length < 2 ^ (prefixWord ++ tailWord_4236036).sum := by decide
  have hdescent : baseEnd_4236036 < baseStart_4236036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236040 : List Nat := [2, 1, 3, 2, 2, 2, 4, 2, 1, 4]
def baseStart_4236040 : Nat := 118140960795 + 4236040 * 2 ^ 59
def prefixEnd_4236040 : Nat := 4983230072969 + 3 ^ 40 * 4236040 * 2
def baseEnd_4236040 : Nat := 725041530557237235906271

theorem tailTrace_4236040 : CollatzResearch.WordTrace tailWord_4236040 prefixEnd_4236040 725041530557237235906271 := by
  unfold tailWord_4236040
  simp only [CollatzResearch.WordTrace]
  refine ⟨77250535786779006439836787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103000714382372008586449049 77250535786779006439836787)
  ·
    refine ⟨115875803680168509659755181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77250535786779006439836787 115875803680168509659755181)
    ·
      refine ⟨43453426380063191122408193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115875803680168509659755181 43453426380063191122408193)
      ·
        refine ⟨32590069785047393341806145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43453426380063191122408193 32590069785047393341806145)
        ·
          refine ⟨24442552338785545006354609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32590069785047393341806145 24442552338785545006354609)
          ·
            refine ⟨18331914254089158754765957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24442552338785545006354609 18331914254089158754765957)
            ·
              refine ⟨3437233922641717266518617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18331914254089158754765957 3437233922641717266518617)
              ·
                refine ⟨2577925441981287949888963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3437233922641717266518617 2577925441981287949888963)
                ·
                  refine ⟨3866888162971931924833445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2577925441981287949888963 3866888162971931924833445)
                  ·
                    refine ⟨725041530557237235906271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3866888162971931924833445 725041530557237235906271)
                    ·
                      rfl

theorem cell23_4236040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_4236040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236040 prefixEnd_4236040 := by exact prefixLift 4236040
  have htrace : WordTrace (prefixWord ++ tailWord_4236040) baseStart_4236040 baseEnd_4236040 := by
    simpa [prefixWord, tailWord_4236040, baseEnd_4236040] using wordTrace_append hprefix tailTrace_4236040
  have hstable : (prefixWord ++ tailWord_4236040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236040).length < 2 ^ (prefixWord ++ tailWord_4236040).sum := by decide
  have hdescent : baseEnd_4236040 < baseStart_4236040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236049 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 3, 5]
def baseStart_4236049 : Nat := 118140960795 + 4236049 * 2 ^ 59
def prefixEnd_4236049 : Nat := 4983230072969 + 3 ^ 40 * 4236049 * 2
def baseEnd_4236049 : Nat := 725043070999200724168757

theorem tailTrace_4236049 : CollatzResearch.WordTrace tailWord_4236049 prefixEnd_4236049 725043070999200724168757 := by
  unfold tailWord_4236049
  simp only [CollatzResearch.WordTrace]
  refine ⟨154501399830525407416751201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103000933220350271611167467 154501399830525407416751201)
  ·
    refine ⟨115876049872894055562563401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154501399830525407416751201 115876049872894055562563401)
    ·
      refine ⟨86907037404670541671922551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115876049872894055562563401 86907037404670541671922551)
      ·
        refine ⟨130360556107005812507883827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86907037404670541671922551 130360556107005812507883827)
        ·
          refine ⟨195540834160508718761825741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130360556107005812507883827 195540834160508718761825741)
          ·
            refine ⟨73327812810190769535684653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195540834160508718761825741 73327812810190769535684653)
            ·
              refine ⟨27497929803821538575881745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73327812810190769535684653 27497929803821538575881745)
              ·
                refine ⟨20623447352866153931911309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27497929803821538575881745 20623447352866153931911309)
                ·
                  refine ⟨7733792757324807724466741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20623447352866153931911309 7733792757324807724466741)
                  ·
                    refine ⟨725043070999200724168757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7733792757324807724466741 725043070999200724168757)
                    ·
                      rfl

theorem cell23_4236049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_4236049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236049 prefixEnd_4236049 := by exact prefixLift 4236049
  have htrace : WordTrace (prefixWord ++ tailWord_4236049) baseStart_4236049 baseEnd_4236049 := by
    simpa [prefixWord, tailWord_4236049, baseEnd_4236049] using wordTrace_append hprefix tailTrace_4236049
  have hstable : (prefixWord ++ tailWord_4236049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236049).length < 2 ^ (prefixWord ++ tailWord_4236049).sum := by decide
  have hdescent : baseEnd_4236049 < baseStart_4236049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236056 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 1, 5, 2]
def baseStart_4236056 : Nat := 118140960795 + 4236056 * 2 ^ 59
def prefixEnd_4236056 : Nat := 4983230072969 + 3 ^ 40 * 4236056 * 2
def baseEnd_4236056 : Nat := 2175132807362183645118739

theorem tailTrace_4236056 : CollatzResearch.WordTrace tailWord_4236056 prefixEnd_4236056 2175132807362183645118739 := by
  unfold tailWord_4236056
  simp only [CollatzResearch.WordTrace]
  refine ⟨77250827570750023806128011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103001103427666698408170681 77250827570750023806128011)
  ·
    refine ⟨115876241356125035709192017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77250827570750023806128011 115876241356125035709192017)
    ·
      refine ⟨86907181017093776781894013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115876241356125035709192017 86907181017093776781894013)
      ·
        refine ⟨32590192881410166293210255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86907181017093776781894013 32590192881410166293210255)
        ·
          refine ⟨48885289322115249439815383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32590192881410166293210255 48885289322115249439815383)
          ·
            refine ⟨73327933983172874159723075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48885289322115249439815383 73327933983172874159723075)
            ·
              refine ⟨109991900974759311239584613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73327933983172874159723075 109991900974759311239584613)
              ·
                refine ⟨20623481432767370857422115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109991900974759311239584613 20623481432767370857422115)
                ·
                  refine ⟨30935222149151056286133173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20623481432767370857422115 30935222149151056286133173)
                  ·
                    refine ⟨2900177076482911526824985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30935222149151056286133173 2900177076482911526824985)
                    ·
                      refine ⟨2175132807362183645118739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2900177076482911526824985 2175132807362183645118739)
                      ·
                        rfl

theorem cell23_4236056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_4236056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236056 prefixEnd_4236056 := by exact prefixLift 4236056
  have htrace : WordTrace (prefixWord ++ tailWord_4236056) baseStart_4236056 baseEnd_4236056 := by
    simpa [prefixWord, tailWord_4236056, baseEnd_4236056] using wordTrace_append hprefix tailTrace_4236056
  have hstable : (prefixWord ++ tailWord_4236056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236056).length < 2 ^ (prefixWord ++ tailWord_4236056).sum := by decide
  have hdescent : baseEnd_4236056 < baseStart_4236056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236063 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 3, 1, 3]
def baseStart_4236063 : Nat := 118140960795 + 4236063 * 2 ^ 59
def prefixEnd_4236063 : Nat := 4983230072969 + 3 ^ 40 * 4236063 * 2
def baseEnd_4236063 : Nat := 2175136401726765117731207

theorem tailTrace_4236063 : CollatzResearch.WordTrace tailWord_4236063 prefixEnd_4236063 2175136401726765117731207 := by
  unfold tailWord_4236063
  simp only [CollatzResearch.WordTrace]
  refine ⟨154501910452474687807760843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103001273634983125205173895 154501910452474687807760843)
  ·
    refine ⟨231752865678712031711641265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154501910452474687807760843 231752865678712031711641265)
    ·
      refine ⟨173814649259034023783730949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231752865678712031711641265 173814649259034023783730949)
      ·
        refine ⟨32590246736068879459449553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173814649259034023783730949 32590246736068879459449553)
        ·
          refine ⟨24442685052051659594587165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32590246736068879459449553 24442685052051659594587165)
          ·
            refine ⟨9166006894519372347970187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24442685052051659594587165 9166006894519372347970187)
            ·
              refine ⟨13749010341779058521955281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9166006894519372347970187 13749010341779058521955281)
              ·
                refine ⟨10311757756334293891466461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13749010341779058521955281 10311757756334293891466461)
                ·
                  refine ⟨3866909158625360209299923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10311757756334293891466461 3866909158625360209299923)
                  ·
                    refine ⟨5800363737938040313949885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3866909158625360209299923 5800363737938040313949885)
                    ·
                      refine ⟨2175136401726765117731207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5800363737938040313949885 2175136401726765117731207)
                      ·
                        rfl

theorem cell23_4236063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_4236063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236063 prefixEnd_4236063 := by exact prefixLift 4236063
  have htrace : WordTrace (prefixWord ++ tailWord_4236063) baseStart_4236063 baseEnd_4236063 := by
    simpa [prefixWord, tailWord_4236063, baseEnd_4236063] using wordTrace_append hprefix tailTrace_4236063
  have hstable : (prefixWord ++ tailWord_4236063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236063).length < 2 ^ (prefixWord ++ tailWord_4236063).sum := by decide
  have hdescent : baseEnd_4236063 < baseStart_4236063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236066 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_4236066 : Nat := 118140960795 + 4236066 * 2 ^ 59
def prefixEnd_4236066 : Nat := 4983230072969 + 3 ^ 40 * 4236066 * 2
def baseEnd_4236066 : Nat := 725045980722909535331231

theorem tailTrace_4236066 : CollatzResearch.WordTrace tailWord_4236066 prefixEnd_4236066 725045980722909535331231 := by
  unfold tailWord_4236066
  simp only [CollatzResearch.WordTrace]
  refine ⟨38625504967865954830030013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103001346580975879546746701 38625504967865954830030013)
  ·
    refine ⟨14484564362949733061261255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38625504967865954830030013 14484564362949733061261255)
    ·
      refine ⟨21726846544424599591891883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14484564362949733061261255 21726846544424599591891883)
      ·
        refine ⟨32590269816636899387837825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21726846544424599591891883 32590269816636899387837825)
        ·
          refine ⟨24442702362477674540878369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32590269816636899387837825 24442702362477674540878369)
          ·
            refine ⟨18332026771858255905658777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24442702362477674540878369 18332026771858255905658777)
            ·
              refine ⟨13749020078893691929244083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18332026771858255905658777 13749020078893691929244083)
              ·
                refine ⟨20623530118340537893866125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13749020078893691929244083 20623530118340537893866125)
                ·
                  refine ⟨7733823794377701710199797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20623530118340537893866125 7733823794377701710199797)
                  ·
                    refine ⟨725045980722909535331231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7733823794377701710199797 725045980722909535331231)
                    ·
                      rfl

theorem cell23_4236066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_4236066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236066 prefixEnd_4236066 := by exact prefixLift 4236066
  have htrace : WordTrace (prefixWord ++ tailWord_4236066) baseStart_4236066 baseEnd_4236066 := by
    simpa [prefixWord, tailWord_4236066, baseEnd_4236066] using wordTrace_append hprefix tailTrace_4236066
  have hstable : (prefixWord ++ tailWord_4236066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236066).length < 2 ^ (prefixWord ++ tailWord_4236066).sum := by decide
  have hdescent : baseEnd_4236066 < baseStart_4236066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236083 : List Nat := [1, 1, 1, 2, 6, 1, 4, 1, 1, 5]
def baseStart_4236083 : Nat := 118140960795 + 4236083 * 2 ^ 59
def prefixEnd_4236083 : Nat := 4983230072969 + 3 ^ 40 * 4236083 * 2
def baseEnd_4236083 : Nat := 725048890446618346493705

theorem tailTrace_4236083 : CollatzResearch.WordTrace tailWord_4236083 prefixEnd_4236083 725048890446618346493705 := by
  unfold tailWord_4236083
  simp only [CollatzResearch.WordTrace]
  refine ⟨154502639912402231223488903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103001759941601487482325935 154502639912402231223488903)
  ·
    refine ⟨231753959868603346835233355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154502639912402231223488903 231753959868603346835233355)
    ·
      refine ⟨347630939802905020252850033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231753959868603346835233355 347630939802905020252850033)
      ·
        refine ⟨260723204852178765189637525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347630939802905020252850033 260723204852178765189637525)
        ·
          refine ⟨12221400227445879618264259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 260723204852178765189637525 12221400227445879618264259)
          ·
            refine ⟨18332100341168819427396389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12221400227445879618264259 18332100341168819427396389)
            ·
              refine ⟨3437268813969153642636823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18332100341168819427396389 3437268813969153642636823)
              ·
                refine ⟨5155903220953730463955235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3437268813969153642636823 5155903220953730463955235)
                ·
                  refine ⟨7733854831430595695932853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5155903220953730463955235 7733854831430595695932853)
                  ·
                    refine ⟨725048890446618346493705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7733854831430595695932853 725048890446618346493705)
                    ·
                      rfl

theorem cell23_4236083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 5].length) (baseStart_4236083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236083 prefixEnd_4236083 := by exact prefixLift 4236083
  have htrace : WordTrace (prefixWord ++ tailWord_4236083) baseStart_4236083 baseEnd_4236083 := by
    simpa [prefixWord, tailWord_4236083, baseEnd_4236083] using wordTrace_append hprefix tailTrace_4236083
  have hstable : (prefixWord ++ tailWord_4236083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236083).length < 2 ^ (prefixWord ++ tailWord_4236083).sum := by decide
  have hdescent : baseEnd_4236083 < baseStart_4236083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236097 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_4236097 : Nat := 118140960795 + 4236097 * 2 ^ 59
def prefixEnd_4236097 : Nat := 4983230072969 + 3 ^ 40 * 4236097 * 2
def baseEnd_4236097 : Nat := 2175153860069017984706051

theorem tailTrace_4236097 : CollatzResearch.WordTrace tailWord_4236097 prefixEnd_4236097 2175153860069017984706051 := by
  unfold tailWord_4236097
  simp only [CollatzResearch.WordTrace]
  refine ⟨154503150534351511614498545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103002100356234341076332363 154503150534351511614498545)
  ·
    refine ⟨115877362900763633710873909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154503150534351511614498545 115877362900763633710873909)
    ·
      refine ⟨10863502771946590660394429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115877362900763633710873909 10863502771946590660394429)
      ·
        refine ⟨4073813539479971497647911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10863502771946590660394429 4073813539479971497647911)
        ·
          refine ⟨6110720309219957246471867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4073813539479971497647911 6110720309219957246471867)
          ·
            refine ⟨9166080463829935869707801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6110720309219957246471867 9166080463829935869707801)
            ·
              refine ⟨6874560347872451902280851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9166080463829935869707801 6874560347872451902280851)
              ·
                refine ⟨10311840521808677853421277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6874560347872451902280851 10311840521808677853421277)
                ·
                  refine ⟨3866940195678254195032979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10311840521808677853421277 3866940195678254195032979)
                  ·
                    refine ⟨5800410293517381292549469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3866940195678254195032979 5800410293517381292549469)
                    ·
                      refine ⟨2175153860069017984706051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5800410293517381292549469 2175153860069017984706051)
                      ·
                        rfl

theorem cell23_4236097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_4236097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236097 prefixEnd_4236097 := by exact prefixLift 4236097
  have htrace : WordTrace (prefixWord ++ tailWord_4236097) baseStart_4236097 baseEnd_4236097 := by
    simpa [prefixWord, tailWord_4236097, baseEnd_4236097] using wordTrace_append hprefix tailTrace_4236097
  have hstable : (prefixWord ++ tailWord_4236097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236097).length < 2 ^ (prefixWord ++ tailWord_4236097).sum := by decide
  have hdescent : baseEnd_4236097 < baseStart_4236097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236099 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 6]
def baseStart_4236099 : Nat := 118140960795 + 4236099 * 2 ^ 59
def prefixEnd_4236099 : Nat := 4983230072969 + 3 ^ 40 * 4236099 * 2
def baseEnd_4236099 : Nat := 2175154887030326976881041

theorem tailTrace_4236099 : CollatzResearch.WordTrace tailWord_4236099 prefixEnd_4236099 2175154887030326976881041 := by
  unfold tailWord_4236099
  simp only [CollatzResearch.WordTrace]
  refine ⟨154503223480344265956071351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103002148986896177304047567 154503223480344265956071351)
  ·
    refine ⟨231754835220516398934107027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154503223480344265956071351 231754835220516398934107027)
    ·
      refine ⟨347632252830774598401160541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231754835220516398934107027 347632252830774598401160541)
      ·
        refine ⟨130362094811540474400435203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347632252830774598401160541 130362094811540474400435203)
        ·
          refine ⟨195543142217310711600652805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130362094811540474400435203 195543142217310711600652805)
          ·
            refine ⟨36664339165745758425122401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195543142217310711600652805 36664339165745758425122401)
            ·
              refine ⟨27498254374309318818841801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36664339165745758425122401 27498254374309318818841801)
              ·
                refine ⟨20623690780731989114131351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27498254374309318818841801 20623690780731989114131351)
                ·
                  refine ⟨30935536171097983671197027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20623690780731989114131351 30935536171097983671197027)
                  ·
                    refine ⟨46403304256646975506795541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30935536171097983671197027 46403304256646975506795541)
                    ·
                      refine ⟨2175154887030326976881041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46403304256646975506795541 2175154887030326976881041)
                      ·
                        rfl

theorem cell23_4236099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_4236099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236099 prefixEnd_4236099 := by exact prefixLift 4236099
  have htrace : WordTrace (prefixWord ++ tailWord_4236099) baseStart_4236099 baseEnd_4236099 := by
    simpa [prefixWord, tailWord_4236099, baseEnd_4236099] using wordTrace_append hprefix tailTrace_4236099
  have hstable : (prefixWord ++ tailWord_4236099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236099).length < 2 ^ (prefixWord ++ tailWord_4236099).sum := by decide
  have hdescent : baseEnd_4236099 < baseStart_4236099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236106 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_4236106 : Nat := 118140960795 + 4236106 * 2 ^ 59
def prefixEnd_4236106 : Nat := 4983230072969 + 3 ^ 40 * 4236106 * 2
def baseEnd_4236106 : Nat := 2175158481394908449493509

theorem tailTrace_4236106 : CollatzResearch.WordTrace tailWord_4236106 prefixEnd_4236106 2175158481394908449493509 := by
  unfold tailWord_4236106
  simp only [CollatzResearch.WordTrace]
  refine ⟨38625869697829726537894043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103002319194212604101050781 38625869697829726537894043)
  ·
    refine ⟨57938804546744589806841065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38625869697829726537894043 57938804546744589806841065)
    ·
      refine ⟨43454103410058442355130799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57938804546744589806841065 43454103410058442355130799)
      ·
        refine ⟨65181155115087663532696199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43454103410058442355130799 65181155115087663532696199)
        ·
          refine ⟨97771732672631495299044299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65181155115087663532696199 97771732672631495299044299)
          ·
            refine ⟨146657599008947242948566449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97771732672631495299044299 146657599008947242948566449)
            ·
              refine ⟨109993199256710432211424837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146657599008947242948566449 109993199256710432211424837)
              ·
                refine ⟨20623724860633206039642157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109993199256710432211424837 20623724860633206039642157)
                ·
                  refine ⟨7733896822737452264865809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20623724860633206039642157 7733896822737452264865809)
                  ·
                    refine ⟨5800422617053089198649357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7733896822737452264865809 5800422617053089198649357)
                    ·
                      refine ⟨2175158481394908449493509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5800422617053089198649357 2175158481394908449493509)
                      ·
                        rfl

theorem cell23_4236106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_4236106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236106 prefixEnd_4236106 := by exact prefixLift 4236106
  have htrace : WordTrace (prefixWord ++ tailWord_4236106) baseStart_4236106 baseEnd_4236106 := by
    simpa [prefixWord, tailWord_4236106, baseEnd_4236106] using wordTrace_append hprefix tailTrace_4236106
  have hstable : (prefixWord ++ tailWord_4236106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236106).length < 2 ^ (prefixWord ++ tailWord_4236106).sum := by decide
  have hdescent : baseEnd_4236106 < baseStart_4236106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236113 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 1, 6]
def baseStart_4236113 : Nat := 118140960795 + 4236113 * 2 ^ 59
def prefixEnd_4236113 : Nat := 4983230072969 + 3 ^ 40 * 4236113 * 2
def baseEnd_4236113 : Nat := 725054025253163307368659

theorem tailTrace_4236113 : CollatzResearch.WordTrace tailWord_4236113 prefixEnd_4236113 725054025253163307368659 := by
  unfold tailWord_4236113
  simp only [CollatzResearch.WordTrace]
  refine ⟨154503734102293546347080993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103002489401529030898053995 154503734102293546347080993)
  ·
    refine ⟨115877800576720159760310745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154503734102293546347080993 115877800576720159760310745)
    ·
      refine ⟨86908350432540119820233059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115877800576720159760310745 86908350432540119820233059)
      ·
        refine ⟨130362525648810179730349589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86908350432540119820233059 130362525648810179730349589)
        ·
          refine ⟨6110743389787977174860137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 130362525648810179730349589 6110743389787977174860137)
          ·
            refine ⟨4583057542340982881145103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6110743389787977174860137 4583057542340982881145103)
            ·
              refine ⟨6874586313511474321717655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4583057542340982881145103 6874586313511474321717655)
              ·
                refine ⟨10311879470267211482576483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6874586313511474321717655 10311879470267211482576483)
                ·
                  refine ⟨15467819205400817223864725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10311879470267211482576483 15467819205400817223864725)
                  ·
                    refine ⟨725054025253163307368659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15467819205400817223864725 725054025253163307368659)
                    ·
                      rfl

theorem cell23_4236113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_4236113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236113 prefixEnd_4236113 := by exact prefixLift 4236113
  have htrace : WordTrace (prefixWord ++ tailWord_4236113) baseStart_4236113 baseEnd_4236113 := by
    simpa [prefixWord, tailWord_4236113, baseEnd_4236113] using wordTrace_append hprefix tailTrace_4236113
  have hstable : (prefixWord ++ tailWord_4236113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236113).length < 2 ^ (prefixWord ++ tailWord_4236113).sum := by decide
  have hdescent : baseEnd_4236113 < baseStart_4236113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236153 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 4, 1, 3]
def baseStart_4236153 : Nat := 118140960795 + 4236153 * 2 ^ 59
def prefixEnd_4236153 : Nat := 4983230072969 + 3 ^ 40 * 4236153 * 2
def baseEnd_4236153 : Nat := 2175182614985669765605793

theorem tailTrace_4236153 : CollatzResearch.WordTrace tailWord_4236153 prefixEnd_4236153 2175182614985669765605793 := by
  unfold tailWord_4236153
  simp only [CollatzResearch.WordTrace]
  refine ⟨154505193022148633178537113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103003462014765755452358075 154505193022148633178537113)
  ·
    refine ⟨115878894766611474883902835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154505193022148633178537113 115878894766611474883902835)
    ·
      refine ⟨173818342149917212325854253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115878894766611474883902835 173818342149917212325854253)
      ·
        refine ⟨65181878306218954622195345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173818342149917212325854253 65181878306218954622195345)
        ·
          refine ⟨48886408729664215966646509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65181878306218954622195345 48886408729664215966646509)
          ·
            refine ⟨18332403273624080987492441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48886408729664215966646509 18332403273624080987492441)
            ·
              refine ⟨13749302455218060740619331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18332403273624080987492441 13749302455218060740619331)
              ·
                refine ⟨20623953682827091110928997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13749302455218060740619331 20623953682827091110928997)
                ·
                  refine ⟨3866991315530079583299187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20623953682827091110928997 3866991315530079583299187)
                  ·
                    refine ⟨5800486973295119374948781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3866991315530079583299187 5800486973295119374948781)
                    ·
                      refine ⟨2175182614985669765605793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5800486973295119374948781 2175182614985669765605793)
                      ·
                        rfl

theorem cell23_4236153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_4236153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236153 prefixEnd_4236153 := by exact prefixLift 4236153
  have htrace : WordTrace (prefixWord ++ tailWord_4236153) baseStart_4236153 baseEnd_4236153 := by
    simpa [prefixWord, tailWord_4236153, baseEnd_4236153] using wordTrace_append hprefix tailTrace_4236153
  have hstable : (prefixWord ++ tailWord_4236153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236153).length < 2 ^ (prefixWord ++ tailWord_4236153).sum := by decide
  have hdescent : baseEnd_4236153 < baseStart_4236153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236163 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 3, 3, 2]
def baseStart_4236163 : Nat := 118140960795 + 4236163 * 2 ^ 59
def prefixEnd_4236163 : Nat := 4983230072969 + 3 ^ 40 * 4236163 * 2
def baseEnd_4236163 : Nat := 2175187749792214726480747

theorem tailTrace_4236163 : CollatzResearch.WordTrace tailWord_4236163 prefixEnd_4236163 2175187749792214726480747 := by
  unfold tailWord_4236163
  simp only [CollatzResearch.WordTrace]
  refine ⟨154505557752112404886401143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103003705168074936590934095 154505557752112404886401143)
  ·
    refine ⟨231758336628168607329601715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154505557752112404886401143 231758336628168607329601715)
    ·
      refine ⟨347637504942252910994402573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231758336628168607329601715 347637504942252910994402573)
      ·
        refine ⟨130364064353344841622900965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347637504942252910994402573 130364064353344841622900965)
        ·
          refine ⟨24443262066252157804293931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130364064353344841622900965 24443262066252157804293931)
          ·
            refine ⟨36664893099378236706440897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24443262066252157804293931 36664893099378236706440897)
            ·
              refine ⟨27498669824533677529830673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36664893099378236706440897 27498669824533677529830673)
              ·
                refine ⟨20624002368400258147373005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27498669824533677529830673 20624002368400258147373005)
                ·
                  refine ⟨7734000888150096805264877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20624002368400258147373005 7734000888150096805264877)
                  ·
                    refine ⟨2900250333056286301974329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7734000888150096805264877 2900250333056286301974329)
                    ·
                      refine ⟨2175187749792214726480747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2900250333056286301974329 2175187749792214726480747)
                      ·
                        rfl

theorem cell23_4236163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 3, 2].length) (baseStart_4236163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236163 prefixEnd_4236163 := by exact prefixLift 4236163
  have htrace : WordTrace (prefixWord ++ tailWord_4236163) baseStart_4236163 baseEnd_4236163 := by
    simpa [prefixWord, tailWord_4236163, baseEnd_4236163] using wordTrace_append hprefix tailTrace_4236163
  have hstable : (prefixWord ++ tailWord_4236163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236163).length < 2 ^ (prefixWord ++ tailWord_4236163).sum := by decide
  have hdescent : baseEnd_4236163 < baseStart_4236163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236180 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_4236180 : Nat := 118140960795 + 4236180 * 2 ^ 59
def prefixEnd_4236180 : Nat := 4983230072969 + 3 ^ 40 * 4236180 * 2
def baseEnd_4236180 : Nat := 2175196478963341159968169

theorem tailTrace_4236180 : CollatzResearch.WordTrace tailWord_4236180 prefixEnd_4236180 2175196478963341159968169 := by
  unfold tailWord_4236180
  simp only [CollatzResearch.WordTrace]
  refine ⟨77253088896525408394884997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103004118528700544526513329 77253088896525408394884997)
  ·
    refine ⟨14484954168098514074040937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77253088896525408394884997 14484954168098514074040937)
    ·
      refine ⟨10863715626073885555530703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14484954168098514074040937 10863715626073885555530703)
      ·
        refine ⟨16295573439110828333296055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10863715626073885555530703 16295573439110828333296055)
        ·
          refine ⟨24443360158666242499944083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16295573439110828333296055 24443360158666242499944083)
          ·
            refine ⟨36665040237999363749916125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24443360158666242499944083 36665040237999363749916125)
            ·
              refine ⟨13749390089249761406218547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36665040237999363749916125 13749390089249761406218547)
              ·
                refine ⟨20624085133874642109327821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13749390089249761406218547 20624085133874642109327821)
                ·
                  refine ⟨7734031925202990790997933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20624085133874642109327821 7734031925202990790997933)
                  ·
                    refine ⟨2900261971951121546624225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7734031925202990790997933 2900261971951121546624225)
                    ·
                      refine ⟨2175196478963341159968169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2900261971951121546624225 2175196478963341159968169)
                      ·
                        rfl

theorem cell23_4236180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_4236180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236180 prefixEnd_4236180 := by exact prefixLift 4236180
  have htrace : WordTrace (prefixWord ++ tailWord_4236180) baseStart_4236180 baseEnd_4236180 := by
    simpa [prefixWord, tailWord_4236180, baseEnd_4236180] using wordTrace_append hprefix tailTrace_4236180
  have hstable : (prefixWord ++ tailWord_4236180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236180).length < 2 ^ (prefixWord ++ tailWord_4236180).sum := by decide
  have hdescent : baseEnd_4236180 < baseStart_4236180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236196 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_4236196 : Nat := 118140960795 + 4236196 * 2 ^ 59
def prefixEnd_4236196 : Nat := 4983230072969 + 3 ^ 40 * 4236196 * 2
def baseEnd_4236196 : Nat := 2175204694653813097368095

theorem tailTrace_4236196 : CollatzResearch.WordTrace tailWord_4236196 prefixEnd_4236196 2175204694653813097368095 := by
  unfold tailWord_4236196
  simp only [CollatzResearch.WordTrace]
  refine ⟨77253380680496425761176221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103004507573995234348234961 77253380680496425761176221)
  ·
    refine ⟨28970017755186159660441083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77253380680496425761176221 28970017755186159660441083)
    ·
      refine ⟨43455026632779239490661625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28970017755186159660441083 43455026632779239490661625)
      ·
        refine ⟨32591269974584429617996219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43455026632779239490661625 32591269974584429617996219)
        ·
          refine ⟨48886904961876644426994329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32591269974584429617996219 48886904961876644426994329)
          ·
            refine ⟨36665178721407483320245747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48886904961876644426994329 36665178721407483320245747)
            ·
              refine ⟨54997768082111224980368621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36665178721407483320245747 54997768082111224980368621)
              ·
                refine ⟨20624163030791709367638233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54997768082111224980368621 20624163030791709367638233)
                ·
                  refine ⟨15468122273093782025728675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20624163030791709367638233 15468122273093782025728675)
                  ·
                    refine ⟨23202183409640673038593013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15468122273093782025728675 23202183409640673038593013)
                    ·
                      refine ⟨2175204694653813097368095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23202183409640673038593013 2175204694653813097368095)
                      ·
                        rfl

theorem cell23_4236196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_4236196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236196 prefixEnd_4236196 := by exact prefixLift 4236196
  have htrace : WordTrace (prefixWord ++ tailWord_4236196) baseStart_4236196 baseEnd_4236196 := by
    simpa [prefixWord, tailWord_4236196, baseEnd_4236196] using wordTrace_append hprefix tailTrace_4236196
  have hstable : (prefixWord ++ tailWord_4236196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236196).length < 2 ^ (prefixWord ++ tailWord_4236196).sum := by decide
  have hdescent : baseEnd_4236196 < baseStart_4236196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236205 : List Nat := [1, 5, 2, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4236205 : Nat := 118140960795 + 4236205 * 2 ^ 59
def prefixEnd_4236205 : Nat := 4983230072969 + 3 ^ 40 * 4236205 * 2
def baseEnd_4236205 : Nat := 2175209315979703562155555

theorem tailTrace_4236205 : CollatzResearch.WordTrace tailWord_4236205 prefixEnd_4236205 2175209315979703562155555 := by
  unfold tailWord_4236205
  simp only [CollatzResearch.WordTrace]
  refine ⟨154507089617960246059430069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103004726411973497372953379 154507089617960246059430069)
  ·
    refine ⟨14485039651683773068071569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154507089617960246059430069 14485039651683773068071569)
    ·
      refine ⟨10863779738762829801053677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14485039651683773068071569 10863779738762829801053677)
      ·
        refine ⟨4073917402036061175395129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10863779738762829801053677 4073917402036061175395129)
        ·
          refine ⟨3055438051527045881546347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4073917402036061175395129 3055438051527045881546347)
          ·
            refine ⟨4583157077290568822319521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3055438051527045881546347 4583157077290568822319521)
            ·
              refine ⟨3437367807967926616739641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4583157077290568822319521 3437367807967926616739641)
              ·
                refine ⟨2578025855975944962554731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3437367807967926616739641 2578025855975944962554731)
                ·
                  refine ⟨3867038783963917443832097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2578025855975944962554731 3867038783963917443832097)
                  ·
                    refine ⟨2900279087972938082874073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3867038783963917443832097 2900279087972938082874073)
                    ·
                      refine ⟨2175209315979703562155555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2900279087972938082874073 2175209315979703562155555)
                      ·
                        rfl

theorem cell23_4236205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4236205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236205 prefixEnd_4236205 := by exact prefixLift 4236205
  have htrace : WordTrace (prefixWord ++ tailWord_4236205) baseStart_4236205 baseEnd_4236205 := by
    simpa [prefixWord, tailWord_4236205, baseEnd_4236205] using wordTrace_append hprefix tailTrace_4236205
  have hstable : (prefixWord ++ tailWord_4236205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236205).length < 2 ^ (prefixWord ++ tailWord_4236205).sum := by decide
  have hdescent : baseEnd_4236205 < baseStart_4236205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236250 : List Nat := [3, 1, 1, 2, 4, 2, 2, 3, 5]
def baseStart_4236250 : Nat := 118140960795 + 4236250 * 2 ^ 59
def prefixEnd_4236250 : Nat := 4983230072969 + 3 ^ 40 * 4236250 * 2
def baseEnd_4236250 : Nat := 241692491401017320676983

theorem tailTrace_4236250 : CollatzResearch.WordTrace tailWord_4236250 prefixEnd_4236250 241692491401017320676983 := by
  unfold tailWord_4236250
  simp only [CollatzResearch.WordTrace]
  refine ⟨38627182725699304686204551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103005820601864812496545469 38627182725699304686204551)
  ·
    refine ⟨57940774088548957029306827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38627182725699304686204551 57940774088548957029306827)
    ·
      refine ⟨86911161132823435543960241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57940774088548957029306827 86911161132823435543960241)
      ·
        refine ⟨65183370849617576657970181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86911161132823435543960241 65183370849617576657970181)
        ·
          refine ⟨12221882034303295623369409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65183370849617576657970181 12221882034303295623369409)
          ·
            refine ⟨9166411525727471717527057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12221882034303295623369409 9166411525727471717527057)
            ·
              refine ⟨6874808644295603788145293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9166411525727471717527057 6874808644295603788145293)
              ·
                refine ⟨2578053241610851420554485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6874808644295603788145293 2578053241610851420554485)
                ·
                  refine ⟨241692491401017320676983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2578053241610851420554485 241692491401017320676983)
                  ·
                    rfl

theorem cell23_4236250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 3, 5].length) (baseStart_4236250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236250 prefixEnd_4236250 := by exact prefixLift 4236250
  have htrace : WordTrace (prefixWord ++ tailWord_4236250) baseStart_4236250 baseEnd_4236250 := by
    simpa [prefixWord, tailWord_4236250, baseEnd_4236250] using wordTrace_append hprefix tailTrace_4236250
  have hstable : (prefixWord ++ tailWord_4236250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236250).length < 2 ^ (prefixWord ++ tailWord_4236250).sum := by decide
  have hdescent : baseEnd_4236250 < baseStart_4236250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236261 : List Nat := [1, 3, 1, 6, 1, 2, 1, 2, 2, 2, 2]
def baseStart_4236261 : Nat := 118140960795 + 4236261 * 2 ^ 59
def prefixEnd_4236261 : Nat := 4983230072969 + 3 ^ 40 * 4236261 * 2
def baseEnd_4236261 : Nat := 2175238070896355343055297

theorem tailTrace_4236261 : CollatzResearch.WordTrace tailWord_4236261 prefixEnd_4236261 2175238070896355343055297 := by
  unfold tailWord_4236261
  simp only [CollatzResearch.WordTrace]
  refine ⟨154509132105757367623468637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103006088070504911748979091 154509132105757367623468637)
  ·
    refine ⟨57940924539659012858800739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154509132105757367623468637 57940924539659012858800739)
    ·
      refine ⟨86911386809488519288201109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57940924539659012858800739 86911386809488519288201109)
      ·
        refine ⟨4073971256694774341634427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86911386809488519288201109 4073971256694774341634427)
        ·
          refine ⟨6110956885042161512451641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4073971256694774341634427 6110956885042161512451641)
          ·
            refine ⟨4583217663781621134338731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6110956885042161512451641 4583217663781621134338731)
            ·
              refine ⟨6874826495672431701508097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4583217663781621134338731 6874826495672431701508097)
              ·
                refine ⟨5156119871754323776131073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6874826495672431701508097 5156119871754323776131073)
                ·
                  refine ⟨3867089903815742832098305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5156119871754323776131073 3867089903815742832098305)
                  ·
                    refine ⟨2900317427861807124073729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3867089903815742832098305 2900317427861807124073729)
                    ·
                      refine ⟨2175238070896355343055297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2900317427861807124073729 2175238070896355343055297)
                      ·
                        rfl

theorem cell23_4236261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_4236261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236261 prefixEnd_4236261 := by exact prefixLift 4236261
  have htrace : WordTrace (prefixWord ++ tailWord_4236261) baseStart_4236261 baseEnd_4236261 := by
    simpa [prefixWord, tailWord_4236261, baseEnd_4236261] using wordTrace_append hprefix tailTrace_4236261
  have hstable : (prefixWord ++ tailWord_4236261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236261).length < 2 ^ (prefixWord ++ tailWord_4236261).sum := by decide
  have hdescent : baseEnd_4236261 < baseStart_4236261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236293 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 3, 4]
def baseStart_4236293 : Nat := 118140960795 + 4236293 * 2 ^ 59
def prefixEnd_4236293 : Nat := 4983230072969 + 3 ^ 40 * 4236293 * 2
def baseEnd_4236293 : Nat := 725084834092433072618383

theorem tailTrace_4236293 : CollatzResearch.WordTrace tailWord_4236293 prefixEnd_4236293 725084834092433072618383 := by
  unfold tailWord_4236293
  simp only [CollatzResearch.WordTrace]
  refine ⟨154510299241641437088633533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103006866161094291392422355 154510299241641437088633533)
  ·
    refine ⟨57941362215615538908237575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154510299241641437088633533 57941362215615538908237575)
    ·
      refine ⟨86912043323423308362356363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57941362215615538908237575 86912043323423308362356363)
      ·
        refine ⟨130368064985134962543534545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86912043323423308362356363 130368064985134962543534545)
        ·
          refine ⟨97776048738851221907650909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130368064985134962543534545 97776048738851221907650909)
          ·
            refine ⟨36666018277069208215369091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97776048738851221907650909 36666018277069208215369091)
            ·
              refine ⟨54999027415603812323053637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36666018277069208215369091 54999027415603812323053637)
              ·
                refine ⟨10312317640425714810572557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54999027415603812323053637 10312317640425714810572557)
                ·
                  refine ⟨3867119115159643053964709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10312317640425714810572557 3867119115159643053964709)
                  ·
                    refine ⟨725084834092433072618383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3867119115159643053964709 725084834092433072618383)
                    ·
                      rfl

theorem cell23_4236293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_4236293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236293 prefixEnd_4236293 := by exact prefixLift 4236293
  have htrace : WordTrace (prefixWord ++ tailWord_4236293) baseStart_4236293 baseEnd_4236293 := by
    simpa [prefixWord, tailWord_4236293, baseEnd_4236293] using wordTrace_append hprefix tailTrace_4236293
  have hstable : (prefixWord ++ tailWord_4236293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236293).length < 2 ^ (prefixWord ++ tailWord_4236293).sum := by decide
  have hdescent : baseEnd_4236293 < baseStart_4236293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236327 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 3, 4]
def baseStart_4236327 : Nat := 118140960795 + 4236327 * 2 ^ 59
def prefixEnd_4236327 : Nat := 4983230072969 + 3 ^ 40 * 4236327 * 2
def baseEnd_4236327 : Nat := 725090653539850694943331

theorem tailTrace_4236327 : CollatzResearch.WordTrace tailWord_4236327 prefixEnd_4236327 725090653539850694943331 := by
  unfold tailWord_4236327
  simp only [CollatzResearch.WordTrace]
  refine ⟨154511539323518260895371235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103007692882345507263580823 154511539323518260895371235)
  ·
    refine ⟨231767308985277391343056853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154511539323518260895371235 231767308985277391343056853)
    ·
      refine ⟨5432046304342438859602895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 231767308985277391343056853 5432046304342438859602895)
      ·
        refine ⟨8148069456513658289404343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5432046304342438859602895 8148069456513658289404343)
        ·
          refine ⟨12222104184770487434106515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8148069456513658289404343 12222104184770487434106515)
          ·
            refine ⟨18333156277155731151159773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12222104184770487434106515 18333156277155731151159773)
            ·
              refine ⟨6874933603933399181684915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18333156277155731151159773 6874933603933399181684915)
              ·
                refine ⟨10312400405900098772527373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6874933603933399181684915 10312400405900098772527373)
                ·
                  refine ⟨3867150152212537039697765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10312400405900098772527373 3867150152212537039697765)
                  ·
                    refine ⟨725090653539850694943331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3867150152212537039697765 725090653539850694943331)
                    ·
                      rfl

theorem cell23_4236327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_4236327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236327 prefixEnd_4236327 := by exact prefixLift 4236327
  have htrace : WordTrace (prefixWord ++ tailWord_4236327) baseStart_4236327 baseEnd_4236327 := by
    simpa [prefixWord, tailWord_4236327, baseEnd_4236327] using wordTrace_append hprefix tailTrace_4236327
  have hstable : (prefixWord ++ tailWord_4236327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236327).length < 2 ^ (prefixWord ++ tailWord_4236327).sum := by decide
  have hdescent : baseEnd_4236327 < baseStart_4236327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236374 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 6]
def baseStart_4236374 : Nat := 118140960795 + 4236374 * 2 ^ 59
def prefixEnd_4236374 : Nat := 4983230072969 + 3 ^ 40 * 4236374 * 2
def baseEnd_4236374 : Nat := 241699566023368155660253

theorem tailTrace_4236374 : CollatzResearch.WordTrace tailWord_4236374 prefixEnd_4236374 241699566023368155660253 := by
  unfold tailWord_4236374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9657078347146749245145761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103008835702898658614888117 9657078347146749245145761)
  ·
    refine ⟨7242808760360061933859321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9657078347146749245145761 7242808760360061933859321)
    ·
      refine ⟨5432106570270046450394491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7242808760360061933859321 5432106570270046450394491)
      ·
        refine ⟨8148159855405069675591737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5432106570270046450394491 8148159855405069675591737)
        ·
          refine ⟨6111119891553802256693803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8148159855405069675591737 6111119891553802256693803)
          ·
            refine ⟨9166679837330703385040705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6111119891553802256693803 9166679837330703385040705)
            ·
              refine ⟨6875009877998027538780529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9166679837330703385040705 6875009877998027538780529)
              ·
                refine ⟨5156257408498520654085397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6875009877998027538780529 5156257408498520654085397)
                ·
                  refine ⟨241699566023368155660253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5156257408498520654085397 241699566023368155660253)
                  ·
                    rfl

theorem cell23_4236374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_4236374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236374 prefixEnd_4236374 := by exact prefixLift 4236374
  have htrace : WordTrace (prefixWord ++ tailWord_4236374) baseStart_4236374 baseEnd_4236374 := by
    simpa [prefixWord, tailWord_4236374, baseEnd_4236374] using wordTrace_append hprefix tailTrace_4236374
  have hstable : (prefixWord ++ tailWord_4236374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236374).length < 2 ^ (prefixWord ++ tailWord_4236374).sum := by decide
  have hdescent : baseEnd_4236374 < baseStart_4236374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236400 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 2, 4]
def baseStart_4236400 : Nat := 118140960795 + 4236400 * 2 ^ 59
def prefixEnd_4236400 : Nat := 4983230072969 + 3 ^ 40 * 4236400 * 2
def baseEnd_4236400 : Nat := 725103148235776766405719

theorem tailTrace_4236400 : CollatzResearch.WordTrace tailWord_4236400 prefixEnd_4236400 725103148235776766405719 := by
  unfold tailWord_4236400
  simp only [CollatzResearch.WordTrace]
  refine ⟨77257100926126897181389327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103009467901502529575185769 77257100926126897181389327)
  ·
    refine ⟨115885651389190345772083991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77257100926126897181389327 115885651389190345772083991)
    ·
      refine ⟨173828477083785518658125987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115885651389190345772083991 173828477083785518658125987)
      ·
        refine ⟨260742715625678277987188981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173828477083785518658125987 260742715625678277987188981)
        ·
          refine ⟨24444629589907338561298967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 260742715625678277987188981 24444629589907338561298967)
          ·
            refine ⟨36666944384861007841948451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24444629589907338561298967 36666944384861007841948451)
            ·
              refine ⟨55000416577291511762922677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36666944384861007841948451 55000416577291511762922677)
              ·
                refine ⟨5156289054121079227774001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55000416577291511762922677 5156289054121079227774001)
                ·
                  refine ⟨3867216790590809420830501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5156289054121079227774001 3867216790590809420830501)
                  ·
                    refine ⟨725103148235776766405719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3867216790590809420830501 725103148235776766405719)
                    ·
                      rfl

theorem cell23_4236400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 2, 4].length) (baseStart_4236400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236400 prefixEnd_4236400 := by exact prefixLift 4236400
  have htrace : WordTrace (prefixWord ++ tailWord_4236400) baseStart_4236400 baseEnd_4236400 := by
    simpa [prefixWord, tailWord_4236400, baseEnd_4236400] using wordTrace_append hprefix tailTrace_4236400
  have hstable : (prefixWord ++ tailWord_4236400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236400).length < 2 ^ (prefixWord ++ tailWord_4236400).sum := by decide
  have hdescent : baseEnd_4236400 < baseStart_4236400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236407 : List Nat := [1, 1, 3, 1, 1, 4, 3, 2, 3, 2, 2]
def baseStart_4236407 : Nat := 118140960795 + 4236407 * 2 ^ 59
def prefixEnd_4236407 : Nat := 4983230072969 + 3 ^ 40 * 4236407 * 2
def baseEnd_4236407 : Nat := 2175313039071911771829625

theorem tailTrace_4236407 : CollatzResearch.WordTrace tailWord_4236407 prefixEnd_4236407 2175313039071911771829625 := by
  unfold tailWord_4236407
  simp only [CollatzResearch.WordTrace]
  refine ⟨154514457163228434558283475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103009638108818956372188983 154514457163228434558283475)
  ·
    refine ⟨231771685744842651837425213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154514457163228434558283475 231771685744842651837425213)
    ·
      refine ⟨86914382154315994439034455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231771685744842651837425213 86914382154315994439034455)
      ·
        refine ⟨130371573231473991658551683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86914382154315994439034455 130371573231473991658551683)
        ·
          refine ⟨195557359847210987487827525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130371573231473991658551683 195557359847210987487827525)
          ·
            refine ⟨36667004971352060153967661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 195557359847210987487827525 36667004971352060153967661)
            ·
              refine ⟨13750126864257022557737873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36667004971352060153967661 13750126864257022557737873)
              ·
                refine ⟨10312595148192766918303405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13750126864257022557737873 10312595148192766918303405)
                ·
                  refine ⟨3867223180572287594363777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10312595148192766918303405 3867223180572287594363777)
                  ·
                    refine ⟨2900417385429215695772833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3867223180572287594363777 2900417385429215695772833)
                    ·
                      refine ⟨2175313039071911771829625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2900417385429215695772833 2175313039071911771829625)
                      ·
                        rfl

theorem cell23_4236407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 2, 2].length) (baseStart_4236407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236407 prefixEnd_4236407 := by exact prefixLift 4236407
  have htrace : WordTrace (prefixWord ++ tailWord_4236407) baseStart_4236407 baseEnd_4236407 := by
    simpa [prefixWord, tailWord_4236407, baseEnd_4236407] using wordTrace_append hprefix tailTrace_4236407
  have hstable : (prefixWord ++ tailWord_4236407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236407).length < 2 ^ (prefixWord ++ tailWord_4236407).sum := by decide
  have hdescent : baseEnd_4236407 < baseStart_4236407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236420 : List Nat := [2, 3, 2, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_4236420 : Nat := 118140960795 + 4236420 * 2 ^ 59
def prefixEnd_4236420 : Nat := 4983230072969 + 3 ^ 40 * 4236420 * 2
def baseEnd_4236420 : Nat := 2175319714320420220967065

theorem tailTrace_4236420 : CollatzResearch.WordTrace tailWord_4236420 prefixEnd_4236420 2175319714320420220967065 := by
  unfold tailWord_4236420
  simp only [CollatzResearch.WordTrace]
  refine ⟨77257465656090668889253357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103009954208120891852337809 77257465656090668889253357)
  ·
    refine ⟨28971549621034000833470009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77257465656090668889253357 28971549621034000833470009)
    ·
      refine ⟨21728662215775500625102507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28971549621034000833470009 21728662215775500625102507)
      ·
        refine ⟨32592993323663250937653761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21728662215775500625102507 32592993323663250937653761)
        ·
          refine ⟨24444744992747438203240321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32592993323663250937653761 24444744992747438203240321)
          ·
            refine ⟨18333558744560578652430241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24444744992747438203240321 18333558744560578652430241)
            ·
              refine ⟨13750169058420433989322681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18333558744560578652430241 13750169058420433989322681)
              ·
                refine ⟨10312626793815325491992011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13750169058420433989322681 10312626793815325491992011)
                ·
                  refine ⟨15468940190722988237988017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10312626793815325491992011 15468940190722988237988017)
                  ·
                    refine ⟨11601705143042241178491013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15468940190722988237988017 11601705143042241178491013)
                    ·
                      refine ⟨2175319714320420220967065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11601705143042241178491013 2175319714320420220967065)
                      ·
                        rfl

theorem cell23_4236420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_4236420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236420 prefixEnd_4236420 := by exact prefixLift 4236420
  have htrace : WordTrace (prefixWord ++ tailWord_4236420) baseStart_4236420 baseEnd_4236420 := by
    simpa [prefixWord, tailWord_4236420, baseEnd_4236420] using wordTrace_append hprefix tailTrace_4236420
  have hstable : (prefixWord ++ tailWord_4236420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236420).length < 2 ^ (prefixWord ++ tailWord_4236420).sum := by decide
  have hdescent : baseEnd_4236420 < baseStart_4236420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236434 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 2, 4]
def baseStart_4236434 : Nat := 118140960795 + 4236434 * 2 ^ 59
def prefixEnd_4236434 : Nat := 4983230072969 + 3 ^ 40 * 4236434 * 2
def baseEnd_4236434 : Nat := 725108967683194388730667

theorem tailTrace_4236434 : CollatzResearch.WordTrace tailWord_4236434 prefixEnd_4236434 725108967683194388730667 := by
  unfold tailWord_4236434
  simp only [CollatzResearch.WordTrace]
  refine ⟨38628860483532654542379089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103010294622753745446344237 38628860483532654542379089)
  ·
    refine ⟨28971645362649490906784317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38628860483532654542379089 28971645362649490906784317)
    ·
      refine ⟨10864367010993559090044119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28971645362649490906784317 10864367010993559090044119)
      ·
        refine ⟨16296550516490338635066179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10864367010993559090044119 16296550516490338635066179)
        ·
          refine ⟨24444825774735507952599269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16296550516490338635066179 24444825774735507952599269)
          ·
            refine ⟨4583404832762907741112363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24444825774735507952599269 4583404832762907741112363)
            ·
              refine ⟨6875107249144361611668545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4583404832762907741112363 6875107249144361611668545)
              ·
                refine ⟨5156330436858271208751409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6875107249144361611668545 5156330436858271208751409)
                ·
                  refine ⟨3867247827643703406563557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5156330436858271208751409 3867247827643703406563557)
                  ·
                    refine ⟨725108967683194388730667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3867247827643703406563557 725108967683194388730667)
                    ·
                      rfl

theorem cell23_4236434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_4236434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236434 prefixEnd_4236434 := by exact prefixLift 4236434
  have htrace : WordTrace (prefixWord ++ tailWord_4236434) baseStart_4236434 baseEnd_4236434 := by
    simpa [prefixWord, tailWord_4236434, baseEnd_4236434] using wordTrace_append hprefix tailTrace_4236434
  have hstable : (prefixWord ++ tailWord_4236434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236434).length < 2 ^ (prefixWord ++ tailWord_4236434).sum := by decide
  have hdescent : baseEnd_4236434 < baseStart_4236434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236463 : List Nat := [1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 4]
def baseStart_4236463 : Nat := 118140960795 + 4236463 * 2 ^ 59
def prefixEnd_4236463 : Nat := 4983230072969 + 3 ^ 40 * 4236463 * 2
def baseEnd_4236463 : Nat := 2175341793988563552729367

theorem tailTrace_4236463 : CollatzResearch.WordTrace tailWord_4236463 prefixEnd_4236463 2175341793988563552729367 := by
  unfold tailWord_4236463
  simp only [CollatzResearch.WordTrace]
  refine ⟨154516499651025556122322043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103010999767350370748214695 154516499651025556122322043)
  ·
    refine ⟨231774749476538334183483065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154516499651025556122322043 231774749476538334183483065)
    ·
      refine ⟨173831062107403750637612299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231774749476538334183483065 173831062107403750637612299)
      ·
        refine ⟨260746593161105625956418449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173831062107403750637612299 260746593161105625956418449)
        ·
          refine ⟨195559944870829219467313837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260746593161105625956418449 195559944870829219467313837)
          ·
            refine ⟨73334979326560957300242689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195559944870829219467313837 73334979326560957300242689)
            ·
              refine ⟨55001234494920717975182017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73334979326560957300242689 55001234494920717975182017)
              ·
                refine ⟨41250925871190538481386513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55001234494920717975182017 41250925871190538481386513)
                ·
                  refine ⟨30938194403392903861039885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41250925871190538481386513 30938194403392903861039885)
                  ·
                    refine ⟨11601822901272338947889957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30938194403392903861039885 11601822901272338947889957)
                    ·
                      refine ⟨2175341793988563552729367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11601822901272338947889957 2175341793988563552729367)
                      ·
                        rfl

theorem cell23_4236463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 4].length) (baseStart_4236463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236463 prefixEnd_4236463 := by exact prefixLift 4236463
  have htrace : WordTrace (prefixWord ++ tailWord_4236463) baseStart_4236463 baseEnd_4236463 := by
    simpa [prefixWord, tailWord_4236463, baseEnd_4236463] using wordTrace_append hprefix tailTrace_4236463
  have hstable : (prefixWord ++ tailWord_4236463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236463).length < 2 ^ (prefixWord ++ tailWord_4236463).sum := by decide
  have hdescent : baseEnd_4236463 < baseStart_4236463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236467 : List Nat := [1, 1, 1, 2, 3, 2, 3, 4, 1, 3, 2]
def baseStart_4236467 : Nat := 118140960795 + 4236467 * 2 ^ 59
def prefixEnd_4236467 : Nat := 4983230072969 + 3 ^ 40 * 4236467 * 2
def baseEnd_4236467 : Nat := 2175343847911181537079349

theorem tailTrace_4236467 : CollatzResearch.WordTrace tailWord_4236467 prefixEnd_4236467 2175343847911181537079349 := by
  unfold tailWord_4236467
  simp only [CollatzResearch.WordTrace]
  refine ⟨154516645543011064805467655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103011097028674043203645103 154516645543011064805467655)
  ·
    refine ⟨231774968314516597208201483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154516645543011064805467655 231774968314516597208201483)
    ·
      refine ⟨347662452471774895812302225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231774968314516597208201483 347662452471774895812302225)
      ·
        refine ⟨260746839353831171859226669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347662452471774895812302225 260746839353831171859226669)
        ·
          refine ⟨97780064757686689447210001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 260746839353831171859226669 97780064757686689447210001)
          ·
            refine ⟨73335048568265017085407501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97780064757686689447210001 73335048568265017085407501)
            ·
              refine ⟨27500643213099381407027813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 73335048568265017085407501 27500643213099381407027813)
              ·
                refine ⟨5156370602456134013817715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27500643213099381407027813 5156370602456134013817715)
                ·
                  refine ⟨7734555903684201020726573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5156370602456134013817715 7734555903684201020726573)
                  ·
                    refine ⟨2900458463881575382772465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7734555903684201020726573 2900458463881575382772465)
                    ·
                      refine ⟨2175343847911181537079349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2900458463881575382772465 2175343847911181537079349)
                      ·
                        rfl

theorem cell23_4236467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 3, 2].length) (baseStart_4236467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236467 prefixEnd_4236467 := by exact prefixLift 4236467
  have htrace : WordTrace (prefixWord ++ tailWord_4236467) baseStart_4236467 baseEnd_4236467 := by
    simpa [prefixWord, tailWord_4236467, baseEnd_4236467] using wordTrace_append hprefix tailTrace_4236467
  have hstable : (prefixWord ++ tailWord_4236467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236467).length < 2 ^ (prefixWord ++ tailWord_4236467).sum := by decide
  have hdescent : baseEnd_4236467 < baseStart_4236467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236563 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 4, 8]
def baseStart_4236563 : Nat := 118140960795 + 4236563 * 2 ^ 59
def prefixEnd_4236563 : Nat := 4983230072969 + 3 ^ 40 * 4236563 * 2
def baseEnd_4236563 : Nat := 725131047351337720492969

theorem tailTrace_4236563 : CollatzResearch.WordTrace tailWord_4236563 prefixEnd_4236563 725131047351337720492969 := by
  unfold tailWord_4236563
  simp only [CollatzResearch.WordTrace]
  refine ⟨154520146950663273200962343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103013431300442182133974895 154520146950663273200962343)
  ·
    refine ⟨231780220425994909801443515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154520146950663273200962343 231780220425994909801443515)
    ·
      refine ⟨347670330638992364702165273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231780220425994909801443515 347670330638992364702165273)
      ·
        refine ⟨260752747979244273526623955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347670330638992364702165273 260752747979244273526623955)
        ·
          refine ⟨391129121968866410289935933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260752747979244273526623955 391129121968866410289935933)
          ·
            refine ⟨146673420738324903858725975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 391129121968866410289935933 146673420738324903858725975)
            ·
              refine ⟨220010131107487355788088963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146673420738324903858725975 220010131107487355788088963)
              ·
                refine ⟨330015196661231033682133445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220010131107487355788088963 330015196661231033682133445)
                ·
                  refine ⟨61877849373980818815400021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 330015196661231033682133445 61877849373980818815400021)
                  ·
                    refine ⟨725131047351337720492969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61877849373980818815400021 725131047351337720492969)
                    ·
                      rfl

theorem cell23_4236563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 8].length) (baseStart_4236563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236563 prefixEnd_4236563 := by exact prefixLift 4236563
  have htrace : WordTrace (prefixWord ++ tailWord_4236563) baseStart_4236563 baseEnd_4236563 := by
    simpa [prefixWord, tailWord_4236563, baseEnd_4236563] using wordTrace_append hprefix tailTrace_4236563
  have hstable : (prefixWord ++ tailWord_4236563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236563).length < 2 ^ (prefixWord ++ tailWord_4236563).sum := by decide
  have hdescent : baseEnd_4236563 < baseStart_4236563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236584 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 2, 5]
def baseStart_4236584 : Nat := 118140960795 + 4236584 * 2 ^ 59
def prefixEnd_4236584 : Nat := 4983230072969 + 3 ^ 40 * 4236584 * 2
def baseEnd_4236584 : Nat := 725134641715919193105437

theorem tailTrace_4236584 : CollatzResearch.WordTrace tailWord_4236584 prefixEnd_4236584 725134641715919193105437 := by
  unfold tailWord_4236584
  simp only [CollatzResearch.WordTrace]
  refine ⟨77260456441793596893738403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103013941922391462524984537 77260456441793596893738403)
  ·
    refine ⟨115890684662690395340607605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77260456441793596893738403 115890684662690395340607605)
    ·
      refine ⟨10864751687127224563181963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115890684662690395340607605 10864751687127224563181963)
      ·
        refine ⟨16297127530690836844772945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10864751687127224563181963 16297127530690836844772945)
        ·
          refine ⟨12222845648018127633579709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16297127530690836844772945 12222845648018127633579709)
          ·
            refine ⟨4583567118006797862592391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12222845648018127633579709 4583567118006797862592391)
            ·
              refine ⟨6875350677010196793888587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4583567118006797862592391 6875350677010196793888587)
              ·
                refine ⟨10313026015515295190832881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6875350677010196793888587 10313026015515295190832881)
                ·
                  refine ⟨7734769511636471393124661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10313026015515295190832881 7734769511636471393124661)
                  ·
                    refine ⟨725134641715919193105437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7734769511636471393124661 725134641715919193105437)
                    ·
                      rfl

theorem cell23_4236584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_4236584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236584 prefixEnd_4236584 := by exact prefixLift 4236584
  have htrace : WordTrace (prefixWord ++ tailWord_4236584) baseStart_4236584 baseEnd_4236584 := by
    simpa [prefixWord, tailWord_4236584, baseEnd_4236584] using wordTrace_append hprefix tailTrace_4236584
  have hstable : (prefixWord ++ tailWord_4236584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236584).length < 2 ^ (prefixWord ++ tailWord_4236584).sum := by decide
  have hdescent : baseEnd_4236584 < baseStart_4236584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236627 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 6]
def baseStart_4236627 : Nat := 118140960795 + 4236627 * 2 ^ 59
def prefixEnd_4236627 : Nat := 4983230072969 + 3 ^ 40 * 4236627 * 2
def baseEnd_4236627 : Nat := 241714000535100101230957

theorem tailTrace_4236627 : CollatzResearch.WordTrace tailWord_4236627 prefixEnd_4236627 241714000535100101230957 := by
  unfold tailWord_4236627
  simp only [CollatzResearch.WordTrace]
  refine ⟨154522481222431412131292135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103014987481620941420861423 154522481222431412131292135)
  ·
    refine ⟨231783721833647118196938203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154522481222431412131292135 231783721833647118196938203)
    ·
      refine ⟨347675582750470677295407305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231783721833647118196938203 347675582750470677295407305)
      ·
        refine ⟨260756687062853007971555479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347675582750470677295407305 260756687062853007971555479)
        ·
          refine ⟨391135030594279511957333219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260756687062853007971555479 391135030594279511957333219)
          ·
            refine ⟨586702545891419267935999829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391135030594279511957333219 586702545891419267935999829)
            ·
              refine ⟨3437710229832534773062499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 586702545891419267935999829 3437710229832534773062499)
              ·
                refine ⟨5156565344748802159593749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3437710229832534773062499 5156565344748802159593749)
                ·
                  refine ⟨241714000535100101230957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5156565344748802159593749 241714000535100101230957)
                  ·
                    rfl

theorem cell23_4236627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 6].length) (baseStart_4236627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236627 prefixEnd_4236627 := by exact prefixLift 4236627
  have htrace : WordTrace (prefixWord ++ tailWord_4236627) baseStart_4236627 baseEnd_4236627 := by
    simpa [prefixWord, tailWord_4236627, baseEnd_4236627] using wordTrace_append hprefix tailTrace_4236627
  have hstable : (prefixWord ++ tailWord_4236627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236627).length < 2 ^ (prefixWord ++ tailWord_4236627).sum := by decide
  have hdescent : baseEnd_4236627 < baseStart_4236627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236648 : List Nat := [2, 1, 4, 2, 3, 2, 1, 3, 1, 4]
def baseStart_4236648 : Nat := 118140960795 + 4236648 * 2 ^ 59
def prefixEnd_4236648 : Nat := 4983230072969 + 3 ^ 40 * 4236648 * 2
def baseEnd_4236648 : Nat := 725145595969881776305339

theorem tailTrace_4236648 : CollatzResearch.WordTrace tailWord_4236648 prefixEnd_4236648 725145595969881776305339 := by
  unfold tailWord_4236648
  simp only [CollatzResearch.WordTrace]
  refine ⟨77261623577677666358903299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103015498103570221811871065 77261623577677666358903299)
  ·
    refine ⟨115892435366516499538354949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77261623577677666358903299 115892435366516499538354949)
    ·
      refine ⟨21729831631221843663441553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115892435366516499538354949 21729831631221843663441553)
      ·
        refine ⟨16297373723416382747581165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21729831631221843663441553 16297373723416382747581165)
        ·
          refine ⟨6111515146281143530342937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16297373723416382747581165 6111515146281143530342937)
          ·
            refine ⟨4583636359710857647757203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6111515146281143530342937 4583636359710857647757203)
            ·
              refine ⟨6875454539566286471635805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4583636359710857647757203 6875454539566286471635805)
              ·
                refine ⟨2578295452337357426863427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6875454539566286471635805 2578295452337357426863427)
                ·
                  refine ⟨3867443178506036140295141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2578295452337357426863427 3867443178506036140295141)
                  ·
                    refine ⟨725145595969881776305339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3867443178506036140295141 725145595969881776305339)
                    ·
                      rfl

theorem cell23_4236648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_4236648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236648 prefixEnd_4236648 := by exact prefixLift 4236648
  have htrace : WordTrace (prefixWord ++ tailWord_4236648) baseStart_4236648 baseEnd_4236648 := by
    simpa [prefixWord, tailWord_4236648, baseEnd_4236648] using wordTrace_append hprefix tailTrace_4236648
  have hstable : (prefixWord ++ tailWord_4236648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236648).length < 2 ^ (prefixWord ++ tailWord_4236648).sum := by decide
  have hdescent : baseEnd_4236648 < baseStart_4236648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236657 : List Nat := [1, 2, 2, 2, 1, 2, 4, 3, 1, 5]
def baseStart_4236657 : Nat := 118140960795 + 4236657 * 2 ^ 59
def prefixEnd_4236657 : Nat := 4983230072969 + 3 ^ 40 * 4236657 * 2
def baseEnd_4236657 : Nat := 725147136411845264567825

theorem tailTrace_4236657 : CollatzResearch.WordTrace tailWord_4236657 prefixEnd_4236657 725147136411845264567825 := by
  unfold tailWord_4236657
  simp only [CollatzResearch.WordTrace]
  refine ⟨154523575412322727254884225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103015716941548484836589483 154523575412322727254884225)
  ·
    refine ⟨115892681559242045441163169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154523575412322727254884225 115892681559242045441163169)
    ·
      refine ⟨86919511169431534080872377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115892681559242045441163169 86919511169431534080872377)
      ·
        refine ⟨65189633377073650560654283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86919511169431534080872377 65189633377073650560654283)
        ·
          refine ⟨97784450065610475840981425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65189633377073650560654283 97784450065610475840981425)
          ·
            refine ⟨73338337549207856880736069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97784450065610475840981425 73338337549207856880736069)
            ·
              refine ⟨13750938290476473165138013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73338337549207856880736069 13750938290476473165138013)
              ·
                refine ⟨5156601858928677436926755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13750938290476473165138013 5156601858928677436926755)
                ·
                  refine ⟨7734902788393016155390133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5156601858928677436926755 7734902788393016155390133)
                  ·
                    refine ⟨725147136411845264567825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7734902788393016155390133 725147136411845264567825)
                    ·
                      rfl

theorem cell23_4236657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 5].length) (baseStart_4236657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236657 prefixEnd_4236657 := by exact prefixLift 4236657
  have htrace : WordTrace (prefixWord ++ tailWord_4236657) baseStart_4236657 baseEnd_4236657 := by
    simpa [prefixWord, tailWord_4236657, baseEnd_4236657] using wordTrace_append hprefix tailTrace_4236657
  have hstable : (prefixWord ++ tailWord_4236657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236657).length < 2 ^ (prefixWord ++ tailWord_4236657).sum := by decide
  have hdescent : baseEnd_4236657 < baseStart_4236657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236707 : List Nat := [1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 4]
def baseStart_4236707 : Nat := 118140960795 + 4236707 * 2 ^ 59
def prefixEnd_4236707 : Nat := 4983230072969 + 3 ^ 40 * 4236707 * 2
def baseEnd_4236707 : Nat := 2175467083268260598078245

theorem tailTrace_4236707 : CollatzResearch.WordTrace tailWord_4236707 prefixEnd_4236707 2175467083268260598078245 := by
  unfold tailWord_4236707
  simp only [CollatzResearch.WordTrace]
  refine ⟨154525399062141585794204375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103016932708094390529469583 154525399062141585794204375)
  ·
    refine ⟨231788098593212378691306563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154525399062141585794204375 231788098593212378691306563)
    ·
      refine ⟨347682147889818568036959845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231788098593212378691306563 347682147889818568036959845)
      ·
        refine ⟨65190402729340981506929971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 347682147889818568036959845 65190402729340981506929971)
        ·
          refine ⟨97785604094011472260394957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65190402729340981506929971 97785604094011472260394957)
          ·
            refine ⟨36669601535254302097648109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97785604094011472260394957 36669601535254302097648109)
            ·
              refine ⟨13751100575720363286618041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36669601535254302097648109 13751100575720363286618041)
              ·
                refine ⟨10313325431790272464963531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13751100575720363286618041 10313325431790272464963531)
                ·
                  refine ⟨15469988147685408697445297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10313325431790272464963531 15469988147685408697445297)
                  ·
                    refine ⟨11602491110764056523083973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15469988147685408697445297 11602491110764056523083973)
                    ·
                      refine ⟨2175467083268260598078245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11602491110764056523083973 2175467083268260598078245)
                      ·
                        rfl

theorem cell23_4236707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_4236707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236707 prefixEnd_4236707 := by exact prefixLift 4236707
  have htrace : WordTrace (prefixWord ++ tailWord_4236707) baseStart_4236707 baseEnd_4236707 := by
    simpa [prefixWord, tailWord_4236707, baseEnd_4236707] using wordTrace_append hprefix tailTrace_4236707
  have hstable : (prefixWord ++ tailWord_4236707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236707).length < 2 ^ (prefixWord ++ tailWord_4236707).sum := by decide
  have hdescent : baseEnd_4236707 < baseStart_4236707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236711 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_4236711 : Nat := 118140960795 + 4236711 * 2 ^ 59
def prefixEnd_4236711 : Nat := 4983230072969 + 3 ^ 40 * 4236711 * 2
def baseEnd_4236711 : Nat := 2175469137190878582428227

theorem tailTrace_4236711 : CollatzResearch.WordTrace tailWord_4236711 prefixEnd_4236711 2175469137190878582428227 := by
  unfold tailWord_4236711
  simp only [CollatzResearch.WordTrace]
  refine ⟨154525544954127094477349987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103017029969418062984899991 154525544954127094477349987)
  ·
    refine ⟨231788317431190641716024981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154525544954127094477349987 231788317431190641716024981)
    ·
      refine ⟨10865077379587061330438671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 231788317431190641716024981 10865077379587061330438671)
      ·
        refine ⟨16297616069380591995658007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10865077379587061330438671 16297616069380591995658007)
        ·
          refine ⟨24446424104070887993487011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16297616069380591995658007 24446424104070887993487011)
          ·
            refine ⟨36669636156106331990230517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24446424104070887993487011 36669636156106331990230517)
            ·
              refine ⟨3437778389634968624084111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36669636156106331990230517 3437778389634968624084111)
              ·
                refine ⟨5156667584452452936126167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3437778389634968624084111 5156667584452452936126167)
                ·
                  refine ⟨7735001376678679404189251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5156667584452452936126167 7735001376678679404189251)
                  ·
                    refine ⟨11602502065018019106283877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7735001376678679404189251 11602502065018019106283877)
                    ·
                      refine ⟨2175469137190878582428227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11602502065018019106283877 2175469137190878582428227)
                      ·
                        rfl

theorem cell23_4236711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_4236711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236711 prefixEnd_4236711 := by exact prefixLift 4236711
  have htrace : WordTrace (prefixWord ++ tailWord_4236711) baseStart_4236711 baseEnd_4236711 := by
    simpa [prefixWord, tailWord_4236711, baseEnd_4236711] using wordTrace_append hprefix tailTrace_4236711
  have hstable : (prefixWord ++ tailWord_4236711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236711).length < 2 ^ (prefixWord ++ tailWord_4236711).sum := by decide
  have hdescent : baseEnd_4236711 < baseStart_4236711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236717 : List Nat := [1, 5, 2, 2, 1, 12]
def baseStart_4236717 : Nat := 118140960795 + 4236717 * 2 ^ 59
def prefixEnd_4236717 : Nat := 4983230072969 + 3 ^ 40 * 4236717 * 2
def baseEnd_4236717 : Nat := 8952560568209076374293

theorem tailTrace_4236717 : CollatzResearch.WordTrace tailWord_4236717 prefixEnd_4236717 8952560568209076374293 := by
  unfold tailWord_4236717
  simp only [CollatzResearch.WordTrace]
  refine ⟨154525763792105357502068405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103017175861403571668045603 154525763792105357502068405)
  ·
    refine ⟨14486790355509877265818913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 154525763792105357502068405 14486790355509877265818913)
    ·
      refine ⟨10865092766632407949364185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14486790355509877265818913 10865092766632407949364185)
      ·
        refine ⟨8148819574974305962023139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10865092766632407949364185 8148819574974305962023139)
        ·
          refine ⟨12223229362461458943034709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8148819574974305962023139 12223229362461458943034709)
          ·
            refine ⟨8952560568209076374293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 12223229362461458943034709 8952560568209076374293)
            ·
              rfl

theorem cell23_4236717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 12].length) (baseStart_4236717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236717 prefixEnd_4236717 := by exact prefixLift 4236717
  have htrace : WordTrace (prefixWord ++ tailWord_4236717) baseStart_4236717 baseEnd_4236717 := by
    simpa [prefixWord, tailWord_4236717, baseEnd_4236717] using wordTrace_append hprefix tailTrace_4236717
  have hstable : (prefixWord ++ tailWord_4236717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236717).length < 2 ^ (prefixWord ++ tailWord_4236717).sum := by decide
  have hdescent : baseEnd_4236717 < baseStart_4236717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236720 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_4236720 : Nat := 118140960795 + 4236720 * 2 ^ 59
def prefixEnd_4236720 : Nat := 4983230072969 + 3 ^ 40 * 4236720 * 2
def baseEnd_4236720 : Nat := 2175473758516769047215685

theorem tailTrace_4236720 : CollatzResearch.WordTrace tailWord_4236720 prefixEnd_4236720 2175473758516769047215685 := by
  unfold tailWord_4236720
  simp only [CollatzResearch.WordTrace]
  refine ⟨77262936605547244507213807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103017248807396326009618409 77262936605547244507213807)
  ·
    refine ⟨115894404908320866760820711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77262936605547244507213807 115894404908320866760820711)
    ·
      refine ⟨173841607362481300141231067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115894404908320866760820711 173841607362481300141231067)
      ·
        refine ⟨260762411043721950211846601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173841607362481300141231067 260762411043721950211846601)
        ·
          refine ⟨195571808282791462658884951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260762411043721950211846601 195571808282791462658884951)
          ·
            refine ⟨293357712424187193988327427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195571808282791462658884951 293357712424187193988327427)
            ·
              refine ⟨440036568636280790982491141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293357712424187193988327427 440036568636280790982491141)
              ·
                refine ⟨82506856619302648309217089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 440036568636280790982491141 82506856619302648309217089)
                ·
                  refine ⟨61880142464476986231912817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82506856619302648309217089 61880142464476986231912817)
                  ·
                    refine ⟨46410106848357739673934613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61880142464476986231912817 46410106848357739673934613)
                    ·
                      refine ⟨2175473758516769047215685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46410106848357739673934613 2175473758516769047215685)
                      ·
                        rfl

theorem cell23_4236720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_4236720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236720 prefixEnd_4236720 := by exact prefixLift 4236720
  have htrace : WordTrace (prefixWord ++ tailWord_4236720) baseStart_4236720 baseEnd_4236720 := by
    simpa [prefixWord, tailWord_4236720, baseEnd_4236720] using wordTrace_append hprefix tailTrace_4236720
  have hstable : (prefixWord ++ tailWord_4236720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236720).length < 2 ^ (prefixWord ++ tailWord_4236720).sum := by decide
  have hdescent : baseEnd_4236720 < baseStart_4236720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236727 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 3]
def baseStart_4236727 : Nat := 118140960795 + 4236727 * 2 ^ 59
def prefixEnd_4236727 : Nat := 4983230072969 + 3 ^ 40 * 4236727 * 2
def baseEnd_4236727 : Nat := 2175477352881350519828153

theorem tailTrace_4236727 : CollatzResearch.WordTrace tailWord_4236727 prefixEnd_4236727 2175477352881350519828153 := by
  unfold tailWord_4236727
  simp only [CollatzResearch.WordTrace]
  refine ⟨154526128522069129209932435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103017419014712752806621623 154526128522069129209932435)
  ·
    refine ⟨231789192783103693814898653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154526128522069129209932435 231789192783103693814898653)
    ·
      refine ⟨86920947293663885180586995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231789192783103693814898653 86920947293663885180586995)
      ·
        refine ⟨130381420940495827770880493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86920947293663885180586995 130381420940495827770880493)
        ·
          refine ⟨48893032852685935414080185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130381420940495827770880493 48893032852685935414080185)
          ·
            refine ⟨36669774639514451560560139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48893032852685935414080185 36669774639514451560560139)
            ·
              refine ⟨55004661959271677340840209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36669774639514451560560139 55004661959271677340840209)
              ·
                refine ⟨41253496469453758005630157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55004661959271677340840209 41253496469453758005630157)
                ·
                  refine ⟨15470061176045159252111309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41253496469453758005630157 15470061176045159252111309)
                  ·
                    refine ⟨5801272941016934719541741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15470061176045159252111309 5801272941016934719541741)
                    ·
                      refine ⟨2175477352881350519828153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5801272941016934719541741 2175477352881350519828153)
                      ·
                        rfl

theorem cell23_4236727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 3].length) (baseStart_4236727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236727 prefixEnd_4236727 := by exact prefixLift 4236727
  have htrace : WordTrace (prefixWord ++ tailWord_4236727) baseStart_4236727 baseEnd_4236727 := by
    simpa [prefixWord, tailWord_4236727, baseEnd_4236727] using wordTrace_append hprefix tailTrace_4236727
  have hstable : (prefixWord ++ tailWord_4236727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236727).length < 2 ^ (prefixWord ++ tailWord_4236727).sum := by decide
  have hdescent : baseEnd_4236727 < baseStart_4236727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236744 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_4236744 : Nat := 118140960795 + 4236744 * 2 ^ 59
def prefixEnd_4236744 : Nat := 4983230072969 + 3 ^ 40 * 4236744 * 2
def baseEnd_4236744 : Nat := 2175486082052476953315575

theorem tailTrace_4236744 : CollatzResearch.WordTrace tailWord_4236744 prefixEnd_4236744 2175486082052476953315575 := by
  unfold tailWord_4236744
  simp only [CollatzResearch.WordTrace]
  refine ⟨77263374281503770556650643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103017832375338360742200857 77263374281503770556650643)
  ·
    refine ⟨115895061422255655834975965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77263374281503770556650643 115895061422255655834975965)
    ·
      refine ⟨43460648033345870938115987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115895061422255655834975965 43460648033345870938115987)
      ·
        refine ⟨65190972050018806407173981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43460648033345870938115987 65190972050018806407173981)
        ·
          refine ⟨24446614518757052402690243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65190972050018806407173981 24446614518757052402690243)
          ·
            refine ⟨36669921778135578604035365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24446614518757052402690243 36669921778135578604035365)
            ·
              refine ⟨6875610333400420988256631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36669921778135578604035365 6875610333400420988256631)
              ·
                refine ⟨10313415500100631482384947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6875610333400420988256631 10313415500100631482384947)
                ·
                  refine ⟨15470123250150947223577421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10313415500100631482384947 15470123250150947223577421)
                  ·
                    refine ⟨5801296218806605208841533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15470123250150947223577421 5801296218806605208841533)
                    ·
                      refine ⟨2175486082052476953315575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5801296218806605208841533 2175486082052476953315575)
                      ·
                        rfl

theorem cell23_4236744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_4236744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236744 prefixEnd_4236744 := by exact prefixLift 4236744
  have htrace : WordTrace (prefixWord ++ tailWord_4236744) baseStart_4236744 baseEnd_4236744 := by
    simpa [prefixWord, tailWord_4236744, baseEnd_4236744] using wordTrace_append hprefix tailTrace_4236744
  have hstable : (prefixWord ++ tailWord_4236744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236744).length < 2 ^ (prefixWord ++ tailWord_4236744).sum := by decide
  have hdescent : baseEnd_4236744 < baseStart_4236744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236757 : List Nat := [1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_4236757 : Nat := 118140960795 + 4236757 * 2 ^ 59
def prefixEnd_4236757 : Nat := 4983230072969 + 3 ^ 40 * 4236757 * 2
def baseEnd_4236757 : Nat := 2175492757300985402453015

theorem tailTrace_4236757 : CollatzResearch.WordTrace tailWord_4236757 prefixEnd_4236757 2175492757300985402453015 := by
  unfold tailWord_4236757
  simp only [CollatzResearch.WordTrace]
  refine ⟨154527222711960444333524525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103018148474640296222349683 154527222711960444333524525)
  ·
    refine ⟨57947708516985166625071697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154527222711960444333524525 57947708516985166625071697)
    ·
      refine ⟨43460781387738874968803773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57947708516985166625071697 43460781387738874968803773)
      ·
        refine ⟨16297793020402078113301415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43460781387738874968803773 16297793020402078113301415)
        ·
          refine ⟨24446689530603117169952123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16297793020402078113301415 24446689530603117169952123)
          ·
            refine ⟨36670034295904675754928185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24446689530603117169952123 36670034295904675754928185)
            ·
              refine ⟨27502525721928506816196139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36670034295904675754928185 27502525721928506816196139)
              ·
                refine ⟨41253788582892760224294209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27502525721928506816196139 41253788582892760224294209)
                ·
                  refine ⟨30940341437169570168220657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41253788582892760224294209 30940341437169570168220657)
                  ·
                    refine ⟨23205256077877177626165493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30940341437169570168220657 23205256077877177626165493)
                    ·
                      refine ⟨2175492757300985402453015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23205256077877177626165493 2175492757300985402453015)
                      ·
                        rfl

theorem cell23_4236757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_4236757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236757 prefixEnd_4236757 := by exact prefixLift 4236757
  have htrace : WordTrace (prefixWord ++ tailWord_4236757) baseStart_4236757 baseEnd_4236757 := by
    simpa [prefixWord, tailWord_4236757, baseEnd_4236757] using wordTrace_append hprefix tailTrace_4236757
  have hstable : (prefixWord ++ tailWord_4236757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236757).length < 2 ^ (prefixWord ++ tailWord_4236757).sum := by decide
  have hdescent : baseEnd_4236757 < baseStart_4236757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236787 : List Nat := [1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 3]
def baseStart_4236787 : Nat := 118140960795 + 4236787 * 2 ^ 59
def prefixEnd_4236787 : Nat := 4983230072969 + 3 ^ 40 * 4236787 * 2
def baseEnd_4236787 : Nat := 2175508161720620285077877

theorem tailTrace_4236787 : CollatzResearch.WordTrace tailWord_4236787 prefixEnd_4236787 2175508161720620285077877 := by
  unfold tailWord_4236787
  simp only [CollatzResearch.WordTrace]
  refine ⟨154528316901851759457116615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103018877934567839638077743 154528316901851759457116615)
  ·
    refine ⟨231792475352777639185674923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154528316901851759457116615 231792475352777639185674923)
    ·
      refine ⟨347688713029166458778512385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231792475352777639185674923 347688713029166458778512385)
      ·
        refine ⟨260766534771874844083884289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 347688713029166458778512385 260766534771874844083884289)
        ·
          refine ⟨195574901078906133062913217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260766534771874844083884289 195574901078906133062913217)
          ·
            refine ⟨146681175809179599797184913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195574901078906133062913217 146681175809179599797184913)
            ·
              refine ⟨110010881856884699847888685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146681175809179599797184913 110010881856884699847888685)
              ·
                refine ⟨41254080696331762442958257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110010881856884699847888685 41254080696331762442958257)
                ·
                  refine ⟨30940560522248821832218693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41254080696331762442958257 30940560522248821832218693)
                  ·
                    refine ⟨5801355097921654093541005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30940560522248821832218693 5801355097921654093541005)
                    ·
                      refine ⟨2175508161720620285077877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5801355097921654093541005 2175508161720620285077877)
                      ·
                        rfl

theorem cell23_4236787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 3].length) (baseStart_4236787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236787 prefixEnd_4236787 := by exact prefixLift 4236787
  have htrace : WordTrace (prefixWord ++ tailWord_4236787) baseStart_4236787 baseEnd_4236787 := by
    simpa [prefixWord, tailWord_4236787, baseEnd_4236787] using wordTrace_append hprefix tailTrace_4236787
  have hstable : (prefixWord ++ tailWord_4236787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236787).length < 2 ^ (prefixWord ++ tailWord_4236787).sum := by decide
  have hdescent : baseEnd_4236787 < baseStart_4236787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236834 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_4236834 : Nat := 118140960795 + 4236834 * 2 ^ 59
def prefixEnd_4236834 : Nat := 4983230072969 + 3 ^ 40 * 4236834 * 2
def baseEnd_4236834 : Nat := 2175532295311381601190161

theorem tailTrace_4236834 : CollatzResearch.WordTrace tailWord_4236834 prefixEnd_4236834 2175532295311381601190161 := by
  unfold tailWord_4236834
  simp only [CollatzResearch.WordTrace]
  refine ⟨38632507783170371621019389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103020020755120990989385037 38632507783170371621019389)
  ·
    refine ⟨14487190418688889357882271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38632507783170371621019389 14487190418688889357882271)
    ·
      refine ⟨21730785628033334036823407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14487190418688889357882271 21730785628033334036823407)
      ·
        refine ⟨32596178442050001055235111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21730785628033334036823407 32596178442050001055235111)
        ·
          refine ⟨48894267663075001582852667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32596178442050001055235111 48894267663075001582852667)
          ·
            refine ⟨73341401494612502374279001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48894267663075001582852667 73341401494612502374279001)
            ·
              refine ⟨55006051120959376780709251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73341401494612502374279001 55006051120959376780709251)
              ·
                refine ⟨82509076681439065171063877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55006051120959376780709251 82509076681439065171063877)
                ·
                  refine ⟨15470451877769824719574477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82509076681439065171063877 15470451877769824719574477)
                  ·
                    refine ⟨5801419454163684269840429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15470451877769824719574477 5801419454163684269840429)
                    ·
                      refine ⟨2175532295311381601190161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5801419454163684269840429 2175532295311381601190161)
                      ·
                        rfl

theorem cell23_4236834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_4236834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236834 prefixEnd_4236834 := by exact prefixLift 4236834
  have htrace : WordTrace (prefixWord ++ tailWord_4236834) baseStart_4236834 baseEnd_4236834 := by
    simpa [prefixWord, tailWord_4236834, baseEnd_4236834] using wordTrace_append hprefix tailTrace_4236834
  have hstable : (prefixWord ++ tailWord_4236834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236834).length < 2 ^ (prefixWord ++ tailWord_4236834).sum := by decide
  have hdescent : baseEnd_4236834 < baseStart_4236834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236871 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 2, 5]
def baseStart_4236871 : Nat := 118140960795 + 4236871 * 2 ^ 59
def prefixEnd_4236871 : Nat := 4983230072969 + 3 ^ 40 * 4236871 * 2
def baseEnd_4236871 : Nat := 725183764698532652142497

theorem tailTrace_4236871 : CollatzResearch.WordTrace tailWord_4236871 prefixEnd_4236871 725183764698532652142497 := by
  unfold tailWord_4236871
  simp only [CollatzResearch.WordTrace]
  refine ⟨154531380633547441803174467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103020920422364961202116311 154531380633547441803174467)
  ·
    refine ⟨231797070950321162704761701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154531380633547441803174467 231797070950321162704761701)
    ·
      refine ⟨43461950803185218007142819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231797070950321162704761701 43461950803185218007142819)
      ·
        refine ⟨65192926204777827010714229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43461950803185218007142819 65192926204777827010714229)
        ·
          refine ⟨6111836831697921282254459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65192926204777827010714229 6111836831697921282254459)
          ·
            refine ⟨9167755247546881923381689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6111836831697921282254459 9167755247546881923381689)
            ·
              refine ⟨6875816435660161442536267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9167755247546881923381689 6875816435660161442536267)
              ·
                refine ⟨10313724653490242163804401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6875816435660161442536267 10313724653490242163804401)
                ·
                  refine ⟨7735293490117681622853301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10313724653490242163804401 7735293490117681622853301)
                  ·
                    refine ⟨725183764698532652142497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7735293490117681622853301 725183764698532652142497)
                    ·
                      rfl

theorem cell23_4236871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_4236871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236871 prefixEnd_4236871 := by exact prefixLift 4236871
  have htrace : WordTrace (prefixWord ++ tailWord_4236871) baseStart_4236871 baseEnd_4236871 := by
    simpa [prefixWord, tailWord_4236871, baseEnd_4236871] using wordTrace_append hprefix tailTrace_4236871
  have hstable : (prefixWord ++ tailWord_4236871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236871).length < 2 ^ (prefixWord ++ tailWord_4236871).sum := by decide
  have hdescent : baseEnd_4236871 < baseStart_4236871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236918 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_4236918 : Nat := 118140960795 + 4236918 * 2 ^ 59
def prefixEnd_4236918 : Nat := 4983230072969 + 3 ^ 40 * 4236918 * 2
def baseEnd_4236918 : Nat := 725191809228786424179925

theorem tailTrace_4236918 : CollatzResearch.WordTrace tailWord_4236918 prefixEnd_4236918 725191809228786424179925 := by
  unfold tailWord_4236918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9658318429023573051883463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103022063242918112553423605 9658318429023573051883463)
  ·
    refine ⟨14487477643535359577825195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9658318429023573051883463 14487477643535359577825195)
    ·
      refine ⟨21731216465303039366737793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14487477643535359577825195 21731216465303039366737793)
      ·
        refine ⟨16298412348977279525053345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21731216465303039366737793 16298412348977279525053345)
        ·
          refine ⟨12223809261732959643790009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16298412348977279525053345 12223809261732959643790009)
          ·
            refine ⟨9167856946299719732842507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12223809261732959643790009 9167856946299719732842507)
            ·
              refine ⟨13751785419449579599263761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9167856946299719732842507 13751785419449579599263761)
              ·
                refine ⟨10313839064587184699447821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13751785419449579599263761 10313839064587184699447821)
                ·
                  refine ⟨3867689649220194262292933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10313839064587184699447821 3867689649220194262292933)
                  ·
                    refine ⟨725191809228786424179925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3867689649220194262292933 725191809228786424179925)
                    ·
                      rfl

theorem cell23_4236918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_4236918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236918 prefixEnd_4236918 := by exact prefixLift 4236918
  have htrace : WordTrace (prefixWord ++ tailWord_4236918) baseStart_4236918 baseEnd_4236918 := by
    simpa [prefixWord, tailWord_4236918, baseEnd_4236918] using wordTrace_append hprefix tailTrace_4236918
  have hstable : (prefixWord ++ tailWord_4236918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236918).length < 2 ^ (prefixWord ++ tailWord_4236918).sum := by decide
  have hdescent : baseEnd_4236918 < baseStart_4236918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4236984 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 2, 6, 3]
def baseStart_4236984 : Nat := 118140960795 + 4236984 * 2 ^ 59
def prefixEnd_4236984 : Nat := 4983230072969 + 3 ^ 40 * 4236984 * 2
def baseEnd_4236984 : Nat := 2175609317409556014314471

theorem tailTrace_4236984 : CollatzResearch.WordTrace tailWord_4236984 prefixEnd_4236984 2175609317409556014314471 := by
  unfold tailWord_4236984
  simp only [CollatzResearch.WordTrace]
  refine ⟨77267751041069031051019003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103023668054758708068025337 77267751041069031051019003)
  ·
    refine ⟨115901626561603546576528505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77267751041069031051019003 115901626561603546576528505)
    ·
      refine ⟨86926219921202659932396379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115901626561603546576528505 86926219921202659932396379)
      ·
        refine ⟨130389329881803989898594569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86926219921202659932396379 130389329881803989898594569)
        ·
          refine ⟨97791997411352992423945927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130389329881803989898594569 97791997411352992423945927)
          ·
            refine ⟨146687996117029488635918891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97791997411352992423945927 146687996117029488635918891)
            ·
              refine ⟨220031994175544232953878337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146687996117029488635918891 220031994175544232953878337)
              ·
                refine ⟨165023995631658174715408753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220031994175544232953878337 165023995631658174715408753)
                ·
                  refine ⟨123767996723743631036556565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 165023995631658174715408753 123767996723743631036556565)
                  ·
                    refine ⟨5801624846425482704838589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 123767996723743631036556565 5801624846425482704838589)
                    ·
                      refine ⟨2175609317409556014314471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5801624846425482704838589 2175609317409556014314471)
                      ·
                        rfl

theorem cell23_4236984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_4236984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4236984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4236984 prefixEnd_4236984 := by exact prefixLift 4236984
  have htrace : WordTrace (prefixWord ++ tailWord_4236984) baseStart_4236984 baseEnd_4236984 := by
    simpa [prefixWord, tailWord_4236984, baseEnd_4236984] using wordTrace_append hprefix tailTrace_4236984
  have hstable : (prefixWord ++ tailWord_4236984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4236984).length < 2 ^ (prefixWord ++ tailWord_4236984).sum := by decide
  have hdescent : baseEnd_4236984 < baseStart_4236984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4236984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237104 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_4237104 : Nat := 118140960795 + 4237104 * 2 ^ 59
def prefixEnd_4237104 : Nat := 4983230072969 + 3 ^ 40 * 4237104 * 2
def baseEnd_4237104 : Nat := 2175670935088095544813919

theorem tailTrace_4237104 : CollatzResearch.WordTrace tailWord_4237104 prefixEnd_4237104 2175670935088095544813919 := by
  unfold tailWord_4237104
  simp only [CollatzResearch.WordTrace]
  refine ⟨77269939420851661298203183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103026585894468881730937577 77269939420851661298203183)
  ·
    refine ⟨115904909131277491947304775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77269939420851661298203183 115904909131277491947304775)
    ·
      refine ⟨173857363696916237920957163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115904909131277491947304775 173857363696916237920957163)
      ·
        refine ⟨260786045545374356881435745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173857363696916237920957163 260786045545374356881435745)
        ·
          refine ⟨195589534159030767661076809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260786045545374356881435745 195589534159030767661076809)
          ·
            refine ⟨146692150619273075745807607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195589534159030767661076809 146692150619273075745807607)
            ·
              refine ⟨220038225928909613618711411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146692150619273075745807607 220038225928909613618711411)
              ·
                refine ⟨330057338893364420428067117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220038225928909613618711411 330057338893364420428067117)
                ·
                  refine ⟨123771502085011657660525169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 330057338893364420428067117 123771502085011657660525169)
                  ·
                    refine ⟨92828626563758743245393877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123771502085011657660525169 92828626563758743245393877)
                    ·
                      refine ⟨2175670935088095544813919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92828626563758743245393877 2175670935088095544813919)
                      ·
                        rfl

theorem cell23_4237104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_4237104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237104 prefixEnd_4237104 := by exact prefixLift 4237104
  have htrace : WordTrace (prefixWord ++ tailWord_4237104) baseStart_4237104 baseEnd_4237104 := by
    simpa [prefixWord, tailWord_4237104, baseEnd_4237104] using wordTrace_append hprefix tailTrace_4237104
  have hstable : (prefixWord ++ tailWord_4237104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237104).length < 2 ^ (prefixWord ++ tailWord_4237104).sum := by decide
  have hdescent : baseEnd_4237104 < baseStart_4237104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237109 : List Nat := [1, 3, 3, 1, 4, 2, 2, 1, 1, 3, 2]
def baseStart_4237109 : Nat := 118140960795 + 4237109 * 2 ^ 59
def prefixEnd_4237109 : Nat := 4983230072969 + 3 ^ 40 * 4237109 * 2
def baseEnd_4237109 : Nat := 2175673502491368025251397

theorem tailTrace_4237109 : CollatzResearch.WordTrace tailWord_4237109 prefixEnd_4237109 2175673502491368025251397 := by
  unfold tailWord_4237109
  simp only [CollatzResearch.WordTrace]
  refine ⟨154540061206685208450338381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103026707471123472300225587 154540061206685208450338381)
  ·
    refine ⟨57952522952506953168876893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154540061206685208450338381 57952522952506953168876893)
    ·
      refine ⟨21732196107190107438328835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57952522952506953168876893 21732196107190107438328835)
      ·
        refine ⟨32598294160785161157493253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21732196107190107438328835 32598294160785161157493253)
        ·
          refine ⟨6112180155147217717029985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32598294160785161157493253 6112180155147217717029985)
          ·
            refine ⟨4584135116360413287772489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6112180155147217717029985 4584135116360413287772489)
            ·
              refine ⟨3438101337270309965829367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4584135116360413287772489 3438101337270309965829367)
              ·
                refine ⟨5157152005905464948744051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3438101337270309965829367 5157152005905464948744051)
                ·
                  refine ⟨7735728008858197423116077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5157152005905464948744051 7735728008858197423116077)
                  ·
                    refine ⟨2900898003321824033668529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7735728008858197423116077 2900898003321824033668529)
                    ·
                      refine ⟨2175673502491368025251397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2900898003321824033668529 2175673502491368025251397)
                      ·
                        rfl

theorem cell23_4237109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_4237109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237109 prefixEnd_4237109 := by exact prefixLift 4237109
  have htrace : WordTrace (prefixWord ++ tailWord_4237109) baseStart_4237109 baseEnd_4237109 := by
    simpa [prefixWord, tailWord_4237109, baseEnd_4237109] using wordTrace_append hprefix tailTrace_4237109
  have hstable : (prefixWord ++ tailWord_4237109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237109).length < 2 ^ (prefixWord ++ tailWord_4237109).sum := by decide
  have hdescent : baseEnd_4237109 < baseStart_4237109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237118 : List Nat := [4, 2, 1, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_4237118 : Nat := 118140960795 + 4237118 * 2 ^ 59
def prefixEnd_4237118 : Nat := 4983230072969 + 3 ^ 40 * 4237118 * 2
def baseEnd_4237118 : Nat := 2175678123817258490038855

theorem tailTrace_4237118 : CollatzResearch.WordTrace tailWord_4237118 prefixEnd_4237118 2175678123817258490038855 := by
  unfold tailWord_4237118
  simp only [CollatzResearch.WordTrace]
  refine ⟨19317548682956575373427001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103026926309101735324944005 19317548682956575373427001)
  ·
    refine ⟨14488161512217431530070251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19317548682956575373427001 14488161512217431530070251)
    ·
      refine ⟨21732242268326147295105377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14488161512217431530070251 21732242268326147295105377)
      ·
        refine ⟨16299181701244610471329033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21732242268326147295105377 16299181701244610471329033)
        ·
          refine ⟨12224386275933457853496775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16299181701244610471329033 12224386275933457853496775)
          ·
            refine ⟨18336579413900186780245163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12224386275933457853496775 18336579413900186780245163)
            ·
              refine ⟨27504869120850280170367745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18336579413900186780245163 27504869120850280170367745)
              ·
                refine ⟨20628651840637710127775809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27504869120850280170367745 20628651840637710127775809)
                ·
                  refine ⟨15471488880478282595831857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20628651840637710127775809 15471488880478282595831857)
                  ·
                    refine ⟨11603616660358711946873893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15471488880478282595831857 11603616660358711946873893)
                    ·
                      refine ⟨2175678123817258490038855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11603616660358711946873893 2175678123817258490038855)
                      ·
                        rfl

theorem cell23_4237118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_4237118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237118 prefixEnd_4237118 := by exact prefixLift 4237118
  have htrace : WordTrace (prefixWord ++ tailWord_4237118) baseStart_4237118 baseEnd_4237118 := by
    simpa [prefixWord, tailWord_4237118, baseEnd_4237118] using wordTrace_append hprefix tailTrace_4237118
  have hstable : (prefixWord ++ tailWord_4237118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237118).length < 2 ^ (prefixWord ++ tailWord_4237118).sum := by decide
  have hdescent : baseEnd_4237118 < baseStart_4237118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237128 : List Nat := [2, 1, 3, 1, 1, 4, 2, 4, 5]
def baseStart_4237128 : Nat := 118140960795 + 4237128 * 2 ^ 59
def prefixEnd_4237128 : Nat := 4983230072969 + 3 ^ 40 * 4237128 * 2
def baseEnd_4237128 : Nat := 241742584291533716768201

theorem tailTrace_4237128 : CollatzResearch.WordTrace tailWord_4237128 prefixEnd_4237128 241742584291533716768201 := by
  unfold tailWord_4237128
  simp only [CollatzResearch.WordTrace]
  refine ⟨77270377096808187347640019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103027169462410916463520025 77270377096808187347640019)
  ·
    refine ⟨115905565645212281021460029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77270377096808187347640019 115905565645212281021460029)
    ·
      refine ⟨43464587116954605383047511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115905565645212281021460029 43464587116954605383047511)
      ·
        refine ⟨65196880675431908074571267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43464587116954605383047511 65196880675431908074571267)
        ·
          refine ⟨97795321013147862111856901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65196880675431908074571267 97795321013147862111856901)
          ·
            refine ⟨18336622689965224145973169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97795321013147862111856901 18336622689965224145973169)
            ·
              refine ⟨13752467017473918109479877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18336622689965224145973169 13752467017473918109479877)
              ·
                refine ⟨2578587565776359645527477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13752467017473918109479877 2578587565776359645527477)
                ·
                  refine ⟨241742584291533716768201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2578587565776359645527477 241742584291533716768201)
                  ·
                    rfl

theorem cell23_4237128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 5].length) (baseStart_4237128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237128 prefixEnd_4237128 := by exact prefixLift 4237128
  have htrace : WordTrace (prefixWord ++ tailWord_4237128) baseStart_4237128 baseEnd_4237128 := by
    simpa [prefixWord, tailWord_4237128, baseEnd_4237128] using wordTrace_append hprefix tailTrace_4237128
  have hstable : (prefixWord ++ tailWord_4237128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237128).length < 2 ^ (prefixWord ++ tailWord_4237128).sum := by decide
  have hdescent : baseEnd_4237128 < baseStart_4237128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237138 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_4237138 : Nat := 118140960795 + 4237138 * 2 ^ 59
def prefixEnd_4237138 : Nat := 4983230072969 + 3 ^ 40 * 4237138 * 2
def baseEnd_4237138 : Nat := 2175688393430348411788763

theorem tailTrace_4237138 : CollatzResearch.WordTrace tailWord_4237138 prefixEnd_4237138 2175688393430348411788763 := by
  unfold tailWord_4237138
  simp only [CollatzResearch.WordTrace]
  refine ⟨38635279730895036600786017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103027412615720097602096045 38635279730895036600786017)
  ·
    refine ⟨28976459798171277450589513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38635279730895036600786017 28976459798171277450589513)
    ·
      refine ⟨21732344848628458087942135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28976459798171277450589513 21732344848628458087942135)
      ·
        refine ⟨32598517272942687131913203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21732344848628458087942135 32598517272942687131913203)
        ·
          refine ⟨48897775909414030697869805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32598517272942687131913203 48897775909414030697869805)
          ·
            refine ⟨18336665966030261511701177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48897775909414030697869805 18336665966030261511701177)
            ·
              refine ⟨13752499474522696133775883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18336665966030261511701177 13752499474522696133775883)
              ·
                refine ⟨20628749211784044200663825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13752499474522696133775883 20628749211784044200663825)
                ·
                  refine ⟨15471561908838033150497869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20628749211784044200663825 15471561908838033150497869)
                  ·
                    refine ⟨5801835715814262431436701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15471561908838033150497869 5801835715814262431436701)
                    ·
                      refine ⟨2175688393430348411788763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5801835715814262431436701 2175688393430348411788763)
                      ·
                        rfl

theorem cell23_4237138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_4237138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237138 prefixEnd_4237138 := by exact prefixLift 4237138
  have htrace : WordTrace (prefixWord ++ tailWord_4237138) baseStart_4237138 baseEnd_4237138 := by
    simpa [prefixWord, tailWord_4237138, baseEnd_4237138] using wordTrace_append hprefix tailTrace_4237138
  have hstable : (prefixWord ++ tailWord_4237138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237138).length < 2 ^ (prefixWord ++ tailWord_4237138).sum := by decide
  have hdescent : baseEnd_4237138 < baseStart_4237138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237141 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 1, 7]
def baseStart_4237141 : Nat := 118140960795 + 4237141 * 2 ^ 59
def prefixEnd_4237141 : Nat := 4983230072969 + 3 ^ 40 * 4237141 * 2
def baseEnd_4237141 : Nat := 725229977957437300017083

theorem tailTrace_4237141 : CollatzResearch.WordTrace tailWord_4237141 prefixEnd_4237141 725229977957437300017083 := by
  unfold tailWord_4237141
  simp only [CollatzResearch.WordTrace]
  refine ⟨154541228342569277915503277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103027485561712851943668851 154541228342569277915503277)
  ·
    refine ⟨57952960628463479218313729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154541228342569277915503277 57952960628463479218313729)
    ·
      refine ⟨43464720471347609413735297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57952960628463479218313729 43464720471347609413735297)
      ·
        refine ⟨32598540353510707060301473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43464720471347609413735297 32598540353510707060301473)
        ·
          refine ⟨24448905265133030295226105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32598540353510707060301473 24448905265133030295226105)
          ·
            refine ⟨18336678948849772721419579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24448905265133030295226105 18336678948849772721419579)
            ·
              refine ⟨27505018423274659082129369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18336678948849772721419579 27505018423274659082129369)
              ·
                refine ⟨20628763817455994311597027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27505018423274659082129369 20628763817455994311597027)
                ·
                  refine ⟨30943145726183991467395541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20628763817455994311597027 30943145726183991467395541)
                  ·
                    refine ⟨725229977957437300017083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30943145726183991467395541 725229977957437300017083)
                    ·
                      rfl

theorem cell23_4237141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_4237141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237141 prefixEnd_4237141 := by exact prefixLift 4237141
  have htrace : WordTrace (prefixWord ++ tailWord_4237141) baseStart_4237141 baseEnd_4237141 := by
    simpa [prefixWord, tailWord_4237141, baseEnd_4237141] using wordTrace_append hprefix tailTrace_4237141
  have hstable : (prefixWord ++ tailWord_4237141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237141).length < 2 ^ (prefixWord ++ tailWord_4237141).sum := by decide
  have hdescent : baseEnd_4237141 < baseStart_4237141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237161 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 4]
def baseStart_4237161 : Nat := 118140960795 + 4237161 * 2 ^ 59
def prefixEnd_4237161 : Nat := 4983230072969 + 3 ^ 40 * 4237161 * 2
def baseEnd_4237161 : Nat := 2175700203485401821801157

theorem tailTrace_4237161 : CollatzResearch.WordTrace tailWord_4237161 prefixEnd_4237161 2175700203485401821801157 := by
  unfold tailWord_4237161
  simp only [CollatzResearch.WordTrace]
  refine ⟨154541957802496821331231337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103027971868331214220820891 154541957802496821331231337)
  ·
    refine ⟨115906468351872615998423503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154541957802496821331231337 115906468351872615998423503)
    ·
      refine ⟨173859702527808923997635255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115906468351872615998423503 173859702527808923997635255)
      ·
        refine ⟨260789553791713385996452883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173859702527808923997635255 260789553791713385996452883)
        ·
          refine ⟨391184330687570078994679325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260789553791713385996452883 391184330687570078994679325)
          ·
            refine ⟨146694124007838779623004747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 391184330687570078994679325 146694124007838779623004747)
            ·
              refine ⟨220041186011758169434507121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146694124007838779623004747 220041186011758169434507121)
              ·
                refine ⟨165030889508818627075880341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220041186011758169434507121 165030889508818627075880341)
                ·
                  refine ⟨7735822945725873144181891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 165030889508818627075880341 7735822945725873144181891)
                  ·
                    refine ⟨11603734418588809716272837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7735822945725873144181891 11603734418588809716272837)
                    ·
                      refine ⟨2175700203485401821801157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11603734418588809716272837 2175700203485401821801157)
                      ·
                        rfl

theorem cell23_4237161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_4237161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237161 prefixEnd_4237161 := by exact prefixLift 4237161
  have htrace : WordTrace (prefixWord ++ tailWord_4237161) baseStart_4237161 baseEnd_4237161 := by
    simpa [prefixWord, tailWord_4237161, baseEnd_4237161] using wordTrace_append hprefix tailTrace_4237161
  have hstable : (prefixWord ++ tailWord_4237161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237161).length < 2 ^ (prefixWord ++ tailWord_4237161).sum := by decide
  have hdescent : baseEnd_4237161 < baseStart_4237161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237178 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2]
def baseStart_4237178 : Nat := 118140960795 + 4237178 * 2 ^ 59
def prefixEnd_4237178 : Nat := 4983230072969 + 3 ^ 40 * 4237178 * 2
def baseEnd_4237178 : Nat := 2175708932656528255288579

theorem tailTrace_4237178 : CollatzResearch.WordTrace tailWord_4237178 prefixEnd_4237178 2175708932656528255288579 := by
  unfold tailWord_4237178
  simp only [CollatzResearch.WordTrace]
  refine ⟨38635644460858808308650047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103028385228956822156400125 38635644460858808308650047)
  ·
    refine ⟨57953466691288212462975071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38635644460858808308650047 57953466691288212462975071)
    ·
      refine ⟨86930200036932318694462607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57953466691288212462975071 86930200036932318694462607)
      ·
        refine ⟨130395300055398478041693911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86930200036932318694462607 130395300055398478041693911)
        ·
          refine ⟨195592950083097717062540867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130395300055398478041693911 195592950083097717062540867)
          ·
            refine ⟨293389425124646575593811301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195592950083097717062540867 293389425124646575593811301)
            ·
              refine ⟨55010517210871232923839619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 293389425124646575593811301 55010517210871232923839619)
              ·
                refine ⟨82515775816306849385759429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55010517210871232923839619 82515775816306849385759429)
                ·
                  refine ⟨15471707965557534259829893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82515775816306849385759429 15471707965557534259829893)
                  ·
                    refine ⟨2900945243542037673718105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15471707965557534259829893 2900945243542037673718105)
                    ·
                      refine ⟨2175708932656528255288579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2900945243542037673718105 2175708932656528255288579)
                      ·
                        rfl

theorem cell23_4237178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2].length) (baseStart_4237178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237178 prefixEnd_4237178 := by exact prefixLift 4237178
  have htrace : WordTrace (prefixWord ++ tailWord_4237178) baseStart_4237178 baseEnd_4237178 := by
    simpa [prefixWord, tailWord_4237178, baseEnd_4237178] using wordTrace_append hprefix tailTrace_4237178
  have hstable : (prefixWord ++ tailWord_4237178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237178).length < 2 ^ (prefixWord ++ tailWord_4237178).sum := by decide
  have hdescent : baseEnd_4237178 < baseStart_4237178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237185 : List Nat := [1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_4237185 : Nat := 118140960795 + 4237185 * 2 ^ 59
def prefixEnd_4237185 : Nat := 4983230072969 + 3 ^ 40 * 4237185 * 2
def baseEnd_4237185 : Nat := 2175712527021109727901047

theorem tailTrace_4237185 : CollatzResearch.WordTrace tailWord_4237185 prefixEnd_4237185 2175712527021109727901047 := by
  unfold tailWord_4237185
  simp only [CollatzResearch.WordTrace]
  refine ⟨154542833154409873430105009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103028555436273248953403339 154542833154409873430105009)
  ·
    refine ⟨115907124865807405072578757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154542833154409873430105009 115907124865807405072578757)
    ·
      refine ⟨21732585912338888451108517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115907124865807405072578757 21732585912338888451108517)
      ·
        refine ⟨4074859858563541584582847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21732585912338888451108517 4074859858563541584582847)
        ·
          refine ⟨6112289787845312376874271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4074859858563541584582847 6112289787845312376874271)
          ·
            refine ⟨9168434681767968565311407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6112289787845312376874271 9168434681767968565311407)
            ·
              refine ⟨13752652022651952847967111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9168434681767968565311407 13752652022651952847967111)
              ·
                refine ⟨20628978033977929271950667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13752652022651952847967111 20628978033977929271950667)
                ·
                  refine ⟨30943467050966893907926001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20628978033977929271950667 30943467050966893907926001)
                  ·
                    refine ⟨23207600288225170430944501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30943467050966893907926001 23207600288225170430944501)
                    ·
                      refine ⟨2175712527021109727901047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23207600288225170430944501 2175712527021109727901047)
                      ·
                        rfl

theorem cell23_4237185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_4237185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237185 prefixEnd_4237185 := by exact prefixLift 4237185
  have htrace : WordTrace (prefixWord ++ tailWord_4237185) baseStart_4237185 baseEnd_4237185 := by
    simpa [prefixWord, tailWord_4237185, baseEnd_4237185] using wordTrace_append hprefix tailTrace_4237185
  have hstable : (prefixWord ++ tailWord_4237185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237185).length < 2 ^ (prefixWord ++ tailWord_4237185).sum := by decide
  have hdescent : baseEnd_4237185 < baseStart_4237185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237251 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 4]
def baseStart_4237251 : Nat := 118140960795 + 4237251 * 2 ^ 59
def prefixEnd_4237251 : Nat := 4983230072969 + 3 ^ 40 * 4237251 * 2
def baseEnd_4237251 : Nat := 2175746416744306469675743

theorem tailTrace_4237251 : CollatzResearch.WordTrace tailWord_4237251 prefixEnd_4237251 2175746416744306469675743 := by
  unfold tailWord_4237251
  simp only [CollatzResearch.WordTrace]
  refine ⟨154545240372170766702007607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103030160248113844468005071 154545240372170766702007607)
  ·
    refine ⟨231817860558256150053011411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154545240372170766702007607 231817860558256150053011411)
    ·
      refine ⟨347726790837384225079517117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231817860558256150053011411 347726790837384225079517117)
      ·
        refine ⟨130397546564019084404818919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347726790837384225079517117 130397546564019084404818919)
        ·
          refine ⟨195596319846028626607228379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130397546564019084404818919 195596319846028626607228379)
          ·
            refine ⟨293394479769042939910842569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195596319846028626607228379 293394479769042939910842569)
            ·
              refine ⟨220045859826782204933131927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293394479769042939910842569 220045859826782204933131927)
              ·
                refine ⟨330068789740173307399697891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220045859826782204933131927 330068789740173307399697891)
                ·
                  refine ⟨495103184610259961099546837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 330068789740173307399697891 495103184610259961099546837)
                  ·
                    refine ⟨11603980889302967838270629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 495103184610259961099546837 11603980889302967838270629)
                    ·
                      refine ⟨2175746416744306469675743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11603980889302967838270629 2175746416744306469675743)
                      ·
                        rfl

theorem cell23_4237251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_4237251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237251 prefixEnd_4237251 := by exact prefixLift 4237251
  have htrace : WordTrace (prefixWord ++ tailWord_4237251) baseStart_4237251 baseEnd_4237251 := by
    simpa [prefixWord, tailWord_4237251, baseEnd_4237251] using wordTrace_append hprefix tailTrace_4237251
  have hstable : (prefixWord ++ tailWord_4237251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237251).length < 2 ^ (prefixWord ++ tailWord_4237251).sum := by decide
  have hdescent : baseEnd_4237251 < baseStart_4237251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237279 : List Nat := [1, 1, 2, 3, 4, 2, 2, 3, 1, 1, 3]
def baseStart_4237279 : Nat := 118140960795 + 4237279 * 2 ^ 59
def prefixEnd_4237279 : Nat := 4983230072969 + 3 ^ 40 * 4237279 * 2
def baseEnd_4237279 : Nat := 2175760794202632360125615

theorem tailTrace_4237279 : CollatzResearch.WordTrace tailWord_4237279 prefixEnd_4237279 2175760794202632360125615 := by
  unfold tailWord_4237279
  simp only [CollatzResearch.WordTrace]
  refine ⟨154546261616069327484026891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103030841077379551656017927 154546261616069327484026891)
  ·
    refine ⟨231819392424103991226040337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154546261616069327484026891 231819392424103991226040337)
    ·
      refine ⟨173864544318077993419530253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231819392424103991226040337 173864544318077993419530253)
      ·
        refine ⟨65199204119279247532323845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173864544318077993419530253 65199204119279247532323845)
        ·
          refine ⟨12224850772364858912310721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65199204119279247532323845 12224850772364858912310721)
          ·
            refine ⟨9168638079273644184233041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12224850772364858912310721 9168638079273644184233041)
            ·
              refine ⟨6876478559455233138174781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9168638079273644184233041 6876478559455233138174781)
              ·
                refine ⟨2578679459795712426815543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6876478559455233138174781 2578679459795712426815543)
                ·
                  refine ⟨3868019189693568640223315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2578679459795712426815543 3868019189693568640223315)
                  ·
                    refine ⟨5802028784540352960334973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3868019189693568640223315 5802028784540352960334973)
                    ·
                      refine ⟨2175760794202632360125615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5802028784540352960334973 2175760794202632360125615)
                      ·
                        rfl

theorem cell23_4237279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_4237279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237279 prefixEnd_4237279 := by exact prefixLift 4237279
  have htrace : WordTrace (prefixWord ++ tailWord_4237279) baseStart_4237279 baseEnd_4237279 := by
    simpa [prefixWord, tailWord_4237279, baseEnd_4237279] using wordTrace_append hprefix tailTrace_4237279
  have hstable : (prefixWord ++ tailWord_4237279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237279).length < 2 ^ (prefixWord ++ tailWord_4237279).sum := by decide
  have hdescent : baseEnd_4237279 < baseStart_4237279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237288 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_4237288 : Nat := 118140960795 + 4237288 * 2 ^ 59
def prefixEnd_4237288 : Nat := 4983230072969 + 3 ^ 40 * 4237288 * 2
def baseEnd_4237288 : Nat := 2175765415528522824913073

theorem tailTrace_4237288 : CollatzResearch.WordTrace tailWord_4237288 prefixEnd_4237288 2175765415528522824913073 := by
  unfold tailWord_4237288
  simp only [CollatzResearch.WordTrace]
  refine ⟨77273294936518361010552259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103031059915357814680736345 77273294936518361010552259)
  ·
    refine ⟨115909942404777541515828389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77273294936518361010552259 115909942404777541515828389)
    ·
      refine ⟨21733114200895789034217823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115909942404777541515828389 21733114200895789034217823)
      ·
        refine ⟨32599671301343683551326735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21733114200895789034217823 32599671301343683551326735)
        ·
          refine ⟨48899506952015525326990103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32599671301343683551326735 48899506952015525326990103)
          ·
            refine ⟨73349260428023287990485155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48899506952015525326990103 73349260428023287990485155)
            ·
              refine ⟨110023890642034931985727733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73349260428023287990485155 110023890642034931985727733)
              ·
                refine ⟨10314739747690774873661975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 110023890642034931985727733 10314739747690774873661975)
                ·
                  refine ⟨15472109621536162310492963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10314739747690774873661975 15472109621536162310492963)
                  ·
                    refine ⟨23208164432304243465739445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15472109621536162310492963 23208164432304243465739445)
                    ·
                      refine ⟨2175765415528522824913073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23208164432304243465739445 2175765415528522824913073)
                      ·
                        rfl

theorem cell23_4237288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_4237288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237288 prefixEnd_4237288 := by exact prefixLift 4237288
  have htrace : WordTrace (prefixWord ++ tailWord_4237288) baseStart_4237288 baseEnd_4237288 := by
    simpa [prefixWord, tailWord_4237288, baseEnd_4237288] using wordTrace_append hprefix tailTrace_4237288
  have hstable : (prefixWord ++ tailWord_4237288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237288).length < 2 ^ (prefixWord ++ tailWord_4237288).sum := by decide
  have hdescent : baseEnd_4237288 < baseStart_4237288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237369 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 2, 1, 3]
def baseStart_4237369 : Nat := 118140960795 + 4237369 * 2 ^ 59
def prefixEnd_4237369 : Nat := 4983230072969 + 3 ^ 40 * 4237369 * 2
def baseEnd_4237369 : Nat := 2175807007461537008000201

theorem tailTrace_4237369 : CollatzResearch.WordTrace tailWord_4237369 prefixEnd_4237369 2175807007461537008000201 := by
  unfold tailWord_4237369
  simp only [CollatzResearch.WordTrace]
  refine ⟨154549544185743272854803161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103033029457162181903202107 154549544185743272854803161)
  ·
    refine ⟨115912158139307454641102371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154549544185743272854803161 115912158139307454641102371)
    ·
      refine ⟨173868237208961181961653557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115912158139307454641102371 173868237208961181961653557)
      ·
        refine ⟨16300147238340110808905021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 173868237208961181961653557 16300147238340110808905021)
        ·
          refine ⟨6112555214377541553339383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16300147238340110808905021 6112555214377541553339383)
          ·
            refine ⟨9168832821566312330009075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6112555214377541553339383 9168832821566312330009075)
            ·
              refine ⟨13753249232349468495013613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9168832821566312330009075 13753249232349468495013613)
              ·
                refine ⟨5157468462131050685630105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13753249232349468495013613 5157468462131050685630105)
                ·
                  refine ⟨3868101346598288014222579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5157468462131050685630105 3868101346598288014222579)
                  ·
                    refine ⟨5802152019897432021333869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3868101346598288014222579 5802152019897432021333869)
                    ·
                      refine ⟨2175807007461537008000201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5802152019897432021333869 2175807007461537008000201)
                      ·
                        rfl

theorem cell23_4237369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_4237369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237369 prefixEnd_4237369 := by exact prefixLift 4237369
  have htrace : WordTrace (prefixWord ++ tailWord_4237369) baseStart_4237369 baseEnd_4237369 := by
    simpa [prefixWord, tailWord_4237369, baseEnd_4237369] using wordTrace_append hprefix tailTrace_4237369
  have hstable : (prefixWord ++ tailWord_4237369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237369).length < 2 ^ (prefixWord ++ tailWord_4237369).sum := by decide
  have hdescent : baseEnd_4237369 < baseStart_4237369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237425 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 2, 3, 3]
def baseStart_4237425 : Nat := 118140960795 + 4237425 * 2 ^ 59
def prefixEnd_4237425 : Nat := 4983230072969 + 3 ^ 40 * 4237425 * 2
def baseEnd_4237425 : Nat := 2175835762378188788899943

theorem tailTrace_4237425 : CollatzResearch.WordTrace tailWord_4237425 prefixEnd_4237425 2175835762378188788899943 := by
  unfold tailWord_4237425
  simp only [CollatzResearch.WordTrace]
  refine ⟨154551586673540394418841729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103034391115693596279227819 154551586673540394418841729)
  ·
    refine ⟨115913690005155295814131297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154551586673540394418841729 115913690005155295814131297)
    ·
      refine ⟨86935267503866471860598473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115913690005155295814131297 86935267503866471860598473)
      ·
        refine ⟨65201450627899853895448855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86935267503866471860598473 65201450627899853895448855)
        ·
          refine ⟨97802175941849780843173283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65201450627899853895448855 97802175941849780843173283)
          ·
            refine ⟨146703263912774671264759925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97802175941849780843173283 146703263912774671264759925)
            ·
              refine ⟨13753430991822625431071243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 146703263912774671264759925 13753430991822625431071243)
              ·
                refine ⟨20630146487733938146606865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13753430991822625431071243 20630146487733938146606865)
                ·
                  refine ⟨15472609865800453609955149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20630146487733938146606865 15472609865800453609955149)
                  ·
                    refine ⟨5802228699675170103733181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15472609865800453609955149 5802228699675170103733181)
                    ·
                      refine ⟨2175835762378188788899943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5802228699675170103733181 2175835762378188788899943)
                      ·
                        rfl

theorem cell23_4237425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_4237425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237425 prefixEnd_4237425 := by exact prefixLift 4237425
  have htrace : WordTrace (prefixWord ++ tailWord_4237425) baseStart_4237425 baseEnd_4237425 := by
    simpa [prefixWord, tailWord_4237425, baseEnd_4237425] using wordTrace_append hprefix tailTrace_4237425
  have hstable : (prefixWord ++ tailWord_4237425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237425).length < 2 ^ (prefixWord ++ tailWord_4237425).sum := by decide
  have hdescent : baseEnd_4237425 < baseStart_4237425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237445 : List Nat := [1, 3, 1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_4237445 : Nat := 118140960795 + 4237445 * 2 ^ 59
def prefixEnd_4237445 : Nat := 4983230072969 + 3 ^ 40 * 4237445 * 2
def baseEnd_4237445 : Nat := 725282010663759570216617

theorem tailTrace_4237445 : CollatzResearch.WordTrace tailWord_4237445 prefixEnd_4237445 725282010663759570216617 := by
  unfold tailWord_4237445
  simp only [CollatzResearch.WordTrace]
  refine ⟨154552316133467937834569789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103034877422311958556379859 154552316133467937834569789)
  ·
    refine ⟨57957118550050476687963671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154552316133467937834569789 57957118550050476687963671)
    ·
      refine ⟨86935677825075715031945507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57957118550050476687963671 86935677825075715031945507)
      ·
        refine ⟨130403516737613572547918261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86935677825075715031945507 130403516737613572547918261)
        ·
          refine ⟨12225329694151272426367337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 130403516737613572547918261 12225329694151272426367337)
          ·
            refine ⟨9168997270613454319775503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12225329694151272426367337 9168997270613454319775503)
            ·
              refine ⟨13753495905920181479663255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9168997270613454319775503 13753495905920181479663255)
              ·
                refine ⟨20630243858880272219494883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13753495905920181479663255 20630243858880272219494883)
                ·
                  refine ⟨30945365788320408329242325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20630243858880272219494883 30945365788320408329242325)
                  ·
                    refine ⟨725282010663759570216617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30945365788320408329242325 725282010663759570216617)
                    ·
                      rfl

theorem cell23_4237445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_4237445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237445 prefixEnd_4237445 := by exact prefixLift 4237445
  have htrace : WordTrace (prefixWord ++ tailWord_4237445) baseStart_4237445 baseEnd_4237445 := by
    simpa [prefixWord, tailWord_4237445, baseEnd_4237445] using wordTrace_append hprefix tailTrace_4237445
  have hstable : (prefixWord ++ tailWord_4237445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237445).length < 2 ^ (prefixWord ++ tailWord_4237445).sum := by decide
  have hdescent : baseEnd_4237445 < baseStart_4237445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237460 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_4237460 : Nat := 118140960795 + 4237460 * 2 ^ 59
def prefixEnd_4237460 : Nat := 4983230072969 + 3 ^ 40 * 4237460 * 2
def baseEnd_4237460 : Nat := 2175853734201096151962283

theorem tailTrace_4237460 : CollatzResearch.WordTrace tailWord_4237460 prefixEnd_4237460 2175853734201096151962283 := by
  unfold tailWord_4237460
  simp only [CollatzResearch.WordTrace]
  refine ⟨77276431614206797698182917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103035242152275730264243889 77276431614206797698182917)
  ·
    refine ⟨14489330927663774568409297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 77276431614206797698182917 14489330927663774568409297)
    ·
      refine ⟨10866998195747830926306973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14489330927663774568409297 10866998195747830926306973)
      ·
        refine ⟨4075124323405436597365115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10866998195747830926306973 4075124323405436597365115)
        ·
          refine ⟨6112686485108154896047673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075124323405436597365115 6112686485108154896047673)
          ·
            refine ⟨4584514863831116172035755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6112686485108154896047673 4584514863831116172035755)
            ·
              refine ⟨6876772295746674258053633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4584514863831116172035755 6876772295746674258053633)
              ·
                refine ⟨5157579221810005693540225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6876772295746674258053633 5157579221810005693540225)
                ·
                  refine ⟨3868184416357504270155169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5157579221810005693540225 3868184416357504270155169)
                  ·
                    refine ⟨2901138312268128202616377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3868184416357504270155169 2901138312268128202616377)
                    ·
                      refine ⟨2175853734201096151962283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2901138312268128202616377 2175853734201096151962283)
                      ·
                        rfl

theorem cell23_4237460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_4237460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237460 prefixEnd_4237460 := by exact prefixLift 4237460
  have htrace : WordTrace (prefixWord ++ tailWord_4237460) baseStart_4237460 baseEnd_4237460 := by
    simpa [prefixWord, tailWord_4237460, baseEnd_4237460] using wordTrace_append hprefix tailTrace_4237460
  have hstable : (prefixWord ++ tailWord_4237460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237460).length < 2 ^ (prefixWord ++ tailWord_4237460).sum := by decide
  have hdescent : baseEnd_4237460 < baseStart_4237460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237465 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 4]
def baseStart_4237465 : Nat := 118140960795 + 4237465 * 2 ^ 59
def prefixEnd_4237465 : Nat := 4983230072969 + 3 ^ 40 * 4237465 * 2
def baseEnd_4237465 : Nat := 2175856301604368632399759

theorem tailTrace_4237465 : CollatzResearch.WordTrace tailWord_4237465 prefixEnd_4237465 2175856301604368632399759 := by
  unfold tailWord_4237465
  simp only [CollatzResearch.WordTrace]
  refine ⟨154553045593395481250297849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103035363728930320833531899 154553045593395481250297849)
  ·
    refine ⟨115914784195046610937723387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154553045593395481250297849 115914784195046610937723387)
    ·
      refine ⟨173872176292569916406585081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115914784195046610937723387 173872176292569916406585081)
      ·
        refine ⟨130404132219427437304938811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173872176292569916406585081 130404132219427437304938811)
        ·
          refine ⟨195606198329141155957408217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130404132219427437304938811 195606198329141155957408217)
          ·
            refine ⟨146704648746855866968056163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195606198329141155957408217 146704648746855866968056163)
            ·
              refine ⟨220056973120283800452084245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146704648746855866968056163 220056973120283800452084245)
              ·
                refine ⟨10315170615013303146191449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 220056973120283800452084245 10315170615013303146191449)
                ·
                  refine ⟨7736377961259977359643587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10315170615013303146191449 7736377961259977359643587)
                  ·
                    refine ⟨11604566941889966039465381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7736377961259977359643587 11604566941889966039465381)
                    ·
                      refine ⟨2175856301604368632399759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11604566941889966039465381 2175856301604368632399759)
                      ·
                        rfl

theorem cell23_4237465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_4237465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237465 prefixEnd_4237465 := by exact prefixLift 4237465
  have htrace : WordTrace (prefixWord ++ tailWord_4237465) baseStart_4237465 baseEnd_4237465 := by
    simpa [prefixWord, tailWord_4237465, baseEnd_4237465] using wordTrace_append hprefix tailTrace_4237465
  have hstable : (prefixWord ++ tailWord_4237465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237465).length < 2 ^ (prefixWord ++ tailWord_4237465).sum := by decide
  have hdescent : baseEnd_4237465 < baseStart_4237465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237488 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 12]
def baseStart_4237488 : Nat := 118140960795 + 4237488 * 2 ^ 59
def prefixEnd_4237488 : Nat := 4983230072969 + 3 ^ 40 * 4237488 * 2
def baseEnd_4237488 : Nat := 241763123517713560268017

theorem tailTrace_4237488 : CollatzResearch.WordTrace tailWord_4237488 prefixEnd_4237488 241763123517713560268017 := by
  unfold tailWord_4237488
  simp only [CollatzResearch.WordTrace]
  refine ⟨77276942236156078089192559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103035922981541437452256745 77276942236156078089192559)
  ·
    refine ⟨115915413354234117133788839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77276942236156078089192559 115915413354234117133788839)
    ·
      refine ⟨173873120031351175700683259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115915413354234117133788839 173873120031351175700683259)
      ·
        refine ⟨260809680047026763551024889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173873120031351175700683259 260809680047026763551024889)
        ·
          refine ⟨195607260035270072663268667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260809680047026763551024889 195607260035270072663268667)
          ·
            refine ⟨293410890052905108994903001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195607260035270072663268667 293410890052905108994903001)
            ·
              refine ⟨220058167539678831746177251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293410890052905108994903001 220058167539678831746177251)
              ·
                refine ⟨330087251309518247619265877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220058167539678831746177251 330087251309518247619265877)
                ·
                  refine ⟨241763123517713560268017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 330087251309518247619265877 241763123517713560268017)
                  ·
                    rfl

theorem cell23_4237488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 12].length) (baseStart_4237488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237488 prefixEnd_4237488 := by exact prefixLift 4237488
  have htrace : WordTrace (prefixWord ++ tailWord_4237488) baseStart_4237488 baseEnd_4237488 := by
    simpa [prefixWord, tailWord_4237488, baseEnd_4237488] using wordTrace_append hprefix tailTrace_4237488
  have hstable : (prefixWord ++ tailWord_4237488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237488).length < 2 ^ (prefixWord ++ tailWord_4237488).sum := by decide
  have hdescent : baseEnd_4237488 < baseStart_4237488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237509 : List Nat := [1, 3, 1, 1, 1, 1, 7, 3, 1, 4]
def baseStart_4237509 : Nat := 118140960795 + 4237509 * 2 ^ 59
def prefixEnd_4237509 : Nat := 4983230072969 + 3 ^ 40 * 4237509 * 2
def baseEnd_4237509 : Nat := 725292964917722153416519

theorem tailTrace_4237509 : CollatzResearch.WordTrace tailWord_4237509 prefixEnd_4237509 725292964917722153416519 := by
  unfold tailWord_4237509
  simp only [CollatzResearch.WordTrace]
  refine ⟨154554650405236076764899581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103036433603490717843266387 154554650405236076764899581)
  ·
    refine ⟨57957993901963528786837343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154554650405236076764899581 57957993901963528786837343)
    ·
      refine ⟨86936990852945293180256015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57957993901963528786837343 86936990852945293180256015)
      ·
        refine ⟨130405486279417939770384023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86936990852945293180256015 130405486279417939770384023)
        ·
          refine ⟨195608229419126909655576035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130405486279417939770384023 195608229419126909655576035)
          ·
            refine ⟨293412344128690364483364053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195608229419126909655576035 293412344128690364483364053)
            ·
              refine ⟨6876851815516180417578845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 293412344128690364483364053 6876851815516180417578845)
              ·
                refine ⟨2578819430818567656592067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6876851815516180417578845 2578819430818567656592067)
                ·
                  refine ⟨3868229146227851484888101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2578819430818567656592067 3868229146227851484888101)
                  ·
                    refine ⟨725292964917722153416519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3868229146227851484888101 725292964917722153416519)
                    ·
                      rfl

theorem cell23_4237509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_4237509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237509 prefixEnd_4237509 := by exact prefixLift 4237509
  have htrace : WordTrace (prefixWord ++ tailWord_4237509) baseStart_4237509 baseEnd_4237509 := by
    simpa [prefixWord, tailWord_4237509, baseEnd_4237509] using wordTrace_append hprefix tailTrace_4237509
  have hstable : (prefixWord ++ tailWord_4237509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237509).length < 2 ^ (prefixWord ++ tailWord_4237509).sum := by decide
  have hdescent : baseEnd_4237509 < baseStart_4237509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237526 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 3, 4]
def baseStart_4237526 : Nat := 118140960795 + 4237526 * 2 ^ 59
def prefixEnd_4237526 : Nat := 4983230072969 + 3 ^ 40 * 4237526 * 2
def baseEnd_4237526 : Nat := 725295874641430964578993

theorem tailTrace_4237526 : CollatzResearch.WordTrace tailWord_4237526 prefixEnd_4237526 725295874641430964578993 := by
  unfold tailWord_4237526
  simp only [CollatzResearch.WordTrace]
  refine ⟨9659704402885905541766777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103036846964116325778845621 9659704402885905541766777)
  ·
    refine ⟨7244778302164429156325083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9659704402885905541766777 7244778302164429156325083)
    ·
      refine ⟨10867167453246643734487625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7244778302164429156325083 10867167453246643734487625)
      ·
        refine ⟨8150375589934982800865719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10867167453246643734487625 8150375589934982800865719)
        ·
          refine ⟨12225563384902474201298579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8150375589934982800865719 12225563384902474201298579)
          ·
            refine ⟨18338345077353711301947869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12225563384902474201298579 18338345077353711301947869)
            ·
              refine ⟨6876879404007641738230451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18338345077353711301947869 6876879404007641738230451)
              ·
                refine ⟨10315319106011462607345677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6876879404007641738230451 10315319106011462607345677)
                ·
                  refine ⟨3868244664754298477754629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10315319106011462607345677 3868244664754298477754629)
                  ·
                    refine ⟨725295874641430964578993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3868244664754298477754629 725295874641430964578993)
                    ·
                      rfl

theorem cell23_4237526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_4237526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237526 prefixEnd_4237526 := by exact prefixLift 4237526
  have htrace : WordTrace (prefixWord ++ tailWord_4237526) baseStart_4237526 baseEnd_4237526 := by
    simpa [prefixWord, tailWord_4237526, baseEnd_4237526] using wordTrace_append hprefix tailTrace_4237526
  have hstable : (prefixWord ++ tailWord_4237526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237526).length < 2 ^ (prefixWord ++ tailWord_4237526).sum := by decide
  have hdescent : baseEnd_4237526 < baseStart_4237526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237535 : List Nat := [1, 1, 2, 3, 2, 1, 1, 4, 3, 5]
def baseStart_4237535 : Nat := 118140960795 + 4237535 * 2 ^ 59
def prefixEnd_4237535 : Nat := 4983230072969 + 3 ^ 40 * 4237535 * 2
def baseEnd_4237535 : Nat := 725297415083394452841479

theorem tailTrace_4237535 : CollatzResearch.WordTrace tailWord_4237535 prefixEnd_4237535 725297415083394452841479 := by
  unfold tailWord_4237535
  simp only [CollatzResearch.WordTrace]
  refine ⟨154555598703141883205346059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103037065802094588803564039 154555598703141883205346059)
  ·
    refine ⟨231833398054712824808019089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154555598703141883205346059 231833398054712824808019089)
    ·
      refine ⟨173875048541034618606014317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231833398054712824808019089 173875048541034618606014317)
      ·
        refine ⟨65203143202887981977255369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173875048541034618606014317 65203143202887981977255369)
        ·
          refine ⟨48902357402165986482941527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65203143202887981977255369 48902357402165986482941527)
          ·
            refine ⟨73353536103248979724412291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48902357402165986482941527 73353536103248979724412291)
            ·
              refine ⟨110030304154873469586618437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73353536103248979724412291 110030304154873469586618437)
              ·
                refine ⟨20630682029038775547490957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110030304154873469586618437 20630682029038775547490957)
                ·
                  refine ⟨7736505760889540830309109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20630682029038775547490957 7736505760889540830309109)
                  ·
                    refine ⟨725297415083394452841479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7736505760889540830309109 725297415083394452841479)
                    ·
                      rfl

theorem cell23_4237535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 5].length) (baseStart_4237535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237535 prefixEnd_4237535 := by exact prefixLift 4237535
  have htrace : WordTrace (prefixWord ++ tailWord_4237535) baseStart_4237535 baseEnd_4237535 := by
    simpa [prefixWord, tailWord_4237535, baseEnd_4237535] using wordTrace_append hprefix tailTrace_4237535
  have hstable : (prefixWord ++ tailWord_4237535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237535).length < 2 ^ (prefixWord ++ tailWord_4237535).sum := by decide
  have hdescent : baseEnd_4237535 < baseStart_4237535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237539 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 6]
def baseStart_4237539 : Nat := 118140960795 + 4237539 * 2 ^ 59
def prefixEnd_4237539 : Nat := 4983230072969 + 3 ^ 40 * 4237539 * 2
def baseEnd_4237539 : Nat := 241766033241422371430491

theorem tailTrace_4237539 : CollatzResearch.WordTrace tailWord_4237539 prefixEnd_4237539 241766033241422371430491 := by
  unfold tailWord_4237539
  simp only [CollatzResearch.WordTrace]
  refine ⟨154555744595127391888491671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103037163063418261258994447 154555744595127391888491671)
  ·
    refine ⟨231833616892691087832737507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154555744595127391888491671 231833616892691087832737507)
    ·
      refine ⟨347750425339036631749106261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231833616892691087832737507 347750425339036631749106261)
      ·
        refine ⟨4075200296941835528309839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 347750425339036631749106261 4075200296941835528309839)
        ·
          refine ⟨6112800445412753292464759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075200296941835528309839 6112800445412753292464759)
          ·
            refine ⟨9169200668119129938697139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6112800445412753292464759 9169200668119129938697139)
            ·
              refine ⟨13753801002178694908045709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9169200668119129938697139 13753801002178694908045709)
              ·
                refine ⟨5157675375817010590517141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13753801002178694908045709 5157675375817010590517141)
                ·
                  refine ⟨241766033241422371430491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5157675375817010590517141 241766033241422371430491)
                  ·
                    rfl

theorem cell23_4237539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 6].length) (baseStart_4237539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237539 prefixEnd_4237539 := by exact prefixLift 4237539
  have htrace : WordTrace (prefixWord ++ tailWord_4237539) baseStart_4237539 baseEnd_4237539 := by
    simpa [prefixWord, tailWord_4237539, baseEnd_4237539] using wordTrace_append hprefix tailTrace_4237539
  have hstable : (prefixWord ++ tailWord_4237539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237539).length < 2 ^ (prefixWord ++ tailWord_4237539).sum := by decide
  have hdescent : baseEnd_4237539 < baseStart_4237539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237569 : List Nat := [1, 2, 4, 1, 1, 2, 5, 1, 1, 5]
def baseStart_4237569 : Nat := 118140960795 + 4237569 * 2 ^ 59
def prefixEnd_4237569 : Nat := 4983230072969 + 3 ^ 40 * 4237569 * 2
def baseEnd_4237569 : Nat := 725303234530812075166427

theorem tailTrace_4237569 : CollatzResearch.WordTrace tailWord_4237569 prefixEnd_4237569 725303234530812075166427 := by
  unfold tailWord_4237569
  simp only [CollatzResearch.WordTrace]
  refine ⟨154556838785018707012083761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103037892523345804674722507 154556838785018707012083761)
  ·
    refine ⟨115917629088764030259062821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154556838785018707012083761 115917629088764030259062821)
    ·
      refine ⟨21734555454143255673574279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115917629088764030259062821 21734555454143255673574279)
      ·
        refine ⟨32601833181214883510361419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21734555454143255673574279 32601833181214883510361419)
        ·
          refine ⟨48902749771822325265542129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32601833181214883510361419 48902749771822325265542129)
          ·
            refine ⟨36677062328866743949156597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48902749771822325265542129 36677062328866743949156597)
            ·
              refine ⟨3438474593331257245233431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36677062328866743949156597 3438474593331257245233431)
              ·
                refine ⟨5157711889996885867850147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3438474593331257245233431 5157711889996885867850147)
                ·
                  refine ⟨7736567834995328801775221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5157711889996885867850147 7736567834995328801775221)
                  ·
                    refine ⟨725303234530812075166427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7736567834995328801775221 725303234530812075166427)
                    ·
                      rfl

theorem cell23_4237569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_4237569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237569 prefixEnd_4237569 := by exact prefixLift 4237569
  have htrace : WordTrace (prefixWord ++ tailWord_4237569) baseStart_4237569 baseEnd_4237569 := by
    simpa [prefixWord, tailWord_4237569, baseEnd_4237569] using wordTrace_append hprefix tailTrace_4237569
  have hstable : (prefixWord ++ tailWord_4237569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237569).length < 2 ^ (prefixWord ++ tailWord_4237569).sum := by decide
  have hdescent : baseEnd_4237569 < baseStart_4237569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237592 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 5, 2, 3]
def baseStart_4237592 : Nat := 118140960795 + 4237592 * 2 ^ 59
def prefixEnd_4237592 : Nat := 4983230072969 + 3 ^ 40 * 4237592 * 2
def baseEnd_4237592 : Nat := 2175921513647489635511675

theorem tailTrace_4237592 : CollatzResearch.WordTrace tailWord_4237592 prefixEnd_4237592 2175921513647489635511675 := by
  unfold tailWord_4237592
  simp only [CollatzResearch.WordTrace]
  refine ⟨77278838831967690970085515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103038451775956921293447353 77278838831967690970085515)
  ·
    refine ⟨115918258247951536455128273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77278838831967690970085515 115918258247951536455128273)
    ·
      refine ⟨86938693685963652341346205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115918258247951536455128273 86938693685963652341346205)
      ·
        refine ⟨32602010132236369628004827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86938693685963652341346205 32602010132236369628004827)
        ·
          refine ⟨48903015198354554442007241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32602010132236369628004827 48903015198354554442007241)
          ·
            refine ⟨36677261398765915831505431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48903015198354554442007241 36677261398765915831505431)
            ·
              refine ⟨55015892098148873747258147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36677261398765915831505431 55015892098148873747258147)
              ·
                refine ⟨82523838147223310620887221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55015892098148873747258147 82523838147223310620887221)
                ·
                  refine ⟨7736609826302185370708177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82523838147223310620887221 7736609826302185370708177)
                  ·
                    refine ⟨5802457369726639028031133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7736609826302185370708177 5802457369726639028031133)
                    ·
                      refine ⟨2175921513647489635511675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5802457369726639028031133 2175921513647489635511675)
                      ·
                        rfl

theorem cell23_4237592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_4237592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237592 prefixEnd_4237592 := by exact prefixLift 4237592
  have htrace : WordTrace (prefixWord ++ tailWord_4237592) baseStart_4237592 baseEnd_4237592 := by
    simpa [prefixWord, tailWord_4237592, baseEnd_4237592] using wordTrace_append hprefix tailTrace_4237592
  have hstable : (prefixWord ++ tailWord_4237592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237592).length < 2 ^ (prefixWord ++ tailWord_4237592).sum := by decide
  have hdescent : baseEnd_4237592 < baseStart_4237592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237595 : List Nat := [1, 1, 1, 1, 1, 1, 9, 8]
def baseStart_4237595 : Nat := 118140960795 + 4237595 * 2 ^ 59
def prefixEnd_4237595 : Nat := 4983230072969 + 3 ^ 40 * 4237595 * 2
def baseEnd_4237595 : Nat := 80589742744053819399043

theorem tailTrace_4237595 : CollatzResearch.WordTrace tailWord_4237595 prefixEnd_4237595 80589742744053819399043 := by
  unfold tailWord_4237595
  simp only [CollatzResearch.WordTrace]
  refine ⟨154557787082924513452530239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103038524721949675635020159 154557787082924513452530239)
  ·
    refine ⟨231836680624386770178795359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154557787082924513452530239 231836680624386770178795359)
    ·
      refine ⟨347755020936580155268193039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231836680624386770178795359 347755020936580155268193039)
      ·
        refine ⟨521632531404870232902289559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347755020936580155268193039 521632531404870232902289559)
        ·
          refine ⟨782448797107305349353434339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521632531404870232902289559 782448797107305349353434339)
          ·
            refine ⟨1173673195660958024030151509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782448797107305349353434339 1173673195660958024030151509)
            ·
              refine ⟨6876991380825925922051669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1173673195660958024030151509 6876991380825925922051669)
              ·
                refine ⟨80589742744053819399043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6876991380825925922051669 80589742744053819399043)
                ·
                  rfl

theorem cell23_4237595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 8].length) (baseStart_4237595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237595 prefixEnd_4237595 := by exact prefixLift 4237595
  have htrace : WordTrace (prefixWord ++ tailWord_4237595) baseStart_4237595 baseEnd_4237595 := by
    simpa [prefixWord, tailWord_4237595, baseEnd_4237595] using wordTrace_append hprefix tailTrace_4237595
  have hstable : (prefixWord ++ tailWord_4237595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237595).length < 2 ^ (prefixWord ++ tailWord_4237595).sum := by decide
  have hdescent : baseEnd_4237595 < baseStart_4237595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237599 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 2, 4]
def baseStart_4237599 : Nat := 118140960795 + 4237599 * 2 ^ 59
def prefixEnd_4237599 : Nat := 4983230072969 + 3 ^ 40 * 4237599 * 2
def baseEnd_4237599 : Nat := 725308369337357036041381

theorem tailTrace_4237599 : CollatzResearch.WordTrace tailWord_4237599 prefixEnd_4237599 725308369337357036041381 := by
  unfold tailWord_4237599
  simp only [CollatzResearch.WordTrace]
  refine ⟨154557932974910022135675851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103038621983273348090450567 154557932974910022135675851)
  ·
    refine ⟨231836899462365033203513777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154557932974910022135675851 231836899462365033203513777)
    ·
      refine ⟨173877674596773774902635333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231836899462365033203513777 173877674596773774902635333)
      ·
        refine ⟨32602063986895082794244125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173877674596773774902635333 32602063986895082794244125)
        ·
          refine ⟨12225773995085656047841547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32602063986895082794244125 12225773995085656047841547)
          ·
            refine ⟨18338660992628484071762321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12225773995085656047841547 18338660992628484071762321)
            ·
              refine ⟨13753995744471363053821741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18338660992628484071762321 13753995744471363053821741)
              ·
                refine ⟨5157748404176761145183153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13753995744471363053821741 5157748404176761145183153)
                ·
                  refine ⟨3868311303132570858887365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5157748404176761145183153 3868311303132570858887365)
                  ·
                    refine ⟨725308369337357036041381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3868311303132570858887365 725308369337357036041381)
                    ·
                      rfl

theorem cell23_4237599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 4].length) (baseStart_4237599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237599 prefixEnd_4237599 := by exact prefixLift 4237599
  have htrace : WordTrace (prefixWord ++ tailWord_4237599) baseStart_4237599 baseEnd_4237599 := by
    simpa [prefixWord, tailWord_4237599, baseEnd_4237599] using wordTrace_append hprefix tailTrace_4237599
  have hstable : (prefixWord ++ tailWord_4237599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237599).length < 2 ^ (prefixWord ++ tailWord_4237599).sum := by decide
  have hdescent : baseEnd_4237599 < baseStart_4237599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237610 : List Nat := [3, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_4237610 : Nat := 118140960795 + 4237610 * 2 ^ 59
def prefixEnd_4237610 : Nat := 4983230072969 + 3 ^ 40 * 4237610 * 2
def baseEnd_4237610 : Nat := 2175930756299270565086593

theorem tailTrace_4237610 : CollatzResearch.WordTrace tailWord_4237610 prefixEnd_4237610 2175930756299270565086593 := by
  unfold tailWord_4237610
  simp only [CollatzResearch.WordTrace]
  refine ⟨38639583544467542753581571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103038889451913447342884189 38639583544467542753581571)
  ·
    refine ⟨57959375316701314130372357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38639583544467542753581571 57959375316701314130372357)
    ·
      refine ⟨10867382871881496399444817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57959375316701314130372357 10867382871881496399444817)
      ·
        refine ⟨8150537153911122299583613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10867382871881496399444817 8150537153911122299583613)
        ·
          refine ⟨3056451432716670862343855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8150537153911122299583613 3056451432716670862343855)
          ·
            refine ⟨4584677149075006293515783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3056451432716670862343855 4584677149075006293515783)
            ·
              refine ⟨6877015723612509440273675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4584677149075006293515783 6877015723612509440273675)
              ·
                refine ⟨10315523585418764160410513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6877015723612509440273675 10315523585418764160410513)
                ·
                  refine ⟨7736642689064073120307885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10315523585418764160410513 7736642689064073120307885)
                  ·
                    refine ⟨2901241008399027420115457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7736642689064073120307885 2901241008399027420115457)
                    ·
                      refine ⟨2175930756299270565086593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2901241008399027420115457 2175930756299270565086593)
                      ·
                        rfl

theorem cell23_4237610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_4237610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237610 prefixEnd_4237610 := by exact prefixLift 4237610
  have htrace : WordTrace (prefixWord ++ tailWord_4237610) baseStart_4237610 baseEnd_4237610 := by
    simpa [prefixWord, tailWord_4237610, baseEnd_4237610] using wordTrace_append hprefix tailTrace_4237610
  have hstable : (prefixWord ++ tailWord_4237610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237610).length < 2 ^ (prefixWord ++ tailWord_4237610).sum := by decide
  have hdescent : baseEnd_4237610 < baseStart_4237610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237626 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3]
def baseStart_4237626 : Nat := 118140960795 + 4237626 * 2 ^ 59
def prefixEnd_4237626 : Nat := 4983230072969 + 3 ^ 40 * 4237626 * 2
def baseEnd_4237626 : Nat := 2175938971989742502486519

theorem tailTrace_4237626 : CollatzResearch.WordTrace tailWord_4237626 prefixEnd_4237626 2175938971989742502486519 := by
  unfold tailWord_4237626
  simp only [CollatzResearch.WordTrace]
  refine ⟨38639729436453051436727183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103039278497208137164605821 38639729436453051436727183)
  ·
    refine ⟨57959594154679577155090775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38639729436453051436727183 57959594154679577155090775)
    ·
      refine ⟨86939391232019365732636163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57959594154679577155090775 86939391232019365732636163)
      ·
        refine ⟨130409086848029048598954245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86939391232019365732636163 130409086848029048598954245)
        ·
          refine ⟨24451703784005446612303921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 130409086848029048598954245 24451703784005446612303921)
          ·
            refine ⟨18338777838004084959227941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24451703784005446612303921 18338777838004084959227941)
            ·
              refine ⟨3438520844625765929855239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18338777838004084959227941 3438520844625765929855239)
              ·
                refine ⟨5157781266938648894782859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3438520844625765929855239 5157781266938648894782859)
                ·
                  refine ⟨7736671900407973342174289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5157781266938648894782859 7736671900407973342174289)
                  ·
                    refine ⟨5802503925305980006630717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7736671900407973342174289 5802503925305980006630717)
                    ·
                      refine ⟨2175938971989742502486519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5802503925305980006630717 2175938971989742502486519)
                      ·
                        rfl

theorem cell23_4237626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3].length) (baseStart_4237626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237626 prefixEnd_4237626 := by exact prefixLift 4237626
  have htrace : WordTrace (prefixWord ++ tailWord_4237626) baseStart_4237626 baseEnd_4237626 := by
    simpa [prefixWord, tailWord_4237626, baseEnd_4237626] using wordTrace_append hprefix tailTrace_4237626
  have hstable : (prefixWord ++ tailWord_4237626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237626).length < 2 ^ (prefixWord ++ tailWord_4237626).sum := by decide
  have hdescent : baseEnd_4237626 < baseStart_4237626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237633 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 2, 4]
def baseStart_4237633 : Nat := 118140960795 + 4237633 * 2 ^ 59
def prefixEnd_4237633 : Nat := 4983230072969 + 3 ^ 40 * 4237633 * 2
def baseEnd_4237633 : Nat := 725314188784774658366329

theorem tailTrace_4237633 : CollatzResearch.WordTrace tailWord_4237633 prefixEnd_4237633 725314188784774658366329 := by
  unfold tailWord_4237633
  simp only [CollatzResearch.WordTrace]
  refine ⟨154559173056786845942413553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103039448704524563961609035 154559173056786845942413553)
  ·
    refine ⟨115919379792590134456810165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154559173056786845942413553 115919379792590134456810165)
    ·
      refine ⟨10867441855555325105325953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115919379792590134456810165 10867441855555325105325953)
      ·
        refine ⟨8150581391666493828994465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10867441855555325105325953 8150581391666493828994465)
        ·
          refine ⟨6112936043749870371745849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8150581391666493828994465 6112936043749870371745849)
          ·
            refine ⟨4584702032812402778809387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6112936043749870371745849 4584702032812402778809387)
            ·
              refine ⟨6877053049218604168214081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4584702032812402778809387 6877053049218604168214081)
              ·
                refine ⟨5157789786913953126160561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6877053049218604168214081 5157789786913953126160561)
                ·
                  refine ⟨3868342340185464844620421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5157789786913953126160561 3868342340185464844620421)
                  ·
                    refine ⟨725314188784774658366329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3868342340185464844620421 725314188784774658366329)
                    ·
                      rfl

theorem cell23_4237633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_4237633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237633 prefixEnd_4237633 := by exact prefixLift 4237633
  have htrace : WordTrace (prefixWord ++ tailWord_4237633) baseStart_4237633 baseEnd_4237633 := by
    simpa [prefixWord, tailWord_4237633, baseEnd_4237633] using wordTrace_append hprefix tailTrace_4237633
  have hstable : (prefixWord ++ tailWord_4237633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237633).length < 2 ^ (prefixWord ++ tailWord_4237633).sum := by decide
  have hdescent : baseEnd_4237633 < baseStart_4237633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237639 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_4237639 : Nat := 118140960795 + 4237639 * 2 ^ 59
def prefixEnd_4237639 : Nat := 4983230072969 + 3 ^ 40 * 4237639 * 2
def baseEnd_4237639 : Nat := 2175945647238250951623959

theorem tailTrace_4237639 : CollatzResearch.WordTrace tailWord_4237639 prefixEnd_4237639 2175945647238250951623959 := by
  unfold tailWord_4237639
  simp only [CollatzResearch.WordTrace]
  refine ⟨154559391894765108967131971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103039594596510072644754647 154559391894765108967131971)
  ·
    refine ⟨231839087842147663450697957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154559391894765108967131971 231839087842147663450697957)
    ·
      refine ⟨43469828970402686897005867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231839087842147663450697957 43469828970402686897005867)
      ·
        refine ⟨65204743455604030345508801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43469828970402686897005867 65204743455604030345508801)
        ·
          refine ⟨48903557591703022759131601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65204743455604030345508801 48903557591703022759131601)
          ·
            refine ⟨36677668193777267069348701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48903557591703022759131601 36677668193777267069348701)
            ·
              refine ⟨13754125572666475151005763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36677668193777267069348701 13754125572666475151005763)
              ·
                refine ⟨20631188358999712726508645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13754125572666475151005763 20631188358999712726508645)
                ·
                  refine ⟨3868347817312446136220371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20631188358999712726508645 3868347817312446136220371)
                  ·
                    refine ⟨5802521725968669204330557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3868347817312446136220371 5802521725968669204330557)
                    ·
                      refine ⟨2175945647238250951623959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5802521725968669204330557 2175945647238250951623959)
                      ·
                        rfl

theorem cell23_4237639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_4237639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237639 prefixEnd_4237639 := by exact prefixLift 4237639
  have htrace : WordTrace (prefixWord ++ tailWord_4237639) baseStart_4237639 baseEnd_4237639 := by
    simpa [prefixWord, tailWord_4237639, baseEnd_4237639] using wordTrace_append hprefix tailTrace_4237639
  have hstable : (prefixWord ++ tailWord_4237639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237639).length < 2 ^ (prefixWord ++ tailWord_4237639).sum := by decide
  have hdescent : baseEnd_4237639 < baseStart_4237639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237682 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_4237682 : Nat := 118140960795 + 4237682 * 2 ^ 59
def prefixEnd_4237682 : Nat := 4983230072969 + 3 ^ 40 * 4237682 * 2
def baseEnd_4237682 : Nat := 2175967726906394283386261

theorem tailTrace_4237682 : CollatzResearch.WordTrace tailWord_4237682 prefixEnd_4237682 2175967726906394283386261 := by
  unfold tailWord_4237682
  simp only [CollatzResearch.WordTrace]
  refine ⟨38640240058402331827736825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103040640155739551540631533 38640240058402331827736825)
  ·
    refine ⟨28980180043801748870802619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38640240058402331827736825 28980180043801748870802619)
    ·
      refine ⟨43470270065702623306203929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28980180043801748870802619 43470270065702623306203929)
      ·
        refine ⟨32602702549276967479652947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43470270065702623306203929 32602702549276967479652947)
        ·
          refine ⟨48904053823915451219479421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32602702549276967479652947 48904053823915451219479421)
          ·
            refine ⟨18339020183968294207304783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48904053823915451219479421 18339020183968294207304783)
            ·
              refine ⟨27508530275952441310957175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18339020183968294207304783 27508530275952441310957175)
              ·
                refine ⟨41262795413928661966435763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27508530275952441310957175 41262795413928661966435763)
                ·
                  refine ⟨61894193120892992949653645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41262795413928661966435763 61894193120892992949653645)
                  ·
                    refine ⟨23210322420334872356120117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61894193120892992949653645 23210322420334872356120117)
                    ·
                      refine ⟨2175967726906394283386261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23210322420334872356120117 2175967726906394283386261)
                      ·
                        rfl

theorem cell23_4237682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_4237682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237682 prefixEnd_4237682 := by exact prefixLift 4237682
  have htrace : WordTrace (prefixWord ++ tailWord_4237682) baseStart_4237682 baseEnd_4237682 := by
    simpa [prefixWord, tailWord_4237682, baseEnd_4237682] using wordTrace_append hprefix tailTrace_4237682
  have hstable : (prefixWord ++ tailWord_4237682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237682).length < 2 ^ (prefixWord ++ tailWord_4237682).sum := by decide
  have hdescent : baseEnd_4237682 < baseStart_4237682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237692 : List Nat := [2, 2, 2, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_4237692 : Nat := 118140960795 + 4237692 * 2 ^ 59
def prefixEnd_4237692 : Nat := 4983230072969 + 3 ^ 40 * 4237692 * 2
def baseEnd_4237692 : Nat := 2175972861712939244261215

theorem tailTrace_4237692 : CollatzResearch.WordTrace tailWord_4237692 prefixEnd_4237692 2175972861712939244261215 := by
  unfold tailWord_4237692
  simp only [CollatzResearch.WordTrace]
  refine ⟨77280662481786549509405665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103040883309048732679207553 77280662481786549509405665)
  ·
    refine ⟨57960496861339912132054249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77280662481786549509405665 57960496861339912132054249)
    ·
      refine ⟨43470372646004934099040687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57960496861339912132054249 43470372646004934099040687)
      ·
        refine ⟨65205558969007401148561031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43470372646004934099040687 65205558969007401148561031)
        ·
          refine ⟨97808338453511101722841547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65205558969007401148561031 97808338453511101722841547)
          ·
            refine ⟨146712507680266652584262321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97808338453511101722841547 146712507680266652584262321)
            ·
              refine ⟨110034380760199989438196741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146712507680266652584262321 110034380760199989438196741)
              ·
                refine ⟨20631446392537498019661889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 110034380760199989438196741 20631446392537498019661889)
                ·
                  refine ⟨15473584794403123514746417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20631446392537498019661889 15473584794403123514746417)
                  ·
                    refine ⟨11605188595802342636059813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15473584794403123514746417 11605188595802342636059813)
                    ·
                      refine ⟨2175972861712939244261215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11605188595802342636059813 2175972861712939244261215)
                      ·
                        rfl

theorem cell23_4237692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_4237692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237692 prefixEnd_4237692 := by exact prefixLift 4237692
  have htrace : WordTrace (prefixWord ++ tailWord_4237692) baseStart_4237692 baseEnd_4237692 := by
    simpa [prefixWord, tailWord_4237692, baseEnd_4237692] using wordTrace_append hprefix tailTrace_4237692
  have hstable : (prefixWord ++ tailWord_4237692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237692).length < 2 ^ (prefixWord ++ tailWord_4237692).sum := by decide
  have hdescent : baseEnd_4237692 < baseStart_4237692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237732 : List Nat := [2, 3, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_4237732 : Nat := 118140960795 + 4237732 * 2 ^ 59
def prefixEnd_4237732 : Nat := 4983230072969 + 3 ^ 40 * 4237732 * 2
def baseEnd_4237732 : Nat := 725331133646373029253677

theorem tailTrace_4237732 : CollatzResearch.WordTrace tailWord_4237732 prefixEnd_4237732 725331133646373029253677 := by
  unfold tailWord_4237732
  simp only [CollatzResearch.WordTrace]
  refine ⟨77281391941714092925133725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103041855922285457233511633 77281391941714092925133725)
  ·
    refine ⟨28980521978142784846925147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77281391941714092925133725 28980521978142784846925147)
    ·
      refine ⟨43470782967214177270387721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28980521978142784846925147 43470782967214177270387721)
      ·
        refine ⟨32603087225410632952790791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43470782967214177270387721 32603087225410632952790791)
        ·
          refine ⟨48904630838115949429186187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32603087225410632952790791 48904630838115949429186187)
          ·
            refine ⟨73356946257173924143779281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48904630838115949429186187 73356946257173924143779281)
            ·
              refine ⟨55017709692880443107834461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73356946257173924143779281 55017709692880443107834461)
              ·
                refine ⟨20631641134830166165437923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55017709692880443107834461 20631641134830166165437923)
                ·
                  refine ⟨30947461702245249248156885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20631641134830166165437923 30947461702245249248156885)
                  ·
                    refine ⟨725331133646373029253677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30947461702245249248156885 725331133646373029253677)
                    ·
                      rfl

theorem cell23_4237732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_4237732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237732 prefixEnd_4237732 := by exact prefixLift 4237732
  have htrace : WordTrace (prefixWord ++ tailWord_4237732) baseStart_4237732 baseEnd_4237732 := by
    simpa [prefixWord, tailWord_4237732, baseEnd_4237732] using wordTrace_append hprefix tailTrace_4237732
  have hstable : (prefixWord ++ tailWord_4237732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237732).length < 2 ^ (prefixWord ++ tailWord_4237732).sum := by decide
  have hdescent : baseEnd_4237732 < baseStart_4237732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237752 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_4237752 : Nat := 118140960795 + 4237752 * 2 ^ 59
def prefixEnd_4237752 : Nat := 4983230072969 + 3 ^ 40 * 4237752 * 2
def baseEnd_4237752 : Nat := 2176003670552209009510939

theorem tailTrace_4237752 : CollatzResearch.WordTrace tailWord_4237752 prefixEnd_4237752 2176003670552209009510939 := by
  unfold tailWord_4237752
  simp only [CollatzResearch.WordTrace]
  refine ⟨77281756671677864632997755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103042342228903819510663673 77281756671677864632997755)
  ·
    refine ⟨115922635007516796949496633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77281756671677864632997755 115922635007516796949496633)
    ·
      refine ⟨86941976255637597712122475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115922635007516796949496633 86941976255637597712122475)
      ·
        refine ⟨130412964383456396568183713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86941976255637597712122475 130412964383456396568183713)
        ·
          refine ⟨97809723287592297426137785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130412964383456396568183713 97809723287592297426137785)
          ·
            refine ⟨73357292465694223069603339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97809723287592297426137785 73357292465694223069603339)
            ·
              refine ⟨110035938698541334604405009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73357292465694223069603339 110035938698541334604405009)
              ·
                refine ⟨82526954023906000953303757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110035938698541334604405009 82526954023906000953303757)
                ·
                  refine ⟨30947607758964750357488909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82526954023906000953303757 30947607758964750357488909)
                  ·
                    refine ⟨11605352909611781384058341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30947607758964750357488909 11605352909611781384058341)
                    ·
                      refine ⟨2176003670552209009510939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11605352909611781384058341 2176003670552209009510939)
                      ·
                        rfl

theorem cell23_4237752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_4237752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237752 prefixEnd_4237752 := by exact prefixLift 4237752
  have htrace : WordTrace (prefixWord ++ tailWord_4237752) baseStart_4237752 baseEnd_4237752 := by
    simpa [prefixWord, tailWord_4237752, baseEnd_4237752] using wordTrace_append hprefix tailTrace_4237752
  have hstable : (prefixWord ++ tailWord_4237752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237752).length < 2 ^ (prefixWord ++ tailWord_4237752).sum := by decide
  have hdescent : baseEnd_4237752 < baseStart_4237752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237753 : List Nat := [1, 2, 1, 4, 3, 3, 2, 2, 5]
def baseStart_4237753 : Nat := 118140960795 + 4237753 * 2 ^ 59
def prefixEnd_4237753 : Nat := 4983230072969 + 3 ^ 40 * 4237753 * 2
def baseEnd_4237753 : Nat := 241778242670318167288715

theorem tailTrace_4237753 : CollatzResearch.WordTrace tailWord_4237753 prefixEnd_4237753 241778242670318167288715 := by
  unfold tailWord_4237753
  simp only [CollatzResearch.WordTrace]
  refine ⟨154563549816352106436781913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103042366544234737624521275 154563549816352106436781913)
  ·
    refine ⟨115922662362264079827586435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154563549816352106436781913 115922662362264079827586435)
    ·
      refine ⟨173883993543396119741379653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115922662362264079827586435 173883993543396119741379653)
      ·
        refine ⟨32603248789386772451508685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173883993543396119741379653 32603248789386772451508685)
        ·
          refine ⟨12226218296020039669315757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32603248789386772451508685 12226218296020039669315757)
          ·
            refine ⟨4584831861007514875993409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12226218296020039669315757 4584831861007514875993409)
            ·
              refine ⟨3438623895755636156995057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4584831861007514875993409 3438623895755636156995057)
              ·
                refine ⟨2578967921816727117746293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3438623895755636156995057 2578967921816727117746293)
                ·
                  refine ⟨241778242670318167288715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2578967921816727117746293 241778242670318167288715)
                  ·
                    rfl

theorem cell23_4237753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 2, 5].length) (baseStart_4237753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237753 prefixEnd_4237753 := by exact prefixLift 4237753
  have htrace : WordTrace (prefixWord ++ tailWord_4237753) baseStart_4237753 baseEnd_4237753 := by
    simpa [prefixWord, tailWord_4237753, baseEnd_4237753] using wordTrace_append hprefix tailTrace_4237753
  have hstable : (prefixWord ++ tailWord_4237753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237753).length < 2 ^ (prefixWord ++ tailWord_4237753).sum := by decide
  have hdescent : baseEnd_4237753 < baseStart_4237753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237756 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 2, 5, 2]
def baseStart_4237756 : Nat := 118140960795 + 4237756 * 2 ^ 59
def prefixEnd_4237756 : Nat := 4983230072969 + 3 ^ 40 * 4237756 * 2
def baseEnd_4237756 : Nat := 2176005724474826993860921

theorem tailTrace_4237756 : CollatzResearch.WordTrace tailWord_4237756 prefixEnd_4237756 2176005724474826993860921 := by
  unfold tailWord_4237756
  simp only [CollatzResearch.WordTrace]
  refine ⟨77281829617670618974570561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103042439490227491966094081 77281829617670618974570561)
  ·
    refine ⟨57961372213252964230927921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77281829617670618974570561 57961372213252964230927921)
    ·
      refine ⟨43471029159939723173195941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57961372213252964230927921 43471029159939723173195941)
      ·
        refine ⟨8150817967488698094974239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43471029159939723173195941 8150817967488698094974239)
        ·
          refine ⟨12226226951233047142461359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8150817967488698094974239 12226226951233047142461359)
          ·
            refine ⟨18339340426849570713692039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12226226951233047142461359 18339340426849570713692039)
            ·
              refine ⟨27509010640274356070538059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18339340426849570713692039 27509010640274356070538059)
              ·
                refine ⟨41263515960411534105807089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27509010640274356070538059 41263515960411534105807089)
                ·
                  refine ⟨30947636970308650579355317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41263515960411534105807089 30947636970308650579355317)
                  ·
                    refine ⟨2901340965966435991814561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30947636970308650579355317 2901340965966435991814561)
                    ·
                      refine ⟨2176005724474826993860921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2901340965966435991814561 2176005724474826993860921)
                      ·
                        rfl

theorem cell23_4237756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_4237756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237756 prefixEnd_4237756 := by exact prefixLift 4237756
  have htrace : WordTrace (prefixWord ++ tailWord_4237756) baseStart_4237756 baseEnd_4237756 := by
    simpa [prefixWord, tailWord_4237756, baseEnd_4237756] using wordTrace_append hprefix tailTrace_4237756
  have hstable : (prefixWord ++ tailWord_4237756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237756).length < 2 ^ (prefixWord ++ tailWord_4237756).sum := by decide
  have hdescent : baseEnd_4237756 < baseStart_4237756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237769 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 1, 6, 2]
def baseStart_4237769 : Nat := 118140960795 + 4237769 * 2 ^ 59
def prefixEnd_4237769 : Nat := 4983230072969 + 3 ^ 40 * 4237769 * 2
def baseEnd_4237769 : Nat := 2176012399723335442998361

theorem tailTrace_4237769 : CollatzResearch.WordTrace tailWord_4237769 prefixEnd_4237769 2176012399723335442998361 := by
  unfold tailWord_4237769
  simp only [CollatzResearch.WordTrace]
  refine ⟨154564133384294141169364361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103042755589529427446242907 154564133384294141169364361)
  ·
    refine ⟨115923100038220605877023271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154564133384294141169364361 115923100038220605877023271)
    ·
      refine ⟨173884650057330908815534907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115923100038220605877023271 173884650057330908815534907)
      ·
        refine ⟨260826975085996363223302361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173884650057330908815534907 260826975085996363223302361)
        ·
          refine ⟨195620231314497272417476771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 260826975085996363223302361 195620231314497272417476771)
          ·
            refine ⟨293430346971745908626215157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195620231314497272417476771 293430346971745908626215157)
            ·
              refine ⟨27509095028601178933707671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 293430346971745908626215157 27509095028601178933707671)
              ·
                refine ⟨41263642542901768400561507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27509095028601178933707671 41263642542901768400561507)
                ·
                  refine ⟨61895463814352652600842261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41263642542901768400561507 61895463814352652600842261)
                  ·
                    refine ⟨2901349866297780590664481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61895463814352652600842261 2901349866297780590664481)
                    ·
                      refine ⟨2176012399723335442998361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2901349866297780590664481 2176012399723335442998361)
                      ·
                        rfl

theorem cell23_4237769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 6, 2].length) (baseStart_4237769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237769 prefixEnd_4237769 := by exact prefixLift 4237769
  have htrace : WordTrace (prefixWord ++ tailWord_4237769) baseStart_4237769 baseEnd_4237769 := by
    simpa [prefixWord, tailWord_4237769, baseEnd_4237769] using wordTrace_append hprefix tailTrace_4237769
  have hstable : (prefixWord ++ tailWord_4237769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237769).length < 2 ^ (prefixWord ++ tailWord_4237769).sum := by decide
  have hdescent : baseEnd_4237769 < baseStart_4237769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237792 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 8]
def baseStart_4237792 : Nat := 118140960795 + 4237792 * 2 ^ 59
def prefixEnd_4237792 : Nat := 4983230072969 + 3 ^ 40 * 4237792 * 2
def baseEnd_4237792 : Nat := 241780467753154317001195

theorem tailTrace_4237792 : CollatzResearch.WordTrace tailWord_4237792 prefixEnd_4237792 241780467753154317001195 := by
  unfold tailWord_4237792
  simp only [CollatzResearch.WordTrace]
  refine ⟨77282486131605408048725815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103043314842140544064967753 77282486131605408048725815)
  ·
    refine ⟨115923729197408112073088723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77282486131605408048725815 115923729197408112073088723)
    ·
      refine ⟨173885593796112168109633085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115923729197408112073088723 173885593796112168109633085)
      ·
        refine ⟨65207097673542063041112407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 173885593796112168109633085 65207097673542063041112407)
        ·
          refine ⟨97810646510313094561668611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65207097673542063041112407 97810646510313094561668611)
          ·
            refine ⟨146715969765469641842502917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97810646510313094561668611 146715969765469641842502917)
            ·
              refine ⟨27509244331025557845469297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146715969765469641842502917 27509244331025557845469297)
              ·
                refine ⟨20631933248269168384101973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27509244331025557845469297 20631933248269168384101973)
                ·
                  refine ⟨241780467753154317001195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20631933248269168384101973 241780467753154317001195)
                  ·
                    rfl

theorem cell23_4237792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 8].length) (baseStart_4237792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237792 prefixEnd_4237792 := by exact prefixLift 4237792
  have htrace : WordTrace (prefixWord ++ tailWord_4237792) baseStart_4237792 baseEnd_4237792 := by
    simpa [prefixWord, tailWord_4237792, baseEnd_4237792] using wordTrace_append hprefix tailTrace_4237792
  have hstable : (prefixWord ++ tailWord_4237792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237792).length < 2 ^ (prefixWord ++ tailWord_4237792).sum := by decide
  have hdescent : baseEnd_4237792 < baseStart_4237792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237839 : List Nat := [1, 1, 2, 1, 1, 1, 2, 8, 1, 5]
def baseStart_4237839 : Nat := 118140960795 + 4237839 * 2 ^ 59
def prefixEnd_4237839 : Nat := 4983230072969 + 3 ^ 40 * 4237839 * 2
def baseEnd_4237839 : Nat := 725349447789716723041013

theorem tailTrace_4237839 : CollatzResearch.WordTrace tailWord_4237839 prefixEnd_4237839 725349447789716723041013 := by
  unfold tailWord_4237839
  simp only [CollatzResearch.WordTrace]
  refine ⟨154566686494040543124412571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103044457662693695416275047 154566686494040543124412571)
  ·
    refine ⟨231850029741060814686618857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154566686494040543124412571 231850029741060814686618857)
    ·
      refine ⟨173887522305795611014964143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231850029741060814686618857 173887522305795611014964143)
      ·
        refine ⟨260831283458693416522446215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173887522305795611014964143 260831283458693416522446215)
        ·
          refine ⟨391246925188040124783669323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260831283458693416522446215 391246925188040124783669323)
          ·
            refine ⟨586870387782060187175503985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391246925188040124783669323 586870387782060187175503985)
            ·
              refine ⟨440152790836545140381627989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586870387782060187175503985 440152790836545140381627989)
              ·
                refine ⟨5158040517615763363847203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 440152790836545140381627989 5158040517615763363847203)
                ·
                  refine ⟨7737060776423645045770805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5158040517615763363847203 7737060776423645045770805)
                  ·
                    refine ⟨725349447789716723041013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7737060776423645045770805 725349447789716723041013)
                    ·
                      rfl

theorem cell23_4237839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 5].length) (baseStart_4237839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237839 prefixEnd_4237839 := by exact prefixLift 4237839
  have htrace : WordTrace (prefixWord ++ tailWord_4237839) baseStart_4237839 baseEnd_4237839 := by
    simpa [prefixWord, tailWord_4237839, baseEnd_4237839] using wordTrace_append hprefix tailTrace_4237839
  have hstable : (prefixWord ++ tailWord_4237839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237839).length < 2 ^ (prefixWord ++ tailWord_4237839).sum := by decide
  have hdescent : baseEnd_4237839 < baseStart_4237839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237847 : List Nat := [1, 1, 3, 6, 1, 2, 1, 3, 1, 4]
def baseStart_4237847 : Nat := 118140960795 + 4237847 * 2 ^ 59
def prefixEnd_4237847 : Nat := 4983230072969 + 3 ^ 40 * 4237847 * 2
def baseEnd_4237847 : Nat := 725350817071462045941001

theorem tailTrace_4237847 : CollatzResearch.WordTrace tailWord_4237847 prefixEnd_4237847 725350817071462045941001 := by
  unfold tailWord_4237847
  simp only [CollatzResearch.WordTrace]
  refine ⟨154566978278011560490703795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103044652185341040327135863 154566978278011560490703795)
  ·
    refine ⟨231850467417017340736055693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154566978278011560490703795 231850467417017340736055693)
    ·
      refine ⟨86943925281381502776020885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231850467417017340736055693 86943925281381502776020885)
      ·
        refine ⟨4075496497564757942625979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 86943925281381502776020885 4075496497564757942625979)
        ·
          refine ⟨6113244746347136913938969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075496497564757942625979 6113244746347136913938969)
          ·
            refine ⟨4584933559760352685454227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6113244746347136913938969 4584933559760352685454227)
            ·
              refine ⟨6877400339640529028181341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4584933559760352685454227 6877400339640529028181341)
              ·
                refine ⟨2579025127365198385568003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6877400339640529028181341 2579025127365198385568003)
                ·
                  refine ⟨3868537691047797578352005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579025127365198385568003 3868537691047797578352005)
                  ·
                    refine ⟨725350817071462045941001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3868537691047797578352005 725350817071462045941001)
                    ·
                      rfl

theorem cell23_4237847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_4237847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237847 prefixEnd_4237847 := by exact prefixLift 4237847
  have htrace : WordTrace (prefixWord ++ tailWord_4237847) baseStart_4237847 baseEnd_4237847 := by
    simpa [prefixWord, tailWord_4237847, baseEnd_4237847] using wordTrace_append hprefix tailTrace_4237847
  have hstable : (prefixWord ++ tailWord_4237847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237847).length < 2 ^ (prefixWord ++ tailWord_4237847).sum := by decide
  have hdescent : baseEnd_4237847 < baseStart_4237847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237879 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 5]
def baseStart_4237879 : Nat := 118140960795 + 4237879 * 2 ^ 59
def prefixEnd_4237879 : Nat := 4983230072969 + 3 ^ 40 * 4237879 * 2
def baseEnd_4237879 : Nat := 2176068882595330012622855

theorem tailTrace_4237879 : CollatzResearch.WordTrace tailWord_4237879 prefixEnd_4237879 2176068882595330012622855 := by
  unfold tailWord_4237879
  simp only [CollatzResearch.WordTrace]
  refine ⟨154568145413895629955868691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103045430275930419970579127 154568145413895629955868691)
  ·
    refine ⟨231852218120843444933803037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154568145413895629955868691 231852218120843444933803037)
    ·
      refine ⟨86944581795316291850176139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231852218120843444933803037 86944581795316291850176139)
      ·
        refine ⟨130416872692974437775264209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86944581795316291850176139 130416872692974437775264209)
        ·
          refine ⟨97812654519730828331448157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130416872692974437775264209 97812654519730828331448157)
          ·
            refine ⟨36679745444899060624293059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97812654519730828331448157 36679745444899060624293059)
            ·
              refine ⟨55019618167348590936439589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36679745444899060624293059 55019618167348590936439589)
              ·
                refine ⟨10316178406377860800582423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55019618167348590936439589 10316178406377860800582423)
                ·
                  refine ⟨15474267609566791200873635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10316178406377860800582423 15474267609566791200873635)
                  ·
                    refine ⟨23211401414350186801310453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15474267609566791200873635 23211401414350186801310453)
                    ·
                      refine ⟨2176068882595330012622855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23211401414350186801310453 2176068882595330012622855)
                      ·
                        rfl

theorem cell23_4237879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_4237879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237879 prefixEnd_4237879 := by exact prefixLift 4237879
  have htrace : WordTrace (prefixWord ++ tailWord_4237879) baseStart_4237879 baseEnd_4237879 := by
    simpa [prefixWord, tailWord_4237879, baseEnd_4237879] using wordTrace_append hprefix tailTrace_4237879
  have hstable : (prefixWord ++ tailWord_4237879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237879).length < 2 ^ (prefixWord ++ tailWord_4237879).sum := by decide
  have hdescent : baseEnd_4237879 < baseStart_4237879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237893 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 4]
def baseStart_4237893 : Nat := 118140960795 + 4237893 * 2 ^ 59
def prefixEnd_4237893 : Nat := 4983230072969 + 3 ^ 40 * 4237893 * 2
def baseEnd_4237893 : Nat := 2176076071324492957847791

theorem tailTrace_4237893 : CollatzResearch.WordTrace tailWord_4237893 prefixEnd_4237893 2176076071324492957847791 := by
  unfold tailWord_4237893
  simp only [CollatzResearch.WordTrace]
  refine ⟨154568656035844910346878333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103045770690563273564585555 154568656035844910346878333)
  ·
    refine ⟨57963246013441841380079375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154568656035844910346878333 57963246013441841380079375)
    ·
      refine ⟨86944869020162762070119063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57963246013441841380079375 86944869020162762070119063)
      ·
        refine ⟨130417303530244143105178595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86944869020162762070119063 130417303530244143105178595)
        ·
          refine ⟨195625955295366214657767893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130417303530244143105178595 195625955295366214657767893)
          ·
            refine ⟨4584983327235145656041435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 195625955295366214657767893 4584983327235145656041435)
            ·
              refine ⟨6877474990852718484062153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4584983327235145656041435 6877474990852718484062153)
              ·
                refine ⟨5158106243139538863046615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6877474990852718484062153 5158106243139538863046615)
                ·
                  refine ⟨7737159364709308294569923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5158106243139538863046615 7737159364709308294569923)
                  ·
                    refine ⟨11605739047063962441854885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7737159364709308294569923 11605739047063962441854885)
                    ·
                      refine ⟨2176076071324492957847791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11605739047063962441854885 2176076071324492957847791)
                      ·
                        rfl

theorem cell23_4237893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_4237893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237893 prefixEnd_4237893 := by exact prefixLift 4237893
  have htrace : WordTrace (prefixWord ++ tailWord_4237893) baseStart_4237893 baseEnd_4237893 := by
    simpa [prefixWord, tailWord_4237893, baseEnd_4237893] using wordTrace_append hprefix tailTrace_4237893
  have hstable : (prefixWord ++ tailWord_4237893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237893).length < 2 ^ (prefixWord ++ tailWord_4237893).sum := by decide
  have hdescent : baseEnd_4237893 < baseStart_4237893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237906 : List Nat := [3, 2, 2, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_4237906 : Nat := 118140960795 + 4237906 * 2 ^ 59
def prefixEnd_4237906 : Nat := 4983230072969 + 3 ^ 40 * 4237906 * 2
def baseEnd_4237906 : Nat := 2176082746573001406985231

theorem tailTrace_4237906 : CollatzResearch.WordTrace tailWord_4237906 prefixEnd_4237906 2176082746573001406985231 := by
  unfold tailWord_4237906
  simp only [CollatzResearch.WordTrace]
  refine ⟨38642282546199453391775393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103046086789865209044734381 38642282546199453391775393)
  ·
    refine ⟨28981711909649590043831545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38642282546199453391775393 28981711909649590043831545)
    ·
      refine ⟨21736283932237192532873659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28981711909649590043831545 21736283932237192532873659)
      ·
        refine ⟨32604425898355788799310489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21736283932237192532873659 32604425898355788799310489)
        ·
          refine ⟨24453319423766841599482867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32604425898355788799310489 24453319423766841599482867)
          ·
            refine ⟨36679979135650262399224301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24453319423766841599482867 36679979135650262399224301)
            ·
              refine ⟨13754992175868848399709113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36679979135650262399224301 13754992175868848399709113)
              ·
                refine ⟨10316244131901636299781835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13754992175868848399709113 10316244131901636299781835)
                ·
                  refine ⟨15474366197852454449672753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10316244131901636299781835 15474366197852454449672753)
                  ·
                    refine ⟨11605774648389340837254565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15474366197852454449672753 11605774648389340837254565)
                    ·
                      refine ⟨2176082746573001406985231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11605774648389340837254565 2176082746573001406985231)
                      ·
                        rfl

theorem cell23_4237906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_4237906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237906 prefixEnd_4237906 := by exact prefixLift 4237906
  have htrace : WordTrace (prefixWord ++ tailWord_4237906) baseStart_4237906 baseEnd_4237906 := by
    simpa [prefixWord, tailWord_4237906, baseEnd_4237906] using wordTrace_append hprefix tailTrace_4237906
  have hstable : (prefixWord ++ tailWord_4237906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237906).length < 2 ^ (prefixWord ++ tailWord_4237906).sum := by decide
  have hdescent : baseEnd_4237906 < baseStart_4237906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237916 : List Nat := [2, 2, 4, 1, 4, 10]
def baseStart_4237916 : Nat := 118140960795 + 4237916 * 2 ^ 59
def prefixEnd_4237916 : Nat := 4983230072969 + 3 ^ 40 * 4237916 * 2
def baseEnd_4237916 : Nat := 8955094162055746369795

theorem tailTrace_4237916 : CollatzResearch.WordTrace tailWord_4237916 prefixEnd_4237916 8955094162055746369795 := by
  unfold tailWord_4237916
  simp only [CollatzResearch.WordTrace]
  refine ⟨77284747457380792637482801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103046329943174390183310401 77284747457380792637482801)
  ·
    refine ⟨57963560593035594478112101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77284747457380792637482801 57963560593035594478112101)
    ·
      refine ⟨10868167611194173964646019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57963560593035594478112101 10868167611194173964646019)
      ·
        refine ⟨16302251416791260946969029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10868167611194173964646019 16302251416791260946969029)
        ·
          refine ⟨3056672140648361427556693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16302251416791260946969029 3056672140648361427556693)
          ·
            refine ⟨8955094162055746369795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3056672140648361427556693 8955094162055746369795)
            ·
              rfl

theorem cell23_4237916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 10].length) (baseStart_4237916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237916 prefixEnd_4237916 := by exact prefixLift 4237916
  have htrace : WordTrace (prefixWord ++ tailWord_4237916) baseStart_4237916 baseEnd_4237916 := by
    simpa [prefixWord, tailWord_4237916, baseEnd_4237916] using wordTrace_append hprefix tailTrace_4237916
  have hstable : (prefixWord ++ tailWord_4237916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237916).length < 2 ^ (prefixWord ++ tailWord_4237916).sum := by decide
  have hdescent : baseEnd_4237916 < baseStart_4237916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237943 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 2, 1, 3]
def baseStart_4237943 : Nat := 118140960795 + 4237943 * 2 ^ 59
def prefixEnd_4237943 : Nat := 4983230072969 + 3 ^ 40 * 4237943 * 2
def baseEnd_4237943 : Nat := 2176101745357217762222561

theorem tailTrace_4237943 : CollatzResearch.WordTrace tailWord_4237943 prefixEnd_4237943 2176101745357217762222561 := by
  unfold tailWord_4237943
  simp only [CollatzResearch.WordTrace]
  refine ⟨154570479685663768886198483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103046986457109179257465655 154570479685663768886198483)
  ·
    refine ⟨231855719528495653329297725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154570479685663768886198483 231855719528495653329297725)
    ·
      refine ⟨86945894823185869998486647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 231855719528495653329297725 86945894823185869998486647)
      ·
        refine ⟨130418842234778804997729971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86945894823185869998486647 130418842234778804997729971)
        ·
          refine ⟨195628263352168207496594957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130418842234778804997729971 195628263352168207496594957)
          ·
            refine ⟨73360598757063077811223109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 195628263352168207496594957 73360598757063077811223109)
            ·
              refine ⟨13755112266949327089604333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73360598757063077811223109 13755112266949327089604333)
              ·
                refine ⟨5158167100105997658601625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13755112266949327089604333 5158167100105997658601625)
                ·
                  refine ⟨3868625325079498243951219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5158167100105997658601625 3868625325079498243951219)
                  ·
                    refine ⟨5802937987619247365926829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3868625325079498243951219 5802937987619247365926829)
                    ·
                      refine ⟨2176101745357217762222561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5802937987619247365926829 2176101745357217762222561)
                      ·
                        rfl

theorem cell23_4237943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 1, 3].length) (baseStart_4237943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237943 prefixEnd_4237943 := by exact prefixLift 4237943
  have htrace : WordTrace (prefixWord ++ tailWord_4237943) baseStart_4237943 baseEnd_4237943 := by
    simpa [prefixWord, tailWord_4237943, baseEnd_4237943] using wordTrace_append hprefix tailTrace_4237943
  have hstable : (prefixWord ++ tailWord_4237943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237943).length < 2 ^ (prefixWord ++ tailWord_4237943).sum := by decide
  have hdescent : baseEnd_4237943 < baseStart_4237943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237953 : List Nat := [1, 2, 4, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_4237953 : Nat := 118140960795 + 4237953 * 2 ^ 59
def prefixEnd_4237953 : Nat := 4983230072969 + 3 ^ 40 * 4237953 * 2
def baseEnd_4237953 : Nat := 2176106880163762723097515

theorem tailTrace_4237953 : CollatzResearch.WordTrace tailWord_4237953 prefixEnd_4237953 2176106880163762723097515 := by
  unfold tailWord_4237953
  simp only [CollatzResearch.WordTrace]
  refine ⟨154570844415627540594062513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103047229610418360396041675 154570844415627540594062513)
  ·
    refine ⟨115928133311720655445546885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154570844415627540594062513 115928133311720655445546885)
    ·
      refine ⟨21736524995947622896040041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115928133311720655445546885 21736524995947622896040041)
      ·
        refine ⟨16302393746960717172030031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21736524995947622896040041 16302393746960717172030031)
        ·
          refine ⟨24453590620441075758045047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16302393746960717172030031 24453590620441075758045047)
          ·
            refine ⟨36680385930661613637067571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24453590620441075758045047 36680385930661613637067571)
            ·
              refine ⟨55020578895992420455601357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36680385930661613637067571 55020578895992420455601357)
              ·
                refine ⟨20632717085997157670850509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55020578895992420455601357 20632717085997157670850509)
                ·
                  refine ⟨7737268907248934126568941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20632717085997157670850509 7737268907248934126568941)
                  ·
                    refine ⟨2901475840218350297463353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7737268907248934126568941 2901475840218350297463353)
                    ·
                      refine ⟨2176106880163762723097515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2901475840218350297463353 2176106880163762723097515)
                      ·
                        rfl

theorem cell23_4237953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_4237953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237953 prefixEnd_4237953 := by exact prefixLift 4237953
  have htrace : WordTrace (prefixWord ++ tailWord_4237953) baseStart_4237953 baseEnd_4237953 := by
    simpa [prefixWord, tailWord_4237953, baseEnd_4237953] using wordTrace_append hprefix tailTrace_4237953
  have hstable : (prefixWord ++ tailWord_4237953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237953).length < 2 ^ (prefixWord ++ tailWord_4237953).sum := by decide
  have hdescent : baseEnd_4237953 < baseStart_4237953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237959 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 1, 8]
def baseStart_4237959 : Nat := 118140960795 + 4237959 * 2 ^ 59
def prefixEnd_4237959 : Nat := 4983230072969 + 3 ^ 40 * 4237959 * 2
def baseEnd_4237959 : Nat := 725369987015896566540829

theorem tailTrace_4237959 : CollatzResearch.WordTrace tailWord_4237959 prefixEnd_4237959 725369987015896566540829 := by
  unfold tailWord_4237959
  simp only [CollatzResearch.WordTrace]
  refine ⟨154571063253605803618780931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103047375502403869079187287 154571063253605803618780931)
  ·
    refine ⟨231856594880408705428171397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154571063253605803618780931 231856594880408705428171397)
    ·
      refine ⟨43473111540076632267782137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 231856594880408705428171397 43473111540076632267782137)
      ·
        refine ⟨32604833655057474200836603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43473111540076632267782137 32604833655057474200836603)
        ·
          refine ⟨48907250482586211301254905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32604833655057474200836603 48907250482586211301254905)
          ·
            refine ⟨36680437861939658475941179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48907250482586211301254905 36680437861939658475941179)
            ·
              refine ⟨55020656792909487713911769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36680437861939658475941179 55020656792909487713911769)
              ·
                refine ⟨41265492594682115785433827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55020656792909487713911769 41265492594682115785433827)
                ·
                  refine ⟨61898238892023173678150741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41265492594682115785433827 61898238892023173678150741)
                  ·
                    refine ⟨725369987015896566540829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61898238892023173678150741 725369987015896566540829)
                    ·
                      rfl

theorem cell23_4237959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_4237959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237959 prefixEnd_4237959 := by exact prefixLift 4237959
  have htrace : WordTrace (prefixWord ++ tailWord_4237959) baseStart_4237959 baseEnd_4237959 := by
    simpa [prefixWord, tailWord_4237959, baseEnd_4237959] using wordTrace_append hprefix tailTrace_4237959
  have hstable : (prefixWord ++ tailWord_4237959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237959).length < 2 ^ (prefixWord ++ tailWord_4237959).sum := by decide
  have hdescent : baseEnd_4237959 < baseStart_4237959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237969 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_4237969 : Nat := 118140960795 + 4237969 * 2 ^ 59
def prefixEnd_4237969 : Nat := 4983230072969 + 3 ^ 40 * 4237969 * 2
def baseEnd_4237969 : Nat := 2176115095854234660497441

theorem tailTrace_4237969 : CollatzResearch.WordTrace tailWord_4237969 prefixEnd_4237969 2176115095854234660497441 := by
  unfold tailWord_4237969
  simp only [CollatzResearch.WordTrace]
  refine ⟨154571427983569575326644961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103047618655713050217763307 154571427983569575326644961)
  ·
    refine ⟨115928570987677181494983721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154571427983569575326644961 115928570987677181494983721)
    ·
      refine ⟨86946428240757886121237791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115928570987677181494983721 86946428240757886121237791)
      ·
        refine ⟨130419642361136829181856687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86946428240757886121237791 130419642361136829181856687)
        ·
          refine ⟨195629463541705243772785031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130419642361136829181856687 195629463541705243772785031)
          ·
            refine ⟨293444195312557865659177547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195629463541705243772785031 293444195312557865659177547)
            ·
              refine ⟨440166292968836798488766321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 293444195312557865659177547 440166292968836798488766321)
              ·
                refine ⟨330124719726627598866574741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 440166292968836798488766321 330124719726627598866574741)
                ·
                  refine ⟨15474596237185668696870691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 330124719726627598866574741 15474596237185668696870691)
                  ·
                    refine ⟨23211894355778503045306037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15474596237185668696870691 23211894355778503045306037)
                    ·
                      refine ⟨2176115095854234660497441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23211894355778503045306037 2176115095854234660497441)
                      ·
                        rfl

theorem cell23_4237969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_4237969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237969 prefixEnd_4237969 := by exact prefixLift 4237969
  have htrace : WordTrace (prefixWord ++ tailWord_4237969) baseStart_4237969 baseEnd_4237969 := by
    simpa [prefixWord, tailWord_4237969, baseEnd_4237969] using wordTrace_append hprefix tailTrace_4237969
  have hstable : (prefixWord ++ tailWord_4237969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237969).length < 2 ^ (prefixWord ++ tailWord_4237969).sum := by decide
  have hdescent : baseEnd_4237969 < baseStart_4237969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4237994 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_4237994 : Nat := 118140960795 + 4237994 * 2 ^ 59
def prefixEnd_4237994 : Nat := 4983230072969 + 3 ^ 40 * 4237994 * 2
def baseEnd_4237994 : Nat := 2176127932870597062684827

theorem tailTrace_4237994 : CollatzResearch.WordTrace tailWord_4237994 prefixEnd_4237994 2176127932870597062684827 := by
  unfold tailWord_4237994
  simp only [CollatzResearch.WordTrace]
  refine ⟨38643084952119751149076259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103048226538986003064203357 38643084952119751149076259)
  ·
    refine ⟨57964627428179626723614389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38643084952119751149076259 57964627428179626723614389)
    ·
      refine ⟨5434183821391840005338849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57964627428179626723614389 5434183821391840005338849)
      ·
        refine ⟨4075637866043880004004137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5434183821391840005338849 4075637866043880004004137)
        ·
          refine ⟨3056728399532910003003103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4075637866043880004004137 3056728399532910003003103)
          ·
            refine ⟨4585092599299365004504655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3056728399532910003003103 4585092599299365004504655)
            ·
              refine ⟨6877638898949047506756983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4585092599299365004504655 6877638898949047506756983)
              ·
                refine ⟨10316458348423571260135475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6877638898949047506756983 10316458348423571260135475)
                ·
                  refine ⟨15474687522635356890203213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10316458348423571260135475 15474687522635356890203213)
                  ·
                    refine ⟨5803007820988258833826205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15474687522635356890203213 5803007820988258833826205)
                    ·
                      refine ⟨2176127932870597062684827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5803007820988258833826205 2176127932870597062684827)
                      ·
                        rfl

theorem cell23_4237994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_4237994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4237994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4237994 prefixEnd_4237994 := by exact prefixLift 4237994
  have htrace : WordTrace (prefixWord ++ tailWord_4237994) baseStart_4237994 baseEnd_4237994 := by
    simpa [prefixWord, tailWord_4237994, baseEnd_4237994] using wordTrace_append hprefix tailTrace_4237994
  have hstable : (prefixWord ++ tailWord_4237994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4237994).length < 2 ^ (prefixWord ++ tailWord_4237994).sum := by decide
  have hdescent : baseEnd_4237994 < baseStart_4237994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4237994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238040 : List Nat := [2, 1, 2, 2, 3, 3, 3, 2, 5]
def baseStart_4238040 : Nat := 118140960795 + 4238040 * 2 ^ 59
def prefixEnd_4238040 : Nat := 4983230072969 + 3 ^ 40 * 4238040 * 2
def baseEnd_4238040 : Nat := 241794616997855986967735

theorem tailTrace_4238040 : CollatzResearch.WordTrace tailWord_4238040 prefixEnd_4238040 241794616997855986967735 := by
  unfold tailWord_4238040
  simp only [CollatzResearch.WordTrace]
  refine ⟨77287008783156177226239787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103049345044208236301653049 77287008783156177226239787)
  ·
    refine ⟨115930513174734265839359681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77287008783156177226239787 115930513174734265839359681)
    ·
      refine ⟨86947884881050699379519761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115930513174734265839359681 86947884881050699379519761)
      ·
        refine ⟨65210913660788024534639821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86947884881050699379519761 65210913660788024534639821)
        ·
          refine ⟨24454092622795509200489933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 65210913660788024534639821 24454092622795509200489933)
          ·
            refine ⟨9170284733548315950183725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24454092622795509200489933 9170284733548315950183725)
            ·
              refine ⟨3438856775080618481318897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9170284733548315950183725 3438856775080618481318897)
              ·
                refine ⟨2579142581310463860989173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3438856775080618481318897 2579142581310463860989173)
                ·
                  refine ⟨241794616997855986967735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2579142581310463860989173 241794616997855986967735)
                  ·
                    rfl

theorem cell23_4238040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 5].length) (baseStart_4238040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238040 prefixEnd_4238040 := by exact prefixLift 4238040
  have htrace : WordTrace (prefixWord ++ tailWord_4238040) baseStart_4238040 baseEnd_4238040 := by
    simpa [prefixWord, tailWord_4238040, baseEnd_4238040] using wordTrace_append hprefix tailTrace_4238040
  have hstable : (prefixWord ++ tailWord_4238040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238040).length < 2 ^ (prefixWord ++ tailWord_4238040).sum := by decide
  have hdescent : baseEnd_4238040 < baseStart_4238040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238123 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 5, 1, 3]
def baseStart_4238123 : Nat := 118140960795 + 4238123 * 2 ^ 59
def prefixEnd_4238123 : Nat := 4983230072969 + 3 ^ 40 * 4238123 * 2
def baseEnd_4238123 : Nat := 2176194171875027057971733

theorem tailTrace_4238123 : CollatzResearch.WordTrace tailWord_4238123 prefixEnd_4238123 2176194171875027057971733 := by
  unfold tailWord_4238123
  simp only [CollatzResearch.WordTrace]
  refine ⟨154577044825011659627751023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103051363216674439751834015 154577044825011659627751023)
  ·
    refine ⟨231865567237517489441626535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154577044825011659627751023 231865567237517489441626535)
    ·
      refine ⟨347798350856276234162439803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231865567237517489441626535 347798350856276234162439803)
      ·
        refine ⟨521697526284414351243659705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347798350856276234162439803 521697526284414351243659705)
        ·
          refine ⟨391273144713310763432744779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 521697526284414351243659705 391273144713310763432744779)
          ·
            refine ⟨586909717069966145149117169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391273144713310763432744779 586909717069966145149117169)
            ·
              refine ⟨440182287802474608861837877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 586909717069966145149117169 440182287802474608861837877)
              ·
                refine ⟨41267089481481994580797301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 440182287802474608861837877 41267089481481994580797301)
                ·
                  refine ⟨3868789638888936991949747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41267089481481994580797301 3868789638888936991949747)
                  ·
                    refine ⟨5803184458333405487924621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3868789638888936991949747 5803184458333405487924621)
                    ·
                      refine ⟨2176194171875027057971733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5803184458333405487924621 2176194171875027057971733)
                      ·
                        rfl

theorem cell23_4238123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 1, 3].length) (baseStart_4238123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238123 prefixEnd_4238123 := by exact prefixLift 4238123
  have htrace : WordTrace (prefixWord ++ tailWord_4238123) baseStart_4238123 baseEnd_4238123 := by
    simpa [prefixWord, tailWord_4238123, baseEnd_4238123] using wordTrace_append hprefix tailTrace_4238123
  have hstable : (prefixWord ++ tailWord_4238123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238123).length < 2 ^ (prefixWord ++ tailWord_4238123).sum := by decide
  have hdescent : baseEnd_4238123 < baseStart_4238123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238180 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_4238180 : Nat := 118140960795 + 4238180 * 2 ^ 59
def prefixEnd_4238180 : Nat := 4983230072969 + 3 ^ 40 * 4238180 * 2
def baseEnd_4238180 : Nat := 2176223440272333334958971

theorem tailTrace_4238180 : CollatzResearch.WordTrace tailWord_4238180 prefixEnd_4238180 2176223440272333334958971 := by
  unfold tailWord_4238180
  simp only [CollatzResearch.WordTrace]
  refine ⟨77289561892902579181287997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103052749190536772241717329 77289561892902579181287997)
  ·
    refine ⟨28983585709838467192982999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 77289561892902579181287997 28983585709838467192982999)
    ·
      refine ⟨43475378564757700789474499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28983585709838467192982999 43475378564757700789474499)
      ·
        refine ⟨65213067847136551184211749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43475378564757700789474499 65213067847136551184211749)
        ·
          refine ⟨12227450221338103347039703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65213067847136551184211749 12227450221338103347039703)
          ·
            refine ⟨18341175332007155020559555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12227450221338103347039703 18341175332007155020559555)
            ·
              refine ⟨27511762998010732530839333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18341175332007155020559555 27511762998010732530839333)
              ·
                refine ⟨5158455562127012349532375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27511762998010732530839333 5158455562127012349532375)
                ·
                  refine ⟨7737683343190518524298563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5158455562127012349532375 7737683343190518524298563)
                  ·
                    refine ⟨11606525014785777786447845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7737683343190518524298563 11606525014785777786447845)
                    ·
                      refine ⟨2176223440272333334958971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11606525014785777786447845 2176223440272333334958971)
                      ·
                        rfl

theorem cell23_4238180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_4238180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238180 prefixEnd_4238180 := by exact prefixLift 4238180
  have htrace : WordTrace (prefixWord ++ tailWord_4238180) baseStart_4238180 baseEnd_4238180 := by
    simpa [prefixWord, tailWord_4238180, baseEnd_4238180] using wordTrace_append hprefix tailTrace_4238180
  have hstable : (prefixWord ++ tailWord_4238180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238180).length < 2 ^ (prefixWord ++ tailWord_4238180).sum := by decide
  have hdescent : baseEnd_4238180 < baseStart_4238180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238234 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3]
def baseStart_4238234 : Nat := 118140960795 + 4238234 * 2 ^ 59
def prefixEnd_4238234 : Nat := 4983230072969 + 3 ^ 40 * 4238234 * 2
def baseEnd_4238234 : Nat := 2176251168227676123683723

theorem tailTrace_4238234 : CollatzResearch.WordTrace tailWord_4238234 prefixEnd_4238234 2176251168227676123683723 := by
  unfold tailWord_4238234
  simp only [CollatzResearch.WordTrace]
  refine ⟨38645273331902381396260439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103054062218406350390027837 38645273331902381396260439)
  ·
    refine ⟨57967909997853572094390659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38645273331902381396260439 57967909997853572094390659)
    ·
      refine ⟨86951864996780358141585989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57967909997853572094390659 86951864996780358141585989)
      ·
        refine ⟨16303474686896317151547373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86951864996780358141585989 16303474686896317151547373)
        ·
          refine ⟨6113803007586118931830265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16303474686896317151547373 6113803007586118931830265)
          ·
            refine ⟨4585352255689589198872699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6113803007586118931830265 4585352255689589198872699)
            ·
              refine ⟨6878028383534383798309049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4585352255689589198872699 6878028383534383798309049)
              ·
                refine ⟨5158521287650787848731787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6878028383534383798309049 5158521287650787848731787)
                ·
                  refine ⟨7737781931476181773097681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5158521287650787848731787 7737781931476181773097681)
                  ·
                    refine ⟨5803336448607136329823261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7737781931476181773097681 5803336448607136329823261)
                    ·
                      refine ⟨2176251168227676123683723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5803336448607136329823261 2176251168227676123683723)
                      ·
                        rfl

theorem cell23_4238234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_4238234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238234 prefixEnd_4238234 := by exact prefixLift 4238234
  have htrace : WordTrace (prefixWord ++ tailWord_4238234) baseStart_4238234 baseEnd_4238234 := by
    simpa [prefixWord, tailWord_4238234, baseEnd_4238234] using wordTrace_append hprefix tailTrace_4238234
  have hstable : (prefixWord ++ tailWord_4238234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238234).length < 2 ^ (prefixWord ++ tailWord_4238234).sum := by decide
  have hdescent : baseEnd_4238234 < baseStart_4238234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238247 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_4238247 : Nat := 118140960795 + 4238247 * 2 ^ 59
def prefixEnd_4238247 : Nat := 4983230072969 + 3 ^ 40 * 4238247 * 2
def baseEnd_4238247 : Nat := 2176257843476184572821163

theorem tailTrace_4238247 : CollatzResearch.WordTrace tailWord_4238247 prefixEnd_4238247 2176257843476184572821163 := by
  unfold tailWord_4238247
  simp only [CollatzResearch.WordTrace]
  refine ⟨154581567476562428805264995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103054378317708285870176663 154581567476562428805264995)
  ·
    refine ⟨231872351214843643207897493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154581567476562428805264995 231872351214843643207897493)
    ·
      refine ⟨10869016463195795775370195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 231872351214843643207897493 10869016463195795775370195)
      ·
        refine ⟨16303524694793693663055293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10869016463195795775370195 16303524694793693663055293)
        ·
          refine ⟨6113821760547635123645735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16303524694793693663055293 6113821760547635123645735)
          ·
            refine ⟨9170732640821452685468603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6113821760547635123645735 9170732640821452685468603)
            ·
              refine ⟨13756098961232179028202905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9170732640821452685468603 13756098961232179028202905)
              ·
                refine ⟨10317074220924134271152179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13756098961232179028202905 10317074220924134271152179)
                ·
                  refine ⟨15475611331386201406728269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10317074220924134271152179 15475611331386201406728269)
                  ·
                    refine ⟨5803354249269825527523101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15475611331386201406728269 5803354249269825527523101)
                    ·
                      refine ⟨2176257843476184572821163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5803354249269825527523101 2176257843476184572821163)
                      ·
                        rfl

theorem cell23_4238247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_4238247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238247 prefixEnd_4238247 := by exact prefixLift 4238247
  have htrace : WordTrace (prefixWord ++ tailWord_4238247) baseStart_4238247 baseEnd_4238247 := by
    simpa [prefixWord, tailWord_4238247, baseEnd_4238247] using wordTrace_append hprefix tailTrace_4238247
  have hstable : (prefixWord ++ tailWord_4238247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238247).length < 2 ^ (prefixWord ++ tailWord_4238247).sum := by decide
  have hdescent : baseEnd_4238247 < baseStart_4238247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238278 : List Nat := [6, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_4238278 : Nat := 118140960795 + 4238278 * 2 ^ 59
def prefixEnd_4238278 : Nat := 4983230072969 + 3 ^ 40 * 4238278 * 2
def baseEnd_4238278 : Nat := 2176273761376473951533521

theorem tailTrace_4238278 : CollatzResearch.WordTrace tailWord_4238278 prefixEnd_4238278 2176273761376473951533521 := by
  unfold tailWord_4238278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4830709316857816284363859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 103055132092966747399762325 4830709316857816284363859)
  ·
    refine ⟨7246063975286724426545789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4830709316857816284363859 7246063975286724426545789)
    ·
      refine ⟨2717273990732521659954671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7246063975286724426545789 2717273990732521659954671)
      ·
        refine ⟨4075910986098782489932007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717273990732521659954671 4075910986098782489932007)
        ·
          refine ⟨6113866479148173734898011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075910986098782489932007 6113866479148173734898011)
          ·
            refine ⟨9170799718722260602347017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6113866479148173734898011 9170799718722260602347017)
            ·
              refine ⟨6878099789041695451760263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9170799718722260602347017 6878099789041695451760263)
              ·
                refine ⟨10317149683562543177640395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6878099789041695451760263 10317149683562543177640395)
                ·
                  refine ⟨15475724525343814766460593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10317149683562543177640395 15475724525343814766460593)
                  ·
                    refine ⟨11606793394007861074845445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15475724525343814766460593 11606793394007861074845445)
                    ·
                      refine ⟨2176273761376473951533521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11606793394007861074845445 2176273761376473951533521)
                      ·
                        rfl

theorem cell23_4238278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_4238278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238278 prefixEnd_4238278 := by exact prefixLift 4238278
  have htrace : WordTrace (prefixWord ++ tailWord_4238278) baseStart_4238278 baseEnd_4238278 := by
    simpa [prefixWord, tailWord_4238278, baseEnd_4238278] using wordTrace_append hprefix tailTrace_4238278
  have hstable : (prefixWord ++ tailWord_4238278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238278).length < 2 ^ (prefixWord ++ tailWord_4238278).sum := by decide
  have hdescent : baseEnd_4238278 < baseStart_4238278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238280 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 2, 6]
def baseStart_4238280 : Nat := 118140960795 + 4238280 * 2 ^ 59
def prefixEnd_4238280 : Nat := 4983230072969 + 3 ^ 40 * 4238280 * 2
def baseEnd_4238280 : Nat := 725424929445927647902837

theorem tailTrace_4238280 : CollatzResearch.WordTrace tailWord_4238280 prefixEnd_4238280 725424929445927647902837 := by
  unfold tailWord_4238280
  simp only [CollatzResearch.WordTrace]
  refine ⟨77291385542721437720608147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103055180723628583627477529 77291385542721437720608147)
  ·
    refine ⟨115937078314082156580912221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77291385542721437720608147 115937078314082156580912221)
    ·
      refine ⟨43476404367780808717842083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115937078314082156580912221 43476404367780808717842083)
      ·
        refine ⟨65214606551671213076763125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43476404367780808717842083 65214606551671213076763125)
        ·
          refine ⟨6113869364219176225946543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 65214606551671213076763125 6113869364219176225946543)
          ·
            refine ⟨9170804046328764338919815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6113869364219176225946543 9170804046328764338919815)
            ·
              refine ⟨13756206069493146508379723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9170804046328764338919815 13756206069493146508379723)
              ·
                refine ⟨20634309104239719762569585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13756206069493146508379723 20634309104239719762569585)
                ·
                  refine ⟨15475731828179789821927189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20634309104239719762569585 15475731828179789821927189)
                  ·
                    refine ⟨725424929445927647902837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15475731828179789821927189 725424929445927647902837)
                    ·
                      rfl

theorem cell23_4238280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_4238280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238280 prefixEnd_4238280 := by exact prefixLift 4238280
  have htrace : WordTrace (prefixWord ++ tailWord_4238280) baseStart_4238280 baseEnd_4238280 := by
    simpa [prefixWord, tailWord_4238280, baseEnd_4238280] using wordTrace_append hprefix tailTrace_4238280
  have hstable : (prefixWord ++ tailWord_4238280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238280).length < 2 ^ (prefixWord ++ tailWord_4238280).sum := by decide
  have hdescent : baseEnd_4238280 < baseStart_4238280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238283 : List Nat := [1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 4]
def baseStart_4238283 : Nat := 118140960795 + 4238283 * 2 ^ 59
def prefixEnd_4238283 : Nat := 4983230072969 + 3 ^ 40 * 4238283 * 2
def baseEnd_4238283 : Nat := 2176276328779746431970997

theorem tailTrace_4238283 : CollatzResearch.WordTrace tailWord_4238283 prefixEnd_4238283 2176276328779746431970997 := by
  unfold tailWord_4238283
  simp only [CollatzResearch.WordTrace]
  refine ⟨154582880504432006953575503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103055253669621337969050335 154582880504432006953575503)
  ·
    refine ⟨231874320756648010430363255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154582880504432006953575503 231874320756648010430363255)
    ·
      refine ⟨347811481134972015645544883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231874320756648010430363255 347811481134972015645544883)
      ·
        refine ⟨521717221702458023468317325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347811481134972015645544883 521717221702458023468317325)
        ·
          refine ⟨195643958138421758800618997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 521717221702458023468317325 195643958138421758800618997)
          ·
            refine ⟨18341621075477039887558031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 195643958138421758800618997 18341621075477039887558031)
            ·
              refine ⟨27512431613215559831337047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18341621075477039887558031 27512431613215559831337047)
              ·
                refine ⟨41268647419823339747005571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27512431613215559831337047 41268647419823339747005571)
                ·
                  refine ⟨61902971129735009620508357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41268647419823339747005571 61902971129735009620508357)
                  ·
                    refine ⟨11606807086825314303845317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61902971129735009620508357 11606807086825314303845317)
                    ·
                      refine ⟨2176276328779746431970997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11606807086825314303845317 2176276328779746431970997)
                      ·
                        rfl

theorem cell23_4238283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 4].length) (baseStart_4238283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238283 prefixEnd_4238283 := by exact prefixLift 4238283
  have htrace : WordTrace (prefixWord ++ tailWord_4238283) baseStart_4238283 baseEnd_4238283 := by
    simpa [prefixWord, tailWord_4238283, baseEnd_4238283] using wordTrace_append hprefix tailTrace_4238283
  have hstable : (prefixWord ++ tailWord_4238283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238283).length < 2 ^ (prefixWord ++ tailWord_4238283).sum := by decide
  have hdescent : baseEnd_4238283 < baseStart_4238283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238287 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 1, 4, 2]
def baseStart_4238287 : Nat := 118140960795 + 4238287 * 2 ^ 59
def prefixEnd_4238287 : Nat := 4983230072969 + 3 ^ 40 * 4238287 * 2
def baseEnd_4238287 : Nat := 2176278382702364416320979

theorem tailTrace_4238287 : CollatzResearch.WordTrace tailWord_4238287 prefixEnd_4238287 2176278382702364416320979 := by
  unfold tailWord_4238287
  simp only [CollatzResearch.WordTrace]
  refine ⟨154583026396417515636721115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103055350930945010424480743 154583026396417515636721115)
  ·
    refine ⟨231874539594626273455081673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154583026396417515636721115 231874539594626273455081673)
    ·
      refine ⟨173905904695969705091311255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231874539594626273455081673 173905904695969705091311255)
      ·
        refine ⟨260858857043954557636966883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173905904695969705091311255 260858857043954557636966883)
        ·
          refine ⟨391288285565931836455450325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260858857043954557636966883 391288285565931836455450325)
          ·
            refine ⟨9170819192951527416924617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 391288285565931836455450325 9170819192951527416924617)
            ·
              refine ⟨6878114394713645562693463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9170819192951527416924617 6878114394713645562693463)
              ·
                refine ⟨10317171592070468344040195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6878114394713645562693463 10317171592070468344040195)
                ·
                  refine ⟨15475757388105702516060293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10317171592070468344040195 15475757388105702516060293)
                  ·
                    refine ⟨2901704510269819221761305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15475757388105702516060293 2901704510269819221761305)
                    ·
                      refine ⟨2176278382702364416320979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2901704510269819221761305 2176278382702364416320979)
                      ·
                        rfl

theorem cell23_4238287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 4, 2].length) (baseStart_4238287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238287 prefixEnd_4238287 := by exact prefixLift 4238287
  have htrace : WordTrace (prefixWord ++ tailWord_4238287) baseStart_4238287 baseEnd_4238287 := by
    simpa [prefixWord, tailWord_4238287, baseEnd_4238287] using wordTrace_append hprefix tailTrace_4238287
  have hstable : (prefixWord ++ tailWord_4238287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238287).length < 2 ^ (prefixWord ++ tailWord_4238287).sum := by decide
  have hdescent : baseEnd_4238287 < baseStart_4238287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238321 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 2, 2, 2]
def baseStart_4238321 : Nat := 118140960795 + 4238321 * 2 ^ 59
def prefixEnd_4238321 : Nat := 4983230072969 + 3 ^ 40 * 4238321 * 2
def baseEnd_4238321 : Nat := 2176295841044617283295823

theorem tailTrace_4238321 : CollatzResearch.WordTrace tailWord_4238321 prefixEnd_4238321 2176295841044617283295823 := by
  unfold tailWord_4238321
  simp only [CollatzResearch.WordTrace]
  refine ⟨154584266478294339443458817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103056177652196226295639211 154584266478294339443458817)
  ·
    refine ⟨115938199858720754582594113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154584266478294339443458817 115938199858720754582594113)
    ·
      refine ⟨86953649894040565936945585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115938199858720754582594113 86953649894040565936945585)
      ·
        refine ⟨65215237420530424452709189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86953649894040565936945585 65215237420530424452709189)
        ·
          refine ⟨12227857016349454584882973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 65215237420530424452709189 12227857016349454584882973)
          ·
            refine ⟨4585446381131045469331115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12227857016349454584882973 4585446381131045469331115)
            ·
              refine ⟨6878169571696568203996673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4585446381131045469331115 6878169571696568203996673)
              ·
                refine ⟨5158627178772426152997505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6878169571696568203996673 5158627178772426152997505)
                ·
                  refine ⟨3868970384079319614748129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5158627178772426152997505 3868970384079319614748129)
                  ·
                    refine ⟨2901727788059489711061097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3868970384079319614748129 2901727788059489711061097)
                    ·
                      refine ⟨2176295841044617283295823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2901727788059489711061097 2176295841044617283295823)
                      ·
                        rfl

theorem cell23_4238321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_4238321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238321 prefixEnd_4238321 := by exact prefixLift 4238321
  have htrace : WordTrace (prefixWord ++ tailWord_4238321) baseStart_4238321 baseEnd_4238321 := by
    simpa [prefixWord, tailWord_4238321, baseEnd_4238321] using wordTrace_append hprefix tailTrace_4238321
  have hstable : (prefixWord ++ tailWord_4238321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238321).length < 2 ^ (prefixWord ++ tailWord_4238321).sum := by decide
  have hdescent : baseEnd_4238321 < baseStart_4238321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238330 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2]
def baseStart_4238330 : Nat := 118140960795 + 4238330 * 2 ^ 59
def prefixEnd_4238330 : Nat := 4983230072969 + 3 ^ 40 * 4238330 * 2
def baseEnd_4238330 : Nat := 2176300462370507748083281

theorem tailTrace_4238330 : CollatzResearch.WordTrace tailWord_4238330 prefixEnd_4238330 2176300462370507748083281 := by
  unfold tailWord_4238330
  simp only [CollatzResearch.WordTrace]
  refine ⟨38646148683815433495134111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103056396490174489320357629 38646148683815433495134111)
  ·
    refine ⟨57969223025723150242701167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38646148683815433495134111 57969223025723150242701167)
    ·
      refine ⟨86953834538584725364051751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57969223025723150242701167 86953834538584725364051751)
      ·
        refine ⟨130430751807877088046077627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86953834538584725364051751 130430751807877088046077627)
        ·
          refine ⟨195646127711815632069116441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130430751807877088046077627 195646127711815632069116441)
          ·
            refine ⟨146734595783861724051837331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195646127711815632069116441 146734595783861724051837331)
            ·
              refine ⟨220101893675792586077755997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146734595783861724051837331 220101893675792586077755997)
              ·
                refine ⟨82538210128422219779158499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 220101893675792586077755997 82538210128422219779158499)
                ·
                  refine ⟨123807315192633329668737749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82538210128422219779158499 123807315192633329668737749)
                  ·
                    refine ⟨2901733949827343664111041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 123807315192633329668737749 2901733949827343664111041)
                    ·
                      refine ⟨2176300462370507748083281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2901733949827343664111041 2176300462370507748083281)
                      ·
                        rfl

theorem cell23_4238330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 7, 2].length) (baseStart_4238330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238330 prefixEnd_4238330 := by exact prefixLift 4238330
  have htrace : WordTrace (prefixWord ++ tailWord_4238330) baseStart_4238330 baseEnd_4238330 := by
    simpa [prefixWord, tailWord_4238330, baseEnd_4238330] using wordTrace_append hprefix tailTrace_4238330
  have hstable : (prefixWord ++ tailWord_4238330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238330).length < 2 ^ (prefixWord ++ tailWord_4238330).sum := by decide
  have hdescent : baseEnd_4238330 < baseStart_4238330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238333 : List Nat := [1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_4238333 : Nat := 118140960795 + 4238333 * 2 ^ 59
def prefixEnd_4238333 : Nat := 4983230072969 + 3 ^ 40 * 4238333 * 2
def baseEnd_4238333 : Nat := 2176302002812471236345767

theorem tailTrace_4238333 : CollatzResearch.WordTrace tailWord_4238333 prefixEnd_4238333 2176302002812471236345767 := by
  unfold tailWord_4238333
  simp only [CollatzResearch.WordTrace]
  refine ⟨154584704154250865492895653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103056469436167243661930435 154584704154250865492895653)
  ·
    refine ⟨28984632028922037279917935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 154584704154250865492895653 28984632028922037279917935)
    ·
      refine ⟨43476948043383055919876903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28984632028922037279917935 43476948043383055919876903)
      ·
        refine ⟨65215422065074583879815355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43476948043383055919876903 65215422065074583879815355)
        ·
          refine ⟨97823133097611875819723033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65215422065074583879815355 97823133097611875819723033)
          ·
            refine ⟨73367349823208906864792275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97823133097611875819723033 73367349823208906864792275)
            ·
              refine ⟨110051024734813360297188413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73367349823208906864792275 110051024734813360297188413)
              ·
                refine ⟨41269134275555010111445655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110051024734813360297188413 41269134275555010111445655)
                ·
                  refine ⟨61903701413332515167168483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41269134275555010111445655 61903701413332515167168483)
                  ·
                    refine ⟨92855552119998772750752725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61903701413332515167168483 92855552119998772750752725)
                    ·
                      refine ⟨2176302002812471236345767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92855552119998772750752725 2176302002812471236345767)
                      ·
                        rfl

theorem cell23_4238333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_4238333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238333 prefixEnd_4238333 := by exact prefixLift 4238333
  have htrace : WordTrace (prefixWord ++ tailWord_4238333) baseStart_4238333 baseEnd_4238333 := by
    simpa [prefixWord, tailWord_4238333, baseEnd_4238333] using wordTrace_append hprefix tailTrace_4238333
  have hstable : (prefixWord ++ tailWord_4238333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238333).length < 2 ^ (prefixWord ++ tailWord_4238333).sum := by decide
  have hdescent : baseEnd_4238333 < baseStart_4238333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238338 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4238338 : Nat := 118140960795 + 4238338 * 2 ^ 59
def prefixEnd_4238338 : Nat := 4983230072969 + 3 ^ 40 * 4238338 * 2
def baseEnd_4238338 : Nat := 2176304570215743716783245

theorem tailTrace_4238338 : CollatzResearch.WordTrace tailWord_4238338 prefixEnd_4238338 2176304570215743716783245 := by
  unfold tailWord_4238338
  simp only [CollatzResearch.WordTrace]
  refine ⟨38646221629808187836706917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103056591012821834231218445 38646221629808187836706917)
  ·
    refine ⟨7246166555589035219382547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38646221629808187836706917 7246166555589035219382547)
    ·
      refine ⟨10869249833383552829073821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7246166555589035219382547 10869249833383552829073821)
      ·
        refine ⟨4075968687518832310902683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10869249833383552829073821 4075968687518832310902683)
        ·
          refine ⟨6113953031278248466354025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4075968687518832310902683 6113953031278248466354025)
          ·
            refine ⟨4585464773458686349765519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6113953031278248466354025 4585464773458686349765519)
            ·
              refine ⟨6878197160188029524648279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4585464773458686349765519 6878197160188029524648279)
              ·
                refine ⟨10317295740282044286972419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6878197160188029524648279 10317295740282044286972419)
                ·
                  refine ⟨15475943610423066430458629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10317295740282044286972419 15475943610423066430458629)
                  ·
                    refine ⟨2901739426954324955710993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15475943610423066430458629 2901739426954324955710993)
                    ·
                      refine ⟨2176304570215743716783245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2901739426954324955710993 2176304570215743716783245)
                      ·
                        rfl

theorem cell23_4238338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4238338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238338 prefixEnd_4238338 := by exact prefixLift 4238338
  have htrace : WordTrace (prefixWord ++ tailWord_4238338) baseStart_4238338 baseEnd_4238338 := by
    simpa [prefixWord, tailWord_4238338, baseEnd_4238338] using wordTrace_append hprefix tailTrace_4238338
  have hstable : (prefixWord ++ tailWord_4238338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238338).length < 2 ^ (prefixWord ++ tailWord_4238338).sum := by decide
  have hdescent : baseEnd_4238338 < baseStart_4238338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238360 : List Nat := [2, 1, 2, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_4238360 : Nat := 118140960795 + 4238360 * 2 ^ 59
def prefixEnd_4238360 : Nat := 4983230072969 + 3 ^ 40 * 4238360 * 2
def baseEnd_4238360 : Nat := 2176315866790142630708143

theorem tailTrace_4238360 : CollatzResearch.WordTrace tailWord_4238360 prefixEnd_4238360 2176315866790142630708143 := by
  unfold tailWord_4238360
  simp only [CollatzResearch.WordTrace]
  refine ⟨77292844462576524552064267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103057125950102032736085689 77292844462576524552064267)
  ·
    refine ⟨115939266693864786828096401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77292844462576524552064267 115939266693864786828096401)
    ·
      refine ⟨86954450020398590121072301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115939266693864786828096401 86954450020398590121072301)
      ·
        refine ⟨32607918757649471295402113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86954450020398590121072301 32607918757649471295402113)
        ·
          refine ⟨24455939068237103471551585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32607918757649471295402113 24455939068237103471551585)
          ·
            refine ⟨18341954301177827603663689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24455939068237103471551585 18341954301177827603663689)
            ·
              refine ⟨13756465725883370702747767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18341954301177827603663689 13756465725883370702747767)
              ·
                refine ⟨20634698588825056054121651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13756465725883370702747767 20634698588825056054121651)
                ·
                  refine ⟨30952047883237584081182477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20634698588825056054121651 30952047883237584081182477)
                  ·
                    refine ⟨11607017956214094030443429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30952047883237584081182477 11607017956214094030443429)
                    ·
                      refine ⟨2176315866790142630708143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11607017956214094030443429 2176315866790142630708143)
                      ·
                        rfl

theorem cell23_4238360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_4238360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238360 prefixEnd_4238360 := by exact prefixLift 4238360
  have htrace : WordTrace (prefixWord ++ tailWord_4238360) baseStart_4238360 baseEnd_4238360 := by
    simpa [prefixWord, tailWord_4238360, baseEnd_4238360] using wordTrace_append hprefix tailTrace_4238360
  have hstable : (prefixWord ++ tailWord_4238360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238360).length < 2 ^ (prefixWord ++ tailWord_4238360).sum := by decide
  have hdescent : baseEnd_4238360 < baseStart_4238360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238400 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 6]
def baseStart_4238400 : Nat := 118140960795 + 4238400 * 2 ^ 59
def prefixEnd_4238400 : Nat := 4983230072969 + 3 ^ 40 * 4238400 * 2
def baseEnd_4238400 : Nat := 241815156224035830467551

theorem tailTrace_4238400 : CollatzResearch.WordTrace tailWord_4238400 prefixEnd_4238400 241815156224035830467551 := by
  unfold tailWord_4238400
  simp only [CollatzResearch.WordTrace]
  refine ⟨77293573922504067967792327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103058098563338757290389769 77293573922504067967792327)
  ·
    refine ⟨115940360883756101951688491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77293573922504067967792327 115940360883756101951688491)
    ·
      refine ⟨173910541325634152927532737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115940360883756101951688491 173910541325634152927532737)
      ·
        refine ⟨130432905994225614695649553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 173910541325634152927532737 130432905994225614695649553)
        ·
          refine ⟨97824679495669211021737165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 130432905994225614695649553 97824679495669211021737165)
          ·
            refine ⟨36684254810875954133151437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97824679495669211021737165 36684254810875954133151437)
            ·
              refine ⟨13756595554078482799931789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36684254810875954133151437 13756595554078482799931789)
              ·
                refine ⟨5158723332779431049974421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13756595554078482799931789 5158723332779431049974421)
                ·
                  refine ⟨241815156224035830467551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5158723332779431049974421 241815156224035830467551)
                  ·
                    rfl

theorem cell23_4238400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 6].length) (baseStart_4238400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238400 prefixEnd_4238400 := by exact prefixLift 4238400
  have htrace : WordTrace (prefixWord ++ tailWord_4238400) baseStart_4238400 baseEnd_4238400 := by
    simpa [prefixWord, tailWord_4238400, baseEnd_4238400] using wordTrace_append hprefix tailTrace_4238400
  have hstable : (prefixWord ++ tailWord_4238400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238400).length < 2 ^ (prefixWord ++ tailWord_4238400).sum := by decide
  have hdescent : baseEnd_4238400 < baseStart_4238400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238410 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_4238410 : Nat := 118140960795 + 4238410 * 2 ^ 59
def prefixEnd_4238410 : Nat := 4983230072969 + 3 ^ 40 * 4238410 * 2
def baseEnd_4238410 : Nat := 2176341540822867435082913

theorem tailTrace_4238410 : CollatzResearch.WordTrace tailWord_4238410 prefixEnd_4238410 2176341540822867435082913 := by
  unfold tailWord_4238410
  simp only [CollatzResearch.WordTrace]
  refine ⟨38646878143742976910862171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103058341716647938428965789 38646878143742976910862171)
  ·
    refine ⟨57970317215614465366293257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38646878143742976910862171 57970317215614465366293257)
    ·
      refine ⟨43477737911710849024719943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57970317215614465366293257 43477737911710849024719943)
      ·
        refine ⟨65216606867566273537079915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43477737911710849024719943 65216606867566273537079915)
        ·
          refine ⟨97824910301349410305619873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65216606867566273537079915 97824910301349410305619873)
          ·
            refine ⟨73368682726012057729214905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97824910301349410305619873 73368682726012057729214905)
            ·
              refine ⟨55026512044509043296911179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73368682726012057729214905 55026512044509043296911179)
              ·
                refine ⟨82539768066763564945366769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55026512044509043296911179 82539768066763564945366769)
                ·
                  refine ⟨61904826050072673709025077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82539768066763564945366769 61904826050072673709025077)
                  ·
                    refine ⟨5803577442194313160221101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61904826050072673709025077 5803577442194313160221101)
                    ·
                      refine ⟨2176341540822867435082913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5803577442194313160221101 2176341540822867435082913)
                      ·
                        rfl

theorem cell23_4238410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_4238410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238410 prefixEnd_4238410 := by exact prefixLift 4238410
  have htrace : WordTrace (prefixWord ++ tailWord_4238410) baseStart_4238410 baseEnd_4238410 := by
    simpa [prefixWord, tailWord_4238410, baseEnd_4238410] using wordTrace_append hprefix tailTrace_4238410
  have hstable : (prefixWord ++ tailWord_4238410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238410).length < 2 ^ (prefixWord ++ tailWord_4238410).sum := by decide
  have hdescent : baseEnd_4238410 < baseStart_4238410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238434 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 6]
def baseStart_4238434 : Nat := 118140960795 + 4238434 * 2 ^ 59
def prefixEnd_4238434 : Nat := 4983230072969 + 3 ^ 40 * 4238434 * 2
def baseEnd_4238434 : Nat := 241817096039841704575867

theorem tailTrace_4238434 : CollatzResearch.WordTrace tailWord_4238434 prefixEnd_4238434 241817096039841704575867 := by
  unfold tailWord_4238434
  simp only [CollatzResearch.WordTrace]
  refine ⟨38647096981721239935580589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103058925284589973161548237 38647096981721239935580589)
  ·
    refine ⟨14492661368145464975842721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38647096981721239935580589 14492661368145464975842721)
    ·
      refine ⟨10869496026109098731882041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14492661368145464975842721 10869496026109098731882041)
      ·
        refine ⟨8152122019581824048911531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10869496026109098731882041 8152122019581824048911531)
        ·
          refine ⟨12228183029372736073367297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8152122019581824048911531 12228183029372736073367297)
          ·
            refine ⟨9171137272029552055025473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12228183029372736073367297 9171137272029552055025473)
            ·
              refine ⟨6878352954022164041269105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9171137272029552055025473 6878352954022164041269105)
              ·
                refine ⟨5158764715516623030951829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6878352954022164041269105 5158764715516623030951829)
                ·
                  refine ⟨241817096039841704575867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5158764715516623030951829 241817096039841704575867)
                  ·
                    rfl

theorem cell23_4238434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_4238434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238434 prefixEnd_4238434 := by exact prefixLift 4238434
  have htrace : WordTrace (prefixWord ++ tailWord_4238434) baseStart_4238434 baseEnd_4238434 := by
    simpa [prefixWord, tailWord_4238434, baseEnd_4238434] using wordTrace_append hprefix tailTrace_4238434
  have hstable : (prefixWord ++ tailWord_4238434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238434).length < 2 ^ (prefixWord ++ tailWord_4238434).sum := by decide
  have hdescent : baseEnd_4238434 < baseStart_4238434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238454 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_4238454 : Nat := 118140960795 + 4238454 * 2 ^ 59
def prefixEnd_4238454 : Nat := 4983230072969 + 3 ^ 40 * 4238454 * 2
def baseEnd_4238454 : Nat := 2176364133971665262932711

theorem tailTrace_4238454 : CollatzResearch.WordTrace tailWord_4238454 prefixEnd_4238454 2176364133971665262932711 := by
  unfold tailWord_4238454
  simp only [CollatzResearch.WordTrace]
  refine ⟨9661819836675781447378151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 103059411591208335438700277 9661819836675781447378151)
  ·
    refine ⟨14492729755013672171067227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9661819836675781447378151 14492729755013672171067227)
    ·
      refine ⟨21739094632520508256600841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14492729755013672171067227 21739094632520508256600841)
      ·
        refine ⟨16304320974390381192450631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21739094632520508256600841 16304320974390381192450631)
        ·
          refine ⟨24456481461585571788675947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16304320974390381192450631 24456481461585571788675947)
          ·
            refine ⟨36684722192378357683013921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24456481461585571788675947 36684722192378357683013921)
            ·
              refine ⟨27513541644283768262260441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36684722192378357683013921 27513541644283768262260441)
              ·
                refine ⟨20635156233212826196695331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27513541644283768262260441 20635156233212826196695331)
                ·
                  refine ⟨30952734349819239295042997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20635156233212826196695331 30952734349819239295042997)
                  ·
                    refine ⟨2901818845295553683910281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30952734349819239295042997 2901818845295553683910281)
                    ·
                      refine ⟨2176364133971665262932711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2901818845295553683910281 2176364133971665262932711)
                      ·
                        rfl

theorem cell23_4238454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_4238454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238454 prefixEnd_4238454 := by exact prefixLift 4238454
  have htrace : WordTrace (prefixWord ++ tailWord_4238454) baseStart_4238454 baseEnd_4238454 := by
    simpa [prefixWord, tailWord_4238454, baseEnd_4238454] using wordTrace_append hprefix tailTrace_4238454
  have hstable : (prefixWord ++ tailWord_4238454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238454).length < 2 ^ (prefixWord ++ tailWord_4238454).sum := by decide
  have hdescent : baseEnd_4238454 < baseStart_4238454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238467 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 4]
def baseStart_4238467 : Nat := 118140960795 + 4238467 * 2 ^ 59
def prefixEnd_4238467 : Nat := 4983230072969 + 3 ^ 40 * 4238467 * 2
def baseEnd_4238467 : Nat := 2176370809220173712070151

theorem tailTrace_4238467 : CollatzResearch.WordTrace tailWord_4238467 prefixEnd_4238467 2176370809220173712070151 := by
  unfold tailWord_4238467
  simp only [CollatzResearch.WordTrace]
  refine ⟨154589591535765406378273655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103059727690510270918849103 154589591535765406378273655)
  ·
    refine ⟨231884387303648109567410483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154589591535765406378273655 231884387303648109567410483)
    ·
      refine ⟨347826580955472164351115725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231884387303648109567410483 347826580955472164351115725)
      ·
        refine ⟨130434967858302061631668397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 347826580955472164351115725 130434967858302061631668397)
        ·
          refine ⟨48913112946863273111875649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 130434967858302061631668397 48913112946863273111875649)
          ·
            refine ⟨36684834710147454833906737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48913112946863273111875649 36684834710147454833906737)
            ·
              refine ⟨27513626032610591125430053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36684834710147454833906737 27513626032610591125430053)
              ·
                refine ⟨5158804881114485836018135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27513626032610591125430053 5158804881114485836018135)
                ·
                  refine ⟨7738207321671728754027203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5158804881114485836018135 7738207321671728754027203)
                  ·
                    refine ⟨11607310982507593131040805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7738207321671728754027203 11607310982507593131040805)
                    ·
                      refine ⟨2176370809220173712070151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11607310982507593131040805 2176370809220173712070151)
                      ·
                        rfl

theorem cell23_4238467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_4238467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238467 prefixEnd_4238467 := by exact prefixLift 4238467
  have htrace : WordTrace (prefixWord ++ tailWord_4238467) baseStart_4238467 baseEnd_4238467 := by
    simpa [prefixWord, tailWord_4238467, baseEnd_4238467] using wordTrace_append hprefix tailTrace_4238467
  have hstable : (prefixWord ++ tailWord_4238467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238467).length < 2 ^ (prefixWord ++ tailWord_4238467).sum := by decide
  have hdescent : baseEnd_4238467 < baseStart_4238467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238478 : List Nat := [4, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3]
def baseStart_4238478 : Nat := 118140960795 + 4238478 * 2 ^ 59
def prefixEnd_4238478 : Nat := 4983230072969 + 3 ^ 40 * 4238478 * 2
def baseEnd_4238478 : Nat := 2176376457507373169032601

theorem tailTrace_4238478 : CollatzResearch.WordTrace tailWord_4238478 prefixEnd_4238478 2176376457507373169032601 := by
  unfold tailWord_4238478
  simp only [CollatzResearch.WordTrace]
  refine ⟨19323749092340694407115511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 103059995159150370171282725 19323749092340694407115511)
  ·
    refine ⟨28985623638511041610673267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19323749092340694407115511 28985623638511041610673267)
    ·
      refine ⟨43478435457766562416009901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28985623638511041610673267 43478435457766562416009901)
      ·
        refine ⟨16304413296662460906003713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43478435457766562416009901 16304413296662460906003713)
        ·
          refine ⟨12228309972496845679502785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16304413296662460906003713 12228309972496845679502785)
          ·
            refine ⟨9171232479372634259627089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12228309972496845679502785 9171232479372634259627089)
            ·
              refine ⟨6878424359529475694720317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9171232479372634259627089 6878424359529475694720317)
              ·
                refine ⟨2579409134823553385520119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6878424359529475694720317 2579409134823553385520119)
                ·
                  refine ⟨3869113702235330078280179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2579409134823553385520119 3869113702235330078280179)
                  ·
                    refine ⟨5803670553352995117420269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3869113702235330078280179 5803670553352995117420269)
                    ·
                      refine ⟨2176376457507373169032601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5803670553352995117420269 2176376457507373169032601)
                      ·
                        rfl

theorem cell23_4238478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_4238478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238478 prefixEnd_4238478 := by exact prefixLift 4238478
  have htrace : WordTrace (prefixWord ++ tailWord_4238478) baseStart_4238478 baseEnd_4238478 := by
    simpa [prefixWord, tailWord_4238478, baseEnd_4238478] using wordTrace_append hprefix tailTrace_4238478
  have hstable : (prefixWord ++ tailWord_4238478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238478).length < 2 ^ (prefixWord ++ tailWord_4238478).sum := by decide
  have hdescent : baseEnd_4238478 < baseStart_4238478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238480 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 4]
def baseStart_4238480 : Nat := 118140960795 + 4238480 * 2 ^ 59
def prefixEnd_4238480 : Nat := 4983230072969 + 3 ^ 40 * 4238480 * 2
def baseEnd_4238480 : Nat := 2176377484468682161207591

theorem tailTrace_4238480 : CollatzResearch.WordTrace tailWord_4238480 prefixEnd_4238480 2176377484468682161207591 := by
  unfold tailWord_4238480
  simp only [CollatzResearch.WordTrace]
  refine ⟨77295032842359154799248447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103060043789812206398997929 77295032842359154799248447)
  ·
    refine ⟨115942549263538732198872671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77295032842359154799248447 115942549263538732198872671)
    ·
      refine ⟨173913823895308098298309007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115942549263538732198872671 173913823895308098298309007)
      ·
        refine ⟨260870735842962147447463511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 173913823895308098298309007 260870735842962147447463511)
        ·
          refine ⟨391306103764443221171195267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260870735842962147447463511 391306103764443221171195267)
          ·
            refine ⟨586959155646664831756792901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 391306103764443221171195267 586959155646664831756792901)
            ·
              refine ⟨110054841683749655954398669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 586959155646664831756792901 110054841683749655954398669)
              ·
                refine ⟨41270565631406120982899501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 110054841683749655954398669 41270565631406120982899501)
                ·
                  refine ⟨15476462111777295368587313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41270565631406120982899501 15476462111777295368587313)
                  ·
                    refine ⟨11607346583832971526440485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15476462111777295368587313 11607346583832971526440485)
                    ·
                      refine ⟨2176377484468682161207591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11607346583832971526440485 2176377484468682161207591)
                      ·
                        rfl

theorem cell23_4238480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_4238480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238480 prefixEnd_4238480 := by exact prefixLift 4238480
  have htrace : WordTrace (prefixWord ++ tailWord_4238480) baseStart_4238480 baseEnd_4238480 := by
    simpa [prefixWord, tailWord_4238480, baseEnd_4238480] using wordTrace_append hprefix tailTrace_4238480
  have hstable : (prefixWord ++ tailWord_4238480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238480).length < 2 ^ (prefixWord ++ tailWord_4238480).sum := by decide
  have hdescent : baseEnd_4238480 < baseStart_4238480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238501 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 3, 2, 2]
def baseStart_4238501 : Nat := 118140960795 + 4238501 * 2 ^ 59
def prefixEnd_4238501 : Nat := 4983230072969 + 3 ^ 40 * 4238501 * 2
def baseEnd_4238501 : Nat := 2176388267562426579044995

theorem tailTrace_4238501 : CollatzResearch.WordTrace tailWord_4238501 prefixEnd_4238501 2176388267562426579044995 := by
  unfold tailWord_4238501
  simp only [CollatzResearch.WordTrace]
  refine ⟨154590831617642230185011357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103060554411761486790007571 154590831617642230185011357)
  ·
    refine ⟨57971561856615836319379259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154590831617642230185011357 57971561856615836319379259)
    ·
      refine ⟨86957342784923754479068889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57971561856615836319379259 86957342784923754479068889)
      ·
        refine ⟨65218007088692815859301667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86957342784923754479068889 65218007088692815859301667)
        ·
          refine ⟨97827010633039223788952501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65218007088692815859301667 97827010633039223788952501)
          ·
            refine ⟨9171282246847427230214297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97827010633039223788952501 9171282246847427230214297)
            ·
              refine ⟨6878461685135570422660723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9171282246847427230214297 6878461685135570422660723)
              ·
                refine ⟨10317692527703355633991085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6878461685135570422660723 10317692527703355633991085)
                ·
                  refine ⟨3869134697888758362746657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10317692527703355633991085 3869134697888758362746657)
                  ·
                    refine ⟨2901851023416568772059993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3869134697888758362746657 2901851023416568772059993)
                    ·
                      refine ⟨2176388267562426579044995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2901851023416568772059993 2176388267562426579044995)
                      ·
                        rfl

theorem cell23_4238501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 3, 2, 2].length) (baseStart_4238501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238501 prefixEnd_4238501 := by exact prefixLift 4238501
  have htrace : WordTrace (prefixWord ++ tailWord_4238501) baseStart_4238501 baseEnd_4238501 := by
    simpa [prefixWord, tailWord_4238501, baseEnd_4238501] using wordTrace_append hprefix tailTrace_4238501
  have hstable : (prefixWord ++ tailWord_4238501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238501).length < 2 ^ (prefixWord ++ tailWord_4238501).sum := by decide
  have hdescent : baseEnd_4238501 < baseStart_4238501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238514 : List Nat := [3, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_4238514 : Nat := 118140960795 + 4238514 * 2 ^ 59
def prefixEnd_4238514 : Nat := 4983230072969 + 3 ^ 40 * 4238514 * 2
def baseEnd_4238514 : Nat := 2176394942810935028182435

theorem tailTrace_4238514 : CollatzResearch.WordTrace tailWord_4238514 prefixEnd_4238514 2176394942810935028182435 := by
  unfold tailWord_4238514
  simp only [CollatzResearch.WordTrace]
  refine ⟨38647826441648783351308649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103060870511063422270156397 38647826441648783351308649)
  ·
    refine ⟨28985869831236587513481487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38647826441648783351308649 28985869831236587513481487)
    ·
      refine ⟨43478804746854881270222231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28985869831236587513481487 43478804746854881270222231)
      ·
        refine ⟨65218207120282321905333347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43478804746854881270222231 65218207120282321905333347)
        ·
          refine ⟨97827310680423482858000021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65218207120282321905333347 97827310680423482858000021)
          ·
            refine ⟨4585655188144850758968751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97827310680423482858000021 4585655188144850758968751)
            ·
              refine ⟨6878482782217276138453127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4585655188144850758968751 6878482782217276138453127)
              ·
                refine ⟨10317724173325914207679691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6878482782217276138453127 10317724173325914207679691)
                ·
                  refine ⟨15476586259988871311519537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10317724173325914207679691 15476586259988871311519537)
                  ·
                    refine ⟨11607439694991653483639653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15476586259988871311519537 11607439694991653483639653)
                    ·
                      refine ⟨2176394942810935028182435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11607439694991653483639653 2176394942810935028182435)
                      ·
                        rfl

theorem cell23_4238514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_4238514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238514 prefixEnd_4238514 := by exact prefixLift 4238514
  have htrace : WordTrace (prefixWord ++ tailWord_4238514) baseStart_4238514 baseEnd_4238514 := by
    simpa [prefixWord, tailWord_4238514, baseEnd_4238514] using wordTrace_append hprefix tailTrace_4238514
  have hstable : (prefixWord ++ tailWord_4238514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238514).length < 2 ^ (prefixWord ++ tailWord_4238514).sum := by decide
  have hdescent : baseEnd_4238514 < baseStart_4238514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238524 : List Nat := [2, 2, 2, 3, 2, 3, 2, 7]
def baseStart_4238524 : Nat := 118140960795 + 4238524 * 2 ^ 59
def prefixEnd_4238524 : Nat := 4983230072969 + 3 ^ 40 * 4238524 * 2
def baseEnd_4238524 : Nat := 80607410282128888483607

theorem tailTrace_4238524 : CollatzResearch.WordTrace tailWord_4238524 prefixEnd_4238524 80607410282128888483607 := by
  unfold tailWord_4238524
  simp only [CollatzResearch.WordTrace]
  refine ⟨77295835248279452556549313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103061113664372603408732417 77295835248279452556549313)
  ·
    refine ⟨57971876436209589417411985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77295835248279452556549313 57971876436209589417411985)
    ·
      refine ⟨43478907327157192063058989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57971876436209589417411985 43478907327157192063058989)
      ·
        refine ⟨16304590247683947023647121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43478907327157192063058989 16304590247683947023647121)
        ·
          refine ⟨12228442685762960267735341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16304590247683947023647121 12228442685762960267735341)
          ·
            refine ⟨4585666007161110100400753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12228442685762960267735341 4585666007161110100400753)
            ·
              refine ⟨3439249505370832575300565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4585666007161110100400753 3439249505370832575300565)
              ·
                refine ⟨80607410282128888483607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3439249505370832575300565 80607410282128888483607)
                ·
                  rfl

theorem cell23_4238524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 7].length) (baseStart_4238524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238524 prefixEnd_4238524 := by exact prefixLift 4238524
  have htrace : WordTrace (prefixWord ++ tailWord_4238524) baseStart_4238524 baseEnd_4238524 := by
    simpa [prefixWord, tailWord_4238524, baseEnd_4238524] using wordTrace_append hprefix tailTrace_4238524
  have hstable : (prefixWord ++ tailWord_4238524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238524).length < 2 ^ (prefixWord ++ tailWord_4238524).sum := by decide
  have hdescent : baseEnd_4238524 < baseStart_4238524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238541 : List Nat := [1, 6, 2, 2, 1, 2, 9]
def baseStart_4238541 : Nat := 118140960795 + 4238541 * 2 ^ 59
def prefixEnd_4238541 : Nat := 4983230072969 + 3 ^ 40 * 4238541 * 2
def baseEnd_4238541 : Nat := 26869244528254400278331

theorem tailTrace_4238541 : CollatzResearch.WordTrace tailWord_4238541 prefixEnd_4238541 26869244528254400278331 := by
  unfold tailWord_4238541
  simp only [CollatzResearch.WordTrace]
  refine ⟨154592290537497317016467477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103061527024998211344311651 154592290537497317016467477)
  ·
    refine ⟨7246513618945186735146913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 154592290537497317016467477 7246513618945186735146913)
    ·
      refine ⟨5434885214208890051360185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7246513618945186735146913 5434885214208890051360185)
      ·
        refine ⟨4076163910656667538520139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5434885214208890051360185 4076163910656667538520139)
        ·
          refine ⟨6114245865985001307780209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4076163910656667538520139 6114245865985001307780209)
          ·
            refine ⟨4585684399488750980835157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6114245865985001307780209 4585684399488750980835157)
            ·
              refine ⟨26869244528254400278331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4585684399488750980835157 26869244528254400278331)
              ·
                rfl

theorem cell23_4238541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 9].length) (baseStart_4238541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238541 prefixEnd_4238541 := by exact prefixLift 4238541
  have htrace : WordTrace (prefixWord ++ tailWord_4238541) baseStart_4238541 baseEnd_4238541 := by
    simpa [prefixWord, tailWord_4238541, baseEnd_4238541] using wordTrace_append hprefix tailTrace_4238541
  have hstable : (prefixWord ++ tailWord_4238541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238541).length < 2 ^ (prefixWord ++ tailWord_4238541).sum := by decide
  have hdescent : baseEnd_4238541 < baseStart_4238541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238644 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_4238644 : Nat := 118140960795 + 4238644 * 2 ^ 59
def prefixEnd_4238644 : Nat := 4983230072969 + 3 ^ 40 * 4238644 * 2
def baseEnd_4238644 : Nat := 725487231765339839852279

theorem tailTrace_4238644 : CollatzResearch.WordTrace tailWord_4238644 prefixEnd_4238644 725487231765339839852279 := by
  unfold tailWord_4238644
  simp only [CollatzResearch.WordTrace]
  refine ⟨77298023628062082803733493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103064031504082777071644657 77298023628062082803733493)
  ·
    refine ⟨7246689715130820262850015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 77298023628062082803733493 7246689715130820262850015)
    ·
      refine ⟨10870034572696230394275023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7246689715130820262850015 10870034572696230394275023)
      ·
        refine ⟨16305051859044345591412535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10870034572696230394275023 16305051859044345591412535)
        ·
          refine ⟨24457577788566518387118803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16305051859044345591412535 24457577788566518387118803)
          ·
            refine ⟨36686366682849777580678205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24457577788566518387118803 36686366682849777580678205)
            ·
              refine ⟨13757387506068666592754327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36686366682849777580678205 13757387506068666592754327)
              ·
                refine ⟨20636081259102999889131491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13757387506068666592754327 20636081259102999889131491)
                ·
                  refine ⟨30954121888654499833697237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20636081259102999889131491 30954121888654499833697237)
                  ·
                    refine ⟨725487231765339839852279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30954121888654499833697237 725487231765339839852279)
                    ·
                      rfl

theorem cell23_4238644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_4238644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238644 prefixEnd_4238644 := by exact prefixLift 4238644
  have htrace : WordTrace (prefixWord ++ tailWord_4238644) baseStart_4238644 baseEnd_4238644 := by
    simpa [prefixWord, tailWord_4238644, baseEnd_4238644] using wordTrace_append hprefix tailTrace_4238644
  have hstable : (prefixWord ++ tailWord_4238644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238644).length < 2 ^ (prefixWord ++ tailWord_4238644).sum := by decide
  have hdescent : baseEnd_4238644 < baseStart_4238644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238738 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 6]
def baseStart_4238738 : Nat := 118140960795 + 4238738 * 2 ^ 59
def prefixEnd_4238738 : Nat := 4983230072969 + 3 ^ 40 * 4238738 * 2
def baseEnd_4238738 : Nat := 241834440275282461309045

theorem tailTrace_4238738 : CollatzResearch.WordTrace tailWord_4238738 prefixEnd_4238738 241834440275282461309045 := by
  unfold tailWord_4238738
  simp only [CollatzResearch.WordTrace]
  refine ⟨38649868929445904915347217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103066317145189079774259245 38649868929445904915347217)
  ·
    refine ⟨28987401697084428686510413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38649868929445904915347217 28987401697084428686510413)
    ·
      refine ⟨10870275636406660757441405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28987401697084428686510413 10870275636406660757441405)
      ·
        refine ⟨4076353363652497784040527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10870275636406660757441405 4076353363652497784040527)
        ·
          refine ⟨6114530045478746676060791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4076353363652497784040527 6114530045478746676060791)
          ·
            refine ⟨9171795068218120014091187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6114530045478746676060791 9171795068218120014091187)
            ·
              refine ⟨13757692602327180021136781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9171795068218120014091187 13757692602327180021136781)
              ·
                refine ⟨5159134725872692507926293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13757692602327180021136781 5159134725872692507926293)
                ·
                  refine ⟨241834440275282461309045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5159134725872692507926293 241834440275282461309045)
                  ·
                    rfl

theorem cell23_4238738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_4238738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238738 prefixEnd_4238738 := by exact prefixLift 4238738
  have htrace : WordTrace (prefixWord ++ tailWord_4238738) baseStart_4238738 baseEnd_4238738 := by
    simpa [prefixWord, tailWord_4238738, baseEnd_4238738] using wordTrace_append hprefix tailTrace_4238738
  have hstable : (prefixWord ++ tailWord_4238738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238738).length < 2 ^ (prefixWord ++ tailWord_4238738).sum := by decide
  have hdescent : baseEnd_4238738 < baseStart_4238738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238751 : List Nat := [1, 1, 2, 5, 1, 2, 3, 2, 1, 5]
def baseStart_4238751 : Nat := 118140960795 + 4238751 * 2 ^ 59
def prefixEnd_4238751 : Nat := 4983230072969 + 3 ^ 40 * 4238751 * 2
def baseEnd_4238751 : Nat := 725505545908683533639615

theorem tailTrace_4238751 : CollatzResearch.WordTrace tailWord_4238751 prefixEnd_4238751 725505545908683533639615 := by
  unfold tailWord_4238751
  simp only [CollatzResearch.WordTrace]
  refine ⟨154599949866736522881612107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103066633244491015254408071 154599949866736522881612107)
  ·
    refine ⟨231899924800104784322418161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154599949866736522881612107 231899924800104784322418161)
    ·
      refine ⟨173924943600078588241813621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 231899924800104784322418161 173924943600078588241813621)
      ·
        refine ⟨16305463462507367647670027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 173924943600078588241813621 16305463462507367647670027)
        ·
          refine ⟨24458195193761051471505041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16305463462507367647670027 24458195193761051471505041)
          ·
            refine ⟨18343646395320788603628781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24458195193761051471505041 18343646395320788603628781)
            ·
              refine ⟨6878867398245295726360793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18343646395320788603628781 6878867398245295726360793)
              ·
                refine ⟨5159150548683971794770595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6878867398245295726360793 5159150548683971794770595)
                ·
                  refine ⟨7738725823025957692155893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5159150548683971794770595 7738725823025957692155893)
                  ·
                    refine ⟨725505545908683533639615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7738725823025957692155893 725505545908683533639615)
                    ·
                      rfl

theorem cell23_4238751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 5].length) (baseStart_4238751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238751 prefixEnd_4238751 := by exact prefixLift 4238751
  have htrace : WordTrace (prefixWord ++ tailWord_4238751) baseStart_4238751 baseEnd_4238751 := by
    simpa [prefixWord, tailWord_4238751, baseEnd_4238751] using wordTrace_append hprefix tailTrace_4238751
  have hstable : (prefixWord ++ tailWord_4238751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238751).length < 2 ^ (prefixWord ++ tailWord_4238751).sum := by decide
  have hdescent : baseEnd_4238751 < baseStart_4238751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238764 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 6, 4]
def baseStart_4238764 : Nat := 118140960795 + 4238764 * 2 ^ 59
def prefixEnd_4238764 : Nat := 4983230072969 + 3 ^ 40 * 4238764 * 2
def baseEnd_4238764 : Nat := 725507770991519683352095

theorem tailTrace_4238764 : CollatzResearch.WordTrace tailWord_4238764 prefixEnd_4238764 725507770991519683352095 := by
  unfold tailWord_4238764
  simp only [CollatzResearch.WordTrace]
  refine ⟨77300212007844713050917673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103066949343792950734556897 77300212007844713050917673)
  ·
    refine ⟨57975159005883534788188255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77300212007844713050917673 57975159005883534788188255)
    ·
      refine ⟨86962738508825302182282383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57975159005883534788188255 86962738508825302182282383)
      ·
        refine ⟨130444107763237953273423575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86962738508825302182282383 130444107763237953273423575)
        ·
          refine ⟨195666161644856929910135363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130444107763237953273423575 195666161644856929910135363)
          ·
            refine ⟨293499242467285394865203045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 195666161644856929910135363 293499242467285394865203045)
            ·
              refine ⟨55031107962616011537225571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 293499242467285394865203045 55031107962616011537225571)
              ·
                refine ⟨82546661943924017305838357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55031107962616011537225571 82546661943924017305838357)
                ·
                  refine ⟨3869374778621438311211173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82546661943924017305838357 3869374778621438311211173)
                  ·
                    refine ⟨725507770991519683352095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3869374778621438311211173 725507770991519683352095)
                    ·
                      rfl

theorem cell23_4238764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_4238764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238764 prefixEnd_4238764 := by exact prefixLift 4238764
  have htrace : WordTrace (prefixWord ++ tailWord_4238764) baseStart_4238764 baseEnd_4238764 := by
    simpa [prefixWord, tailWord_4238764, baseEnd_4238764] using wordTrace_append hprefix tailTrace_4238764
  have hstable : (prefixWord ++ tailWord_4238764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238764).length < 2 ^ (prefixWord ++ tailWord_4238764).sum := by decide
  have hdescent : baseEnd_4238764 < baseStart_4238764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238777 : List Nat := [1, 2, 1, 4, 15]
def baseStart_4238777 : Nat := 118140960795 + 4238777 * 2 ^ 59
def prefixEnd_4238777 : Nat := 4983230072969 + 3 ^ 40 * 4238777 * 2
def baseEnd_4238777 : Nat := 2985637843927390259525

theorem tailTrace_4238777 : CollatzResearch.WordTrace tailWord_4238777 prefixEnd_4238777 2985637843927390259525 := by
  unfold tailWord_4238777
  simp only [CollatzResearch.WordTrace]
  refine ⟨154600898164642329322058585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103067265443094886214705723 154600898164642329322058585)
  ·
    refine ⟨115950673623481746991543939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154600898164642329322058585 115950673623481746991543939)
    ·
      refine ⟨173926010435222620487315909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115950673623481746991543939 173926010435222620487315909)
      ·
        refine ⟨32611126956604241341371733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 173926010435222620487315909 32611126956604241341371733)
        ·
          refine ⟨2985637843927390259525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 32611126956604241341371733 2985637843927390259525)
          ·
            rfl

theorem cell23_4238777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 15].length) (baseStart_4238777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238777 prefixEnd_4238777 := by exact prefixLift 4238777
  have htrace : WordTrace (prefixWord ++ tailWord_4238777) baseStart_4238777 baseEnd_4238777 := by
    simpa [prefixWord, tailWord_4238777, baseEnd_4238777] using wordTrace_append hprefix tailTrace_4238777
  have hstable : (prefixWord ++ tailWord_4238777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238777).length < 2 ^ (prefixWord ++ tailWord_4238777).sum := by decide
  have hdescent : baseEnd_4238777 < baseStart_4238777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238794 : List Nat := [3, 1, 2, 1, 2, 3, 3, 8]
def baseStart_4238794 : Nat := 118140960795 + 4238794 * 2 ^ 59
def prefixEnd_4238794 : Nat := 4983230072969 + 3 ^ 40 * 4238794 * 2
def baseEnd_4238794 : Nat := 80612545088673849358561

theorem tailTrace_4238794 : CollatzResearch.WordTrace tailWord_4238794 prefixEnd_4238794 80612545088673849358561 := by
  unfold tailWord_4238794
  simp only [CollatzResearch.WordTrace]
  refine ⟨38650379551395185306356859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 103067678803720494150284957 38650379551395185306356859)
  ·
    refine ⟨57975569327092777959535289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38650379551395185306356859 57975569327092777959535289)
    ·
      refine ⟨43481676995319583469651467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57975569327092777959535289 43481676995319583469651467)
      ·
        refine ⟨65222515492979375204477201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43481676995319583469651467 65222515492979375204477201)
        ·
          refine ⟨48916886619734531403357901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65222515492979375204477201 48916886619734531403357901)
          ·
            refine ⟨18343832482400449276259213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48916886619734531403357901 18343832482400449276259213)
            ·
              refine ⟨6878937180900168478597205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18343832482400449276259213 6878937180900168478597205)
              ·
                refine ⟨80612545088673849358561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6878937180900168478597205 80612545088673849358561)
                ·
                  rfl

theorem cell23_4238794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 8].length) (baseStart_4238794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238794 prefixEnd_4238794 := by exact prefixLift 4238794
  have htrace : WordTrace (prefixWord ++ tailWord_4238794) baseStart_4238794 baseEnd_4238794 := by
    simpa [prefixWord, tailWord_4238794, baseEnd_4238794] using wordTrace_append hprefix tailTrace_4238794
  have hstable : (prefixWord ++ tailWord_4238794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238794).length < 2 ^ (prefixWord ++ tailWord_4238794).sum := by decide
  have hdescent : baseEnd_4238794 < baseStart_4238794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238844 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_4238844 : Nat := 118140960795 + 4238844 * 2 ^ 59
def prefixEnd_4238844 : Nat := 4983230072969 + 3 ^ 40 * 4238844 * 2
def baseEnd_4238844 : Nat := 2176564391426918737055917

theorem tailTrace_4238844 : CollatzResearch.WordTrace tailWord_4238844 prefixEnd_4238844 2176564391426918737055917 := by
  unfold tailWord_4238844
  simp only [CollatzResearch.WordTrace]
  refine ⟨77301670927699799882373793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103068894570266399843165057 77301670927699799882373793)
  ·
    refine ⟨57976253195774849911780345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 77301670927699799882373793 57976253195774849911780345)
    ·
      refine ⟨43482189896831137433835259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57976253195774849911780345 43482189896831137433835259)
      ·
        refine ⟨65223284845246706150752889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43482189896831137433835259 65223284845246706150752889)
        ·
          refine ⟨48917463633935029613064667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 65223284845246706150752889 48917463633935029613064667)
          ·
            refine ⟨73376195450902544419597001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48917463633935029613064667 73376195450902544419597001)
            ·
              refine ⟨55032146588176908314697751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73376195450902544419597001 55032146588176908314697751)
              ·
                refine ⟨82548219882265362472046627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55032146588176908314697751 82548219882265362472046627)
                ·
                  refine ⟨123822329823398043708069941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82548219882265362472046627 123822329823398043708069941)
                  ·
                    refine ⟨11608343420943566597631557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 123822329823398043708069941 11608343420943566597631557)
                    ·
                      refine ⟨2176564391426918737055917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11608343420943566597631557 2176564391426918737055917)
                      ·
                        rfl

theorem cell23_4238844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_4238844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238844 prefixEnd_4238844 := by exact prefixLift 4238844
  have htrace : WordTrace (prefixWord ++ tailWord_4238844) baseStart_4238844 baseEnd_4238844 := by
    simpa [prefixWord, tailWord_4238844, baseEnd_4238844] using wordTrace_append hprefix tailTrace_4238844
  have hstable : (prefixWord ++ tailWord_4238844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238844).length < 2 ^ (prefixWord ++ tailWord_4238844).sum := by decide
  have hdescent : baseEnd_4238844 < baseStart_4238844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238881 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_4238881 : Nat := 118140960795 + 4238881 * 2 ^ 59
def prefixEnd_4238881 : Nat := 4983230072969 + 3 ^ 40 * 4238881 * 2
def baseEnd_4238881 : Nat := 2176583390211135092293247

theorem tailTrace_4238881 : CollatzResearch.WordTrace tailWord_4238881 prefixEnd_4238881 2176583390211135092293247 := by
  unfold tailWord_4238881
  simp only [CollatzResearch.WordTrace]
  refine ⟨154604691356265555083844497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103069794237510370055896331 154604691356265555083844497)
  ·
    refine ⟨115953518517199166312883373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154604691356265555083844497 115953518517199166312883373)
    ·
      refine ⟨43482569443949687367331265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115953518517199166312883373 43482569443949687367331265)
      ·
        refine ⟨32611927082962265525498449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43482569443949687367331265 32611927082962265525498449)
        ·
          refine ⟨24458945312221699144123837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32611927082962265525498449 24458945312221699144123837)
          ·
            refine ⟨9172104492083137179046439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24458945312221699144123837 9172104492083137179046439)
            ·
              refine ⟨13758156738124705768569659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9172104492083137179046439 13758156738124705768569659)
              ·
                refine ⟨20637235107187058652854489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13758156738124705768569659 20637235107187058652854489)
                ·
                  refine ⟨15477926330390293989640867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20637235107187058652854489 15477926330390293989640867)
                  ·
                    refine ⟨23216889495585440984461301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15477926330390293989640867 23216889495585440984461301)
                    ·
                      refine ⟨2176583390211135092293247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23216889495585440984461301 2176583390211135092293247)
                      ·
                        rfl

theorem cell23_4238881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_4238881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238881 prefixEnd_4238881 := by exact prefixLift 4238881
  have htrace : WordTrace (prefixWord ++ tailWord_4238881) baseStart_4238881 baseEnd_4238881 := by
    simpa [prefixWord, tailWord_4238881, baseEnd_4238881] using wordTrace_append hprefix tailTrace_4238881
  have hstable : (prefixWord ++ tailWord_4238881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238881).length < 2 ^ (prefixWord ++ tailWord_4238881).sum := by decide
  have hdescent : baseEnd_4238881 < baseStart_4238881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238901 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 7]
def baseStart_4238901 : Nat := 118140960795 + 4238901 * 2 ^ 59
def prefixEnd_4238901 : Nat := 4983230072969 + 3 ^ 40 * 4238901 * 2
def baseEnd_4238901 : Nat := 241843739980469446004795

theorem tailTrace_4238901 : CollatzResearch.WordTrace tailWord_4238901 prefixEnd_4238901 241843739980469446004795 := by
  unfold tailWord_4238901
  simp only [CollatzResearch.WordTrace]
  refine ⟨154605420816193098499572557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103070280544128732333048371 154605420816193098499572557)
  ·
    refine ⟨57977032806072411937339709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 154605420816193098499572557 57977032806072411937339709)
    ·
      refine ⟨21741387302277154476502391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57977032806072411937339709 21741387302277154476502391)
      ·
        refine ⟨32612080953415731714753587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21741387302277154476502391 32612080953415731714753587)
        ·
          refine ⟨48918121430123597572130381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32612080953415731714753587 48918121430123597572130381)
          ·
            refine ⟨18344295536296349089548893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48918121430123597572130381 18344295536296349089548893)
            ·
              refine ⟨6879110826111130908580835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18344295536296349089548893 6879110826111130908580835)
              ·
                refine ⟨10318666239166696362871253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6879110826111130908580835 10318666239166696362871253)
                ·
                  refine ⟨241843739980469446004795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10318666239166696362871253 241843739980469446004795)
                  ·
                    rfl

theorem cell23_4238901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_4238901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238901 prefixEnd_4238901 := by exact prefixLift 4238901
  have htrace : WordTrace (prefixWord ++ tailWord_4238901) baseStart_4238901 baseEnd_4238901 := by
    simpa [prefixWord, tailWord_4238901, baseEnd_4238901] using wordTrace_append hprefix tailTrace_4238901
  have hstable : (prefixWord ++ tailWord_4238901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238901).length < 2 ^ (prefixWord ++ tailWord_4238901).sum := by decide
  have hdescent : baseEnd_4238901 < baseStart_4238901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238952 : List Nat := [2, 1, 4, 3, 1, 3, 2, 2, 5]
def baseStart_4238952 : Nat := 118140960795 + 4238952 * 2 ^ 59
def prefixEnd_4238952 : Nat := 4983230072969 + 3 ^ 40 * 4238952 * 2
def baseEnd_4238952 : Nat := 241846649704178257167269

theorem tailTrace_4238952 : CollatzResearch.WordTrace tailWord_4238952 prefixEnd_4238952 241846649704178257167269 := by
  unfold tailWord_4238952
  simp only [CollatzResearch.WordTrace]
  refine ⟨77303640469504167104839555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 103071520626005556139786073 77303640469504167104839555)
  ·
    refine ⟨115955460704256250657259333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 77303640469504167104839555 115955460704256250657259333)
    ·
      refine ⟨21741648882048046998236125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115955460704256250657259333 21741648882048046998236125)
      ·
        refine ⟨8153118330768017624338547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21741648882048046998236125 8153118330768017624338547)
        ·
          refine ⟨12229677496152026436507821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8153118330768017624338547 12229677496152026436507821)
          ·
            refine ⟨4586129061057009913690433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12229677496152026436507821 4586129061057009913690433)
            ·
              refine ⟨3439596795792757435267825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4586129061057009913690433 3439596795792757435267825)
              ·
                refine ⟨2579697596844568076450869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3439596795792757435267825 2579697596844568076450869)
                ·
                  refine ⟨241846649704178257167269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2579697596844568076450869 241846649704178257167269)
                  ·
                    rfl

theorem cell23_4238952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 5].length) (baseStart_4238952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238952 prefixEnd_4238952 := by exact prefixLift 4238952
  have htrace : WordTrace (prefixWord ++ tailWord_4238952) baseStart_4238952 baseEnd_4238952 := by
    simpa [prefixWord, tailWord_4238952, baseEnd_4238952] using wordTrace_append hprefix tailTrace_4238952
  have hstable : (prefixWord ++ tailWord_4238952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238952).length < 2 ^ (prefixWord ++ tailWord_4238952).sum := by decide
  have hdescent : baseEnd_4238952 < baseStart_4238952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238961 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 7, 4]
def baseStart_4238961 : Nat := 118140960795 + 4238961 * 2 ^ 59
def prefixEnd_4238961 : Nat := 4983230072969 + 3 ^ 40 * 4238961 * 2
def baseEnd_4238961 : Nat := 725541489554498259764293

theorem tailTrace_4238961 : CollatzResearch.WordTrace tailWord_4238961 prefixEnd_4238961 725541489554498259764293 := by
  unfold tailWord_4238961
  simp only [CollatzResearch.WordTrace]
  refine ⟨154607609195975728746756737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103071739463983819164504491 154607609195975728746756737)
  ·
    refine ⟨115955706896981796560067553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 154607609195975728746756737 115955706896981796560067553)
    ·
      refine ⟨86966780172736347420050665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115955706896981796560067553 86966780172736347420050665)
      ·
        refine ⟨65225085129552260565037999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86966780172736347420050665 65225085129552260565037999)
        ·
          refine ⟨97837627694328390847556999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65225085129552260565037999 97837627694328390847556999)
          ·
            refine ⟨146756441541492586271335499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97837627694328390847556999 146756441541492586271335499)
            ·
              refine ⟨220134662312238879407003249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146756441541492586271335499 220134662312238879407003249)
              ·
                refine ⟨165100996734179159555252437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220134662312238879407003249 165100996734179159555252437)
                ·
                  refine ⟨3869554610957324052076229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 165100996734179159555252437 3869554610957324052076229)
                  ·
                    refine ⟨725541489554498259764293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3869554610957324052076229 725541489554498259764293)
                    ·
                      rfl

theorem cell23_4238961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 4].length) (baseStart_4238961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238961 prefixEnd_4238961 := by exact prefixLift 4238961
  have htrace : WordTrace (prefixWord ++ tailWord_4238961) baseStart_4238961 baseEnd_4238961 := by
    simpa [prefixWord, tailWord_4238961, baseEnd_4238961] using wordTrace_append hprefix tailTrace_4238961
  have hstable : (prefixWord ++ tailWord_4238961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238961).length < 2 ^ (prefixWord ++ tailWord_4238961).sum := by decide
  have hdescent : baseEnd_4238961 < baseStart_4238961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4238971 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 3]
def baseStart_4238971 : Nat := 118140960795 + 4238971 * 2 ^ 59
def prefixEnd_4238971 : Nat := 4983230072969 + 3 ^ 40 * 4238971 * 2
def baseEnd_4238971 : Nat := 2176629603470039740167833

theorem tailTrace_4238971 : CollatzResearch.WordTrace tailWord_4238971 prefixEnd_4238971 2176629603470039740167833 := by
  unfold tailWord_4238971
  simp only [CollatzResearch.WordTrace]
  refine ⟨154607973925939500454620767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 103071982617293000303080511 154607973925939500454620767)
  ·
    refine ⟨231911960888909250681931151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 154607973925939500454620767 231911960888909250681931151)
    ·
      refine ⟨347867941333363876022896727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231911960888909250681931151 347867941333363876022896727)
      ·
        refine ⟨521801912000045814034345091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 347867941333363876022896727 521801912000045814034345091)
        ·
          refine ⟨782702868000068721051517637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 521801912000045814034345091 782702868000068721051517637)
          ·
            refine ⟨146756787750012885197159557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 782702868000068721051517637 146756787750012885197159557)
            ·
              refine ⟨27516897703127415974467417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 146756787750012885197159557 27516897703127415974467417)
              ·
                refine ⟨20637673277345561980850563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27516897703127415974467417 20637673277345561980850563)
                ·
                  refine ⟨30956509916018342971275845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20637673277345561980850563 30956509916018342971275845)
                  ·
                    refine ⟨5804345609253439307114221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30956509916018342971275845 5804345609253439307114221)
                    ·
                      refine ⟨2176629603470039740167833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5804345609253439307114221 2176629603470039740167833)
                      ·
                        rfl

theorem cell23_4238971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 3].length) (baseStart_4238971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4238971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4238971 prefixEnd_4238971 := by exact prefixLift 4238971
  have htrace : WordTrace (prefixWord ++ tailWord_4238971) baseStart_4238971 baseEnd_4238971 := by
    simpa [prefixWord, tailWord_4238971, baseEnd_4238971] using wordTrace_append hprefix tailTrace_4238971
  have hstable : (prefixWord ++ tailWord_4238971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4238971).length < 2 ^ (prefixWord ++ tailWord_4238971).sum := by decide
  have hdescent : baseEnd_4238971 < baseStart_4238971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4238971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
