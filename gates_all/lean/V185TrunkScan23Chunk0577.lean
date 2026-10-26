import V185TrunkScan23Chunk0576

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3412078 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_3412078 : Nat := 118140960795 + 3412078 * 2 ^ 59
def prefixEnd_3412078 : Nat := 4983230072969 + 3 ^ 40 * 3412078 * 2
def baseEnd_3412078 : Nat := 1752036044631806462833145

theorem tailTrace_3412078 : CollatzResearch.WordTrace tailWord_3412078 prefixEnd_3412078 1752036044631806462833145 := by
  unfold tailWord_3412078
  simp only [CollatzResearch.WordTrace]
  refine ⟨15556088566578952171685611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82965805688421078248989925 15556088566578952171685611)
  ·
    refine ⟨23334132849868428257528417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15556088566578952171685611 23334132849868428257528417)
    ·
      refine ⟨17500599637401321193146313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23334132849868428257528417 17500599637401321193146313)
      ·
        refine ⟨13125449728050990894859735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17500599637401321193146313 13125449728050990894859735)
        ·
          refine ⟨19688174592076486342289603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13125449728050990894859735 19688174592076486342289603)
          ·
            refine ⟨29532261888114729513434405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19688174592076486342289603 29532261888114729513434405)
            ·
              refine ⟨5537299104021511783768951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29532261888114729513434405 5537299104021511783768951)
              ·
                refine ⟨8305948656032267675653427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5537299104021511783768951 8305948656032267675653427)
                ·
                  refine ⟨12458922984048401513480141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8305948656032267675653427 12458922984048401513480141)
                  ·
                    refine ⟨4672096119018150567555053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12458922984048401513480141 4672096119018150567555053)
                    ·
                      refine ⟨1752036044631806462833145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4672096119018150567555053 1752036044631806462833145)
                      ·
                        rfl

theorem cell23_3412078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_3412078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412078 prefixEnd_3412078 := by exact prefixLift 3412078
  have htrace : WordTrace (prefixWord ++ tailWord_3412078) baseStart_3412078 baseEnd_3412078 := by
    simpa [prefixWord, tailWord_3412078, baseEnd_3412078] using wordTrace_append hprefix tailTrace_3412078
  have hstable : (prefixWord ++ tailWord_3412078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412078).length < 2 ^ (prefixWord ++ tailWord_3412078).sum := by decide
  have hdescent : baseEnd_3412078 < baseStart_3412078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412088 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 1, 3, 2]
def baseStart_3412088 : Nat := 118140960795 + 3412088 * 2 ^ 59
def prefixEnd_3412088 : Nat := 4983230072969 + 3 ^ 40 * 3412088 * 2
def baseEnd_3412088 : Nat := 1752041179438351423708099

theorem tailTrace_3412088 : CollatzResearch.WordTrace tailWord_3412088 prefixEnd_3412088 1752041179438351423708099 := by
  unfold tailWord_3412088
  simp only [CollatzResearch.WordTrace]
  refine ⟨62224536631297694540674459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82966048841730259387565945 62224536631297694540674459)
  ·
    refine ⟨93336804946946541811011689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62224536631297694540674459 93336804946946541811011689)
    ·
      refine ⟨70002603710209906358258767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93336804946946541811011689 70002603710209906358258767)
      ·
        refine ⟨105003905565314859537388151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70002603710209906358258767 105003905565314859537388151)
        ·
          refine ⟨157505858347972289306082227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105003905565314859537388151 157505858347972289306082227)
          ·
            refine ⟨236258787521958433959123341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157505858347972289306082227 236258787521958433959123341)
            ·
              refine ⟨88597045320734412734671253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236258787521958433959123341 88597045320734412734671253)
              ·
                refine ⟨4152986499409425596937715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88597045320734412734671253 4152986499409425596937715)
                ·
                  refine ⟨6229479749114138395406573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4152986499409425596937715 6229479749114138395406573)
                  ·
                    refine ⟨2336054905917801898277465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6229479749114138395406573 2336054905917801898277465)
                    ·
                      refine ⟨1752041179438351423708099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336054905917801898277465 1752041179438351423708099)
                      ·
                        rfl

theorem cell23_3412088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 1, 3, 2].length) (baseStart_3412088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412088 prefixEnd_3412088 := by exact prefixLift 3412088
  have htrace : WordTrace (prefixWord ++ tailWord_3412088) baseStart_3412088 baseEnd_3412088 := by
    simpa [prefixWord, tailWord_3412088, baseEnd_3412088] using wordTrace_append hprefix tailTrace_3412088
  have hstable : (prefixWord ++ tailWord_3412088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412088).length < 2 ^ (prefixWord ++ tailWord_3412088).sum := by decide
  have hdescent : baseEnd_3412088 < baseStart_3412088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412171 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 2, 5]
def baseStart_3412171 : Nat := 118140960795 + 3412171 * 2 ^ 59
def prefixEnd_3412171 : Nat := 4983230072969 + 3 ^ 40 * 3412171 * 2
def baseEnd_3412171 : Nat := 584027932777558199656739

theorem tailTrace_3412171 : CollatzResearch.WordTrace tailWord_3412171 prefixEnd_3412171 584027932777558199656739 := by
  unfold tailWord_3412171
  simp only [CollatzResearch.WordTrace]
  refine ⟨124452100521294694256620367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82968067014196462837746911 124452100521294694256620367)
  ·
    refine ⟨186678150781942041384930551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124452100521294694256620367 186678150781942041384930551)
    ·
      refine ⟨280017226172913062077395827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186678150781942041384930551 280017226172913062077395827)
      ·
        refine ⟨420025839259369593116093741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280017226172913062077395827 420025839259369593116093741)
        ·
          refine ⟨157509689722263597418535153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420025839259369593116093741 157509689722263597418535153)
          ·
            refine ⟨118132267291697698063901365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157509689722263597418535153 118132267291697698063901365)
            ·
              refine ⟨11074900058596659193490753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118132267291697698063901365 11074900058596659193490753)
              ·
                refine ⟨8306175043947494395118065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11074900058596659193490753 8306175043947494395118065)
                ·
                  refine ⟨6229631282960620796338549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8306175043947494395118065 6229631282960620796338549)
                  ·
                    refine ⟨584027932777558199656739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6229631282960620796338549 584027932777558199656739)
                    ·
                      rfl

theorem cell23_3412171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 5].length) (baseStart_3412171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412171 prefixEnd_3412171 := by exact prefixLift 3412171
  have htrace : WordTrace (prefixWord ++ tailWord_3412171) baseStart_3412171 baseEnd_3412171 := by
    simpa [prefixWord, tailWord_3412171, baseEnd_3412171] using wordTrace_append hprefix tailTrace_3412171
  have hstable : (prefixWord ++ tailWord_3412171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412171).length < 2 ^ (prefixWord ++ tailWord_3412171).sum := by decide
  have hdescent : baseEnd_3412171 < baseStart_3412171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412191 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 4]
def baseStart_3412191 : Nat := 118140960795 + 3412191 * 2 ^ 59
def prefixEnd_3412191 : Nat := 4983230072969 + 3 ^ 40 * 3412191 * 2
def baseEnd_3412191 : Nat := 1752094067945764520720125

theorem tailTrace_3412191 : CollatzResearch.WordTrace tailWord_3412191 prefixEnd_3412191 1752094067945764520720125 := by
  unfold tailWord_3412191
  simp only [CollatzResearch.WordTrace]
  refine ⟨124452829981222237672348427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82968553320814825114898951 124452829981222237672348427)
  ·
    refine ⟨186679244971833356508522641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124452829981222237672348427 186679244971833356508522641)
    ·
      refine ⟨140009433728875017381391981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186679244971833356508522641 140009433728875017381391981)
      ·
        refine ⟨52503537648328131518021993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140009433728875017381391981 52503537648328131518021993)
        ·
          refine ⟨39377653236246098638516495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52503537648328131518021993 39377653236246098638516495)
          ·
            refine ⟨59066479854369147957774743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39377653236246098638516495 59066479854369147957774743)
            ·
              refine ⟨88599719781553721936662115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59066479854369147957774743 88599719781553721936662115)
              ·
                refine ⟨132899579672330582904993173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88599719781553721936662115 132899579672330582904993173)
                ·
                  refine ⟨6229667797140496073671555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132899579672330582904993173 6229667797140496073671555)
                  ·
                    refine ⟨9344501695710744110507333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6229667797140496073671555 9344501695710744110507333)
                    ·
                      refine ⟨1752094067945764520720125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9344501695710744110507333 1752094067945764520720125)
                      ·
                        rfl

theorem cell23_3412191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_3412191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412191 prefixEnd_3412191 := by exact prefixLift 3412191
  have htrace : WordTrace (prefixWord ++ tailWord_3412191) baseStart_3412191 baseEnd_3412191 := by
    simpa [prefixWord, tailWord_3412191, baseEnd_3412191] using wordTrace_append hprefix tailTrace_3412191
  have hstable : (prefixWord ++ tailWord_3412191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412191).length < 2 ^ (prefixWord ++ tailWord_3412191).sum := by decide
  have hdescent : baseEnd_3412191 < baseStart_3412191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412205 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_3412205 : Nat := 118140960795 + 3412205 * 2 ^ 59
def prefixEnd_3412205 : Nat := 4983230072969 + 3 ^ 40 * 3412205 * 2
def baseEnd_3412205 : Nat := 584033752224975821981687

theorem tailTrace_3412205 : CollatzResearch.WordTrace tailWord_3412205 prefixEnd_3412205 584033752224975821981687 := by
  unfold tailWord_3412205
  simp only [CollatzResearch.WordTrace]
  refine ⟨124453340603171518063358069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82968893735447678708905379 124453340603171518063358069)
  ·
    refine ⟨11667500681547329818439819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124453340603171518063358069 11667500681547329818439819)
    ·
      refine ⟨17501251022320994727659729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11667500681547329818439819 17501251022320994727659729)
      ·
        refine ⟨13125938266740746045744797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17501251022320994727659729 13125938266740746045744797)
        ·
          refine ⟨4922226850027779767154299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13125938266740746045744797 4922226850027779767154299)
          ·
            refine ⟨7383340275041669650731449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4922226850027779767154299 7383340275041669650731449)
            ·
              refine ⟨5537505206281252238048587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7383340275041669650731449 5537505206281252238048587)
              ·
                refine ⟨8306257809421878357072881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5537505206281252238048587 8306257809421878357072881)
                ·
                  refine ⟨6229693357066408767804661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8306257809421878357072881 6229693357066408767804661)
                  ·
                    refine ⟨584033752224975821981687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6229693357066408767804661 584033752224975821981687)
                    ·
                      rfl

theorem cell23_3412205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_3412205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412205 prefixEnd_3412205 := by exact prefixLift 3412205
  have htrace : WordTrace (prefixWord ++ tailWord_3412205) baseStart_3412205 baseEnd_3412205 := by
    simpa [prefixWord, tailWord_3412205, baseEnd_3412205] using wordTrace_append hprefix tailTrace_3412205
  have hstable : (prefixWord ++ tailWord_3412205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412205).length < 2 ^ (prefixWord ++ tailWord_3412205).sum := by decide
  have hdescent : baseEnd_3412205 < baseStart_3412205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412235 : List Nat := [1, 1, 1, 1, 5, 2, 3, 4, 1, 4]
def baseStart_3412235 : Nat := 118140960795 + 3412235 * 2 ^ 59
def prefixEnd_3412235 : Nat := 4983230072969 + 3 ^ 40 * 3412235 * 2
def baseEnd_3412235 : Nat := 584038887031520782856641

theorem tailTrace_3412235 : CollatzResearch.WordTrace tailWord_3412235 prefixEnd_3412235 584038887031520782856641 := by
  unfold tailWord_3412235
  simp only [CollatzResearch.WordTrace]
  refine ⟨124454434793062833186950159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82969623195375222124633439 124454434793062833186950159)
  ·
    refine ⟨186681652189594249780425239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124454434793062833186950159 186681652189594249780425239)
    ·
      refine ⟨280022478284391374670637859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186681652189594249780425239 280022478284391374670637859)
      ·
        refine ⟨420033717426587062005956789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280022478284391374670637859 420033717426587062005956789)
        ·
          refine ⟨39378161008742537063058449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 420033717426587062005956789 39378161008742537063058449)
          ·
            refine ⟨29533620756556902797293837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39378161008742537063058449 29533620756556902797293837)
            ·
              refine ⟨11075107783708838548985189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29533620756556902797293837 11075107783708838548985189)
              ·
                refine ⟨2076582709445407227934723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11075107783708838548985189 2076582709445407227934723)
                ·
                  refine ⟨3114874064168110841902085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076582709445407227934723 3114874064168110841902085)
                  ·
                    refine ⟨584038887031520782856641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3114874064168110841902085 584038887031520782856641)
                    ·
                      rfl

theorem cell23_3412235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 1, 4].length) (baseStart_3412235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412235 prefixEnd_3412235 := by exact prefixLift 3412235
  have htrace : WordTrace (prefixWord ++ tailWord_3412235) baseStart_3412235 baseEnd_3412235 := by
    simpa [prefixWord, tailWord_3412235, baseEnd_3412235] using wordTrace_append hprefix tailTrace_3412235
  have hstable : (prefixWord ++ tailWord_3412235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412235).length < 2 ^ (prefixWord ++ tailWord_3412235).sum := by decide
  have hdescent : baseEnd_3412235 < baseStart_3412235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412291 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 3, 6]
def baseStart_3412291 : Nat := 118140960795 + 3412291 * 2 ^ 59
def prefixEnd_3412291 : Nat := 4983230072969 + 3 ^ 40 * 3412291 * 2
def baseEnd_3412291 : Nat := 584048472003738043156555

theorem tailTrace_3412291 : CollatzResearch.WordTrace tailWord_3412291 prefixEnd_3412291 584048472003738043156555 := by
  unfold tailWord_3412291
  simp only [CollatzResearch.WordTrace]
  refine ⟨124456477280859954750988727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82970984853906636500659151 124456477280859954750988727)
  ·
    refine ⟨186684715921289932126483091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124456477280859954750988727 186684715921289932126483091)
    ·
      refine ⟨280027073881934898189724637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186684715921289932126483091 280027073881934898189724637)
      ·
        refine ⟨105010152705725586821146739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280027073881934898189724637 105010152705725586821146739)
        ·
          refine ⟨157515229058588380231720109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105010152705725586821146739 157515229058588380231720109)
          ·
            refine ⟨59068210896970642586895041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157515229058588380231720109 59068210896970642586895041)
            ·
              refine ⟨44301158172727981940171281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59068210896970642586895041 44301158172727981940171281)
              ·
                refine ⟨33225868629545986455128461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44301158172727981940171281 33225868629545986455128461)
                ·
                  refine ⟨12459700736079744920673173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33225868629545986455128461 12459700736079744920673173)
                  ·
                    refine ⟨584048472003738043156555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12459700736079744920673173 584048472003738043156555)
                    ·
                      rfl

theorem cell23_3412291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 6].length) (baseStart_3412291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412291 prefixEnd_3412291 := by exact prefixLift 3412291
  have htrace : WordTrace (prefixWord ++ tailWord_3412291) baseStart_3412291 baseEnd_3412291 := by
    simpa [prefixWord, tailWord_3412291, baseEnd_3412291] using wordTrace_append hprefix tailTrace_3412291
  have hstable : (prefixWord ++ tailWord_3412291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412291).length < 2 ^ (prefixWord ++ tailWord_3412291).sum := by decide
  have hdescent : baseEnd_3412291 < baseStart_3412291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412338 : List Nat := [3, 2, 1, 2, 1, 5, 9]
def baseStart_3412338 : Nat := 118140960795 + 3412338 * 2 ^ 59
def prefixEnd_3412338 : Nat := 4983230072969 + 3 ^ 40 * 3412338 * 2
def baseEnd_3412338 : Nat := 21631722834592289451629

theorem tailTrace_3412338 : CollatzResearch.WordTrace tailWord_3412338 prefixEnd_3412338 21631722834592289451629 := by
  unfold tailWord_3412338
  simp only [CollatzResearch.WordTrace]
  refine ⟨31114547877922420444487417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82972127674459787851966445 31114547877922420444487417)
  ·
    refine ⟨23335910908441815333365563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31114547877922420444487417 23335910908441815333365563)
    ·
      refine ⟨35003866362662723000048345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23335910908441815333365563 35003866362662723000048345)
      ·
        refine ⟨26252899771997042250036259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35003866362662723000048345 26252899771997042250036259)
        ·
          refine ⟨39379349657995563375054389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26252899771997042250036259 39379349657995563375054389)
          ·
            refine ⟨3691814030437084066411349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39379349657995563375054389 3691814030437084066411349)
            ·
              refine ⟨21631722834592289451629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3691814030437084066411349 21631722834592289451629)
              ·
                rfl

theorem cell23_3412338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 9].length) (baseStart_3412338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412338 prefixEnd_3412338 := by exact prefixLift 3412338
  have htrace : WordTrace (prefixWord ++ tailWord_3412338) baseStart_3412338 baseEnd_3412338 := by
    simpa [prefixWord, tailWord_3412338, baseEnd_3412338] using wordTrace_append hprefix tailTrace_3412338
  have hstable : (prefixWord ++ tailWord_3412338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412338).length < 2 ^ (prefixWord ++ tailWord_3412338).sum := by decide
  have hdescent : baseEnd_3412338 < baseStart_3412338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412348 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_3412348 : Nat := 118140960795 + 3412348 * 2 ^ 59
def prefixEnd_3412348 : Nat := 4983230072969 + 3 ^ 40 * 3412348 * 2
def baseEnd_3412348 : Nat := 1752174684408520406456903

theorem tailTrace_3412348 : CollatzResearch.WordTrace tailWord_3412348 prefixEnd_3412348 1752174684408520406456903 := by
  unfold tailWord_3412348
  simp only [CollatzResearch.WordTrace]
  refine ⟨62229278120826726742906849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82972370827768968990542465 62229278120826726742906849)
  ·
    refine ⟨46671958590620045057180137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62229278120826726742906849 46671958590620045057180137)
    ·
      refine ⟨35003968942965033792885103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46671958590620045057180137 35003968942965033792885103)
      ·
        refine ⟨52505953414447550689327655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35003968942965033792885103 52505953414447550689327655)
        ·
          refine ⟨78758930121671326033991483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52505953414447550689327655 78758930121671326033991483)
          ·
            refine ⟨118138395182506989050987225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78758930121671326033991483 118138395182506989050987225)
            ·
              refine ⟨88603796386880241788240419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118138395182506989050987225 88603796386880241788240419)
              ·
                refine ⟨132905694580320362682360629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88603796386880241788240419 132905694580320362682360629)
                ·
                  refine ⟨12459908866905034001471309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132905694580320362682360629 12459908866905034001471309)
                  ·
                    refine ⟨4672465825089387750551741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12459908866905034001471309 4672465825089387750551741)
                    ·
                      refine ⟨1752174684408520406456903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4672465825089387750551741 1752174684408520406456903)
                      ·
                        rfl

theorem cell23_3412348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_3412348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412348 prefixEnd_3412348 := by exact prefixLift 3412348
  have htrace : WordTrace (prefixWord ++ tailWord_3412348) baseStart_3412348 baseEnd_3412348 := by
    simpa [prefixWord, tailWord_3412348, baseEnd_3412348] using wordTrace_append hprefix tailTrace_3412348
  have hstable : (prefixWord ++ tailWord_3412348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412348).length < 2 ^ (prefixWord ++ tailWord_3412348).sum := by decide
  have hdescent : baseEnd_3412348 < baseStart_3412348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412349 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 3, 2, 2]
def baseStart_3412349 : Nat := 118140960795 + 3412349 * 2 ^ 59
def prefixEnd_3412349 : Nat := 4983230072969 + 3 ^ 40 * 3412349 * 2
def baseEnd_3412349 : Nat := 1752175197889174902544399

theorem tailTrace_3412349 : CollatzResearch.WordTrace tailWord_3412349 prefixEnd_3412349 1752175197889174902544399 := by
  unfold tailWord_3412349
  simp only [CollatzResearch.WordTrace]
  refine ⟨124458592714649830656600101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82972395143099887104400067 124458592714649830656600101)
  ·
    refine ⟨23335986133996843248112519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124458592714649830656600101 23335986133996843248112519)
    ·
      refine ⟨35003979200995264872168779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23335986133996843248112519 35003979200995264872168779)
      ·
        refine ⟨52505968801492897308253169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35003979200995264872168779 52505968801492897308253169)
        ·
          refine ⟨39379476601119672981189877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52505968801492897308253169 39379476601119672981189877)
          ·
            refine ⟨3691825931354969341986551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39379476601119672981189877 3691825931354969341986551)
            ·
              refine ⟨5537738897032454012979827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691825931354969341986551 5537738897032454012979827)
              ·
                refine ⟨8306608345548681019469741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5537738897032454012979827 8306608345548681019469741)
                ·
                  refine ⟨3114978129580755382301153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8306608345548681019469741 3114978129580755382301153)
                  ·
                    refine ⟨2336233597185566536725865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3114978129580755382301153 2336233597185566536725865)
                    ·
                      refine ⟨1752175197889174902544399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336233597185566536725865 1752175197889174902544399)
                      ·
                        rfl

theorem cell23_3412349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_3412349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412349 prefixEnd_3412349 := by exact prefixLift 3412349
  have htrace : WordTrace (prefixWord ++ tailWord_3412349) baseStart_3412349 baseEnd_3412349 := by
    simpa [prefixWord, tailWord_3412349, baseEnd_3412349] using wordTrace_append hprefix tailTrace_3412349
  have hstable : (prefixWord ++ tailWord_3412349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412349).length < 2 ^ (prefixWord ++ tailWord_3412349).sum := by decide
  have hdescent : baseEnd_3412349 < baseStart_3412349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412351 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 1, 9]
def baseStart_3412351 : Nat := 118140960795 + 3412351 * 2 ^ 59
def prefixEnd_3412351 : Nat := 4983230072969 + 3 ^ 40 * 3412351 * 2
def baseEnd_3412351 : Nat := 584058741616827964906463

theorem tailTrace_3412351 : CollatzResearch.WordTrace tailWord_3412351 prefixEnd_3412351 584058741616827964906463 := by
  unfold tailWord_3412351
  simp only [CollatzResearch.WordTrace]
  refine ⟨124458665660642584998172907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82972443773761723332115271 124458665660642584998172907)
  ·
    refine ⟨186687998490963877497259361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124458665660642584998172907 186687998490963877497259361)
    ·
      refine ⟨140015998868222908122944521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186687998490963877497259361 140015998868222908122944521)
      ·
        refine ⟨105011999151167181092208391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140015998868222908122944521 105011999151167181092208391)
        ·
          refine ⟨157517998726750771638312587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105011999151167181092208391 157517998726750771638312587)
          ·
            refine ⟨236276998090126157457468881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157517998726750771638312587 236276998090126157457468881)
            ·
              refine ⟨177207748567594618093101661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236276998090126157457468881 177207748567594618093101661)
              ·
                refine ⟨66452905712847981784913123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177207748567594618093101661 66452905712847981784913123)
                ·
                  refine ⟨99679358569271972677369685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66452905712847981784913123 99679358569271972677369685)
                  ·
                    refine ⟨584058741616827964906463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 99679358569271972677369685 584058741616827964906463)
                    ·
                      rfl

theorem cell23_3412351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_3412351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412351 prefixEnd_3412351 := by exact prefixLift 3412351
  have htrace : WordTrace (prefixWord ++ tailWord_3412351) baseStart_3412351 baseEnd_3412351 := by
    simpa [prefixWord, tailWord_3412351, baseEnd_3412351] using wordTrace_append hprefix tailTrace_3412351
  have hstable : (prefixWord ++ tailWord_3412351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412351).length < 2 ^ (prefixWord ++ tailWord_3412351).sum := by decide
  have hdescent : baseEnd_3412351 < baseStart_3412351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412382 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3412382 : Nat := 118140960795 + 3412382 * 2 ^ 59
def prefixEnd_3412382 : Nat := 4983230072969 + 3 ^ 40 * 3412382 * 2
def baseEnd_3412382 : Nat := 1752192142750773273431747

theorem tailTrace_3412382 : CollatzResearch.WordTrace tailWord_3412382 prefixEnd_3412382 1752192142750773273431747 := by
  unfold tailWord_3412382
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557474540441284661568925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82973197549020184861700933 15557474540441284661568925)
  ·
    refine ⟨5834052952665481748088347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15557474540441284661568925 5834052952665481748088347)
    ·
      refine ⟨8751079428998222622132521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5834052952665481748088347 8751079428998222622132521)
      ·
        refine ⟨6563309571748666966599391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8751079428998222622132521 6563309571748666966599391)
        ·
          refine ⟨9844964357623000449899087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6563309571748666966599391 9844964357623000449899087)
          ·
            refine ⟨14767446536434500674848631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9844964357623000449899087 14767446536434500674848631)
            ·
              refine ⟨22151169804651751012272947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14767446536434500674848631 22151169804651751012272947)
              ·
                refine ⟨33226754706977626518409421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22151169804651751012272947 33226754706977626518409421)
                ·
                  refine ⟨12460033015116609944403533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33226754706977626518409421 12460033015116609944403533)
                  ·
                    refine ⟨4672512380668728729151325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12460033015116609944403533 4672512380668728729151325)
                    ·
                      refine ⟨1752192142750773273431747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4672512380668728729151325 1752192142750773273431747)
                      ·
                        rfl

theorem cell23_3412382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3412382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412382 prefixEnd_3412382 := by exact prefixLift 3412382
  have htrace : WordTrace (prefixWord ++ tailWord_3412382) baseStart_3412382 baseEnd_3412382 := by
    simpa [prefixWord, tailWord_3412382, baseEnd_3412382] using wordTrace_append hprefix tailTrace_3412382
  have hstable : (prefixWord ++ tailWord_3412382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412382).length < 2 ^ (prefixWord ++ tailWord_3412382).sum := by decide
  have hdescent : baseEnd_3412382 < baseStart_3412382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412450 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_3412450 : Nat := 118140960795 + 3412450 * 2 ^ 59
def prefixEnd_3412450 : Nat := 4983230072969 + 3 ^ 40 * 3412450 * 2
def baseEnd_3412450 : Nat := 1752227059435279007381435

theorem tailTrace_3412450 : CollatzResearch.WordTrace tailWord_3412450 prefixEnd_3412450 1752227059435279007381435 := by
  unfold tailWord_3412450
  simp only [CollatzResearch.WordTrace]
  refine ⟨31115569121820981226506701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82974850991522616604017869 31115569121820981226506701)
  ·
    refine ⟨11668338420682867959940013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31115569121820981226506701 11668338420682867959940013)
    ·
      refine ⟨4375626907756075484977505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11668338420682867959940013 4375626907756075484977505)
      ·
        refine ⟨3281720180817056613733129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4375626907756075484977505 3281720180817056613733129)
        ·
          refine ⟨2461290135612792460299847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3281720180817056613733129 2461290135612792460299847)
          ·
            refine ⟨3691935203419188690449771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461290135612792460299847 3691935203419188690449771)
            ·
              refine ⟨5537902805128783035674657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691935203419188690449771 5537902805128783035674657)
              ·
                refine ⟨4153427103846587276755993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5537902805128783035674657 4153427103846587276755993)
                ·
                  refine ⟨3115070327884940457566995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4153427103846587276755993 3115070327884940457566995)
                  ·
                    refine ⟨4672605491827410686350493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3115070327884940457566995 4672605491827410686350493)
                    ·
                      refine ⟨1752227059435279007381435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4672605491827410686350493 1752227059435279007381435)
                      ·
                        rfl

theorem cell23_3412450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_3412450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412450 prefixEnd_3412450 := by exact prefixLift 3412450
  have htrace : WordTrace (prefixWord ++ tailWord_3412450) baseStart_3412450 baseEnd_3412450 := by
    simpa [prefixWord, tailWord_3412450, baseEnd_3412450] using wordTrace_append hprefix tailTrace_3412450
  have hstable : (prefixWord ++ tailWord_3412450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412450).length < 2 ^ (prefixWord ++ tailWord_3412450).sum := by decide
  have hdescent : baseEnd_3412450 < baseStart_3412450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412455 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3412455 : Nat := 118140960795 + 3412455 * 2 ^ 59
def prefixEnd_3412455 : Nat := 4983230072969 + 3 ^ 40 * 3412455 * 2
def baseEnd_3412455 : Nat := 1752229626838551487818911

theorem tailTrace_3412455 : CollatzResearch.WordTrace tailWord_3412455 prefixEnd_3412455 1752229626838551487818911 := by
  unfold tailWord_3412455
  simp only [CollatzResearch.WordTrace]
  refine ⟨124462458852265810759958819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82974972568177207173305879 124462458852265810759958819)
  ·
    refine ⟨186693688278398716139938229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124462458852265810759958819 186693688278398716139938229)
    ·
      refine ⟨17502533276099879638119209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186693688278398716139938229 17502533276099879638119209)
      ·
        refine ⟨13126899957074909728589407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17502533276099879638119209 13126899957074909728589407)
        ·
          refine ⟨19690349935612364592884111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13126899957074909728589407 19690349935612364592884111)
          ·
            refine ⟨29535524903418546889326167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19690349935612364592884111 29535524903418546889326167)
            ·
              refine ⟨44303287355127820333989251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29535524903418546889326167 44303287355127820333989251)
              ·
                refine ⟨66454931032691730500983877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44303287355127820333989251 66454931032691730500983877)
                ·
                  refine ⟨12460299568629699468934477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66454931032691730500983877 12460299568629699468934477)
                  ·
                    refine ⟨4672612338236137300850429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12460299568629699468934477 4672612338236137300850429)
                    ·
                      refine ⟨1752229626838551487818911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4672612338236137300850429 1752229626838551487818911)
                      ·
                        rfl

theorem cell23_3412455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3412455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412455 prefixEnd_3412455 := by exact prefixLift 3412455
  have htrace : WordTrace (prefixWord ++ tailWord_3412455) baseStart_3412455 baseEnd_3412455 := by
    simpa [prefixWord, tailWord_3412455, baseEnd_3412455] using wordTrace_append hprefix tailTrace_3412455
  have hstable : (prefixWord ++ tailWord_3412455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412455).length < 2 ^ (prefixWord ++ tailWord_3412455).sum := by decide
  have hdescent : baseEnd_3412455 < baseStart_3412455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412456 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 2, 2, 2]
def baseStart_3412456 : Nat := 118140960795 + 3412456 * 2 ^ 59
def prefixEnd_3412456 : Nat := 4983230072969 + 3 ^ 40 * 3412456 * 2
def baseEnd_3412456 : Nat := 1752230140319205983906407

theorem tailTrace_3412456 : CollatzResearch.WordTrace tailWord_3412456 prefixEnd_3412456 1752230140319205983906407 := by
  unfold tailWord_3412456
  simp only [CollatzResearch.WordTrace]
  refine ⟨62231247662631093965372611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82974996883508125287163481 62231247662631093965372611)
  ·
    refine ⟨93346871493946640948058917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62231247662631093965372611 93346871493946640948058917)
    ·
      refine ⟨17502538405114995177761047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93346871493946640948058917 17502538405114995177761047)
      ·
        refine ⟨26253807607672492766641571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17502538405114995177761047 26253807607672492766641571)
        ·
          refine ⟨39380711411508739149962357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26253807607672492766641571 39380711411508739149962357)
          ·
            refine ⟨3691941694828944295308971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39380711411508739149962357 3691941694828944295308971)
            ·
              refine ⟨5537912542243416442963457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691941694828944295308971 5537912542243416442963457)
              ·
                refine ⟨4153434406682562332222593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5537912542243416442963457 4153434406682562332222593)
                ·
                  refine ⟨3115075805011921749166945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4153434406682562332222593 3115075805011921749166945)
                  ·
                    refine ⟨2336306853758941311875209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3115075805011921749166945 2336306853758941311875209)
                    ·
                      refine ⟨1752230140319205983906407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336306853758941311875209 1752230140319205983906407)
                      ·
                        rfl

theorem cell23_3412456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_3412456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412456 prefixEnd_3412456 := by exact prefixLift 3412456
  have htrace : WordTrace (prefixWord ++ tailWord_3412456) baseStart_3412456 baseEnd_3412456 := by
    simpa [prefixWord, tailWord_3412456, baseEnd_3412456] using wordTrace_append hprefix tailTrace_3412456
  have hstable : (prefixWord ++ tailWord_3412456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412456).length < 2 ^ (prefixWord ++ tailWord_3412456).sum := by decide
  have hdescent : baseEnd_3412456 < baseStart_3412456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412462 : List Nat := [4, 1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_3412462 : Nat := 118140960795 + 3412462 * 2 ^ 59
def prefixEnd_3412462 : Nat := 4983230072969 + 3 ^ 40 * 3412462 * 2
def baseEnd_3412462 : Nat := 194692580133681440047931

theorem tailTrace_3412462 : CollatzResearch.WordTrace tailWord_3412462 prefixEnd_3412462 194692580133681440047931 := by
  unfold tailWord_3412462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557839270405056369432955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82975142775493633970309093 15557839270405056369432955)
  ·
    refine ⟨23336758905607584554149433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15557839270405056369432955 23336758905607584554149433)
    ·
      refine ⟨17502569179205688415612075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23336758905607584554149433 17502569179205688415612075)
      ·
        refine ⟨26253853768808532623418113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17502569179205688415612075 26253853768808532623418113)
        ·
          refine ⟨19690390326606399467563585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26253853768808532623418113 19690390326606399467563585)
          ·
            refine ⟨14767792744954799600672689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19690390326606399467563585 14767792744954799600672689)
            ·
              refine ⟨11075844558716099700504517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14767792744954799600672689 11075844558716099700504517)
              ·
                refine ⟨2076720854759268693844597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11075844558716099700504517 2076720854759268693844597)
                ·
                  refine ⟨194692580133681440047931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2076720854759268693844597 194692580133681440047931)
                  ·
                    rfl

theorem cell23_3412462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_3412462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412462 prefixEnd_3412462 := by exact prefixLift 3412462
  have htrace : WordTrace (prefixWord ++ tailWord_3412462) baseStart_3412462 baseEnd_3412462 := by
    simpa [prefixWord, tailWord_3412462, baseEnd_3412462] using wordTrace_append hprefix tailTrace_3412462
  have hstable : (prefixWord ++ tailWord_3412462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412462).length < 2 ^ (prefixWord ++ tailWord_3412462).sum := by decide
  have hdescent : baseEnd_3412462 < baseStart_3412462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412488 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 1, 10]
def baseStart_3412488 : Nat := 118140960795 + 3412488 * 2 ^ 59
def prefixEnd_3412488 : Nat := 4983230072969 + 3 ^ 40 * 3412488 * 2
def baseEnd_3412488 : Nat := 584082190566716619568753

theorem tailTrace_3412488 : CollatzResearch.WordTrace tailWord_3412488 prefixEnd_3412488 584082190566716619568753 := by
  unfold tailWord_3412488
  simp only [CollatzResearch.WordTrace]
  refine ⟨62231831230573128697955059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82975774974097504930606745 62231831230573128697955059)
  ·
    refine ⟨93347746845859693046932589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62231831230573128697955059 93347746845859693046932589)
    ·
      refine ⟨35005405067197384892599721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93347746845859693046932589 35005405067197384892599721)
      ·
        refine ⟨26254053800398038669449791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35005405067197384892599721 26254053800398038669449791)
        ·
          refine ⟨39381080700597058004174687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26254053800398038669449791 39381080700597058004174687)
          ·
            refine ⟨59071621050895587006262031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39381080700597058004174687 59071621050895587006262031)
            ·
              refine ⟨88607431576343380509393047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59071621050895587006262031 88607431576343380509393047)
              ·
                refine ⟨132911147364515070764089571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88607431576343380509393047 132911147364515070764089571)
                ·
                  refine ⟨199366721046772606146134357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132911147364515070764089571 199366721046772606146134357)
                  ·
                    refine ⟨584082190566716619568753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 199366721046772606146134357 584082190566716619568753)
                    ·
                      rfl

theorem cell23_3412488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_3412488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412488 prefixEnd_3412488 := by exact prefixLift 3412488
  have htrace : WordTrace (prefixWord ++ tailWord_3412488) baseStart_3412488 baseEnd_3412488 := by
    simpa [prefixWord, tailWord_3412488, baseEnd_3412488] using wordTrace_append hprefix tailTrace_3412488
  have hstable : (prefixWord ++ tailWord_3412488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412488).length < 2 ^ (prefixWord ++ tailWord_3412488).sum := by decide
  have hdescent : baseEnd_3412488 < baseStart_3412488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412495 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 3, 6, 2]
def baseStart_3412495 : Nat := 118140960795 + 3412495 * 2 ^ 59
def prefixEnd_3412495 : Nat := 4983230072969 + 3 ^ 40 * 3412495 * 2
def baseEnd_3412495 : Nat := 1752250166064731331318727

theorem tailTrace_3412495 : CollatzResearch.WordTrace tailWord_3412495 prefixEnd_3412495 1752250166064731331318727 := by
  unfold tailWord_3412495
  simp only [CollatzResearch.WordTrace]
  refine ⟨124463917772120897591414939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82975945181413931727609959 124463917772120897591414939)
  ·
    refine ⟨186695876658181346387122409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124463917772120897591414939 186695876658181346387122409)
    ·
      refine ⟨140021907493636009790341807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186695876658181346387122409 140021907493636009790341807)
      ·
        refine ⟨210032861240454014685512711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140021907493636009790341807 210032861240454014685512711)
        ·
          refine ⟨315049291860681022028269067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210032861240454014685512711 315049291860681022028269067)
          ·
            refine ⟨472573937791021533042403601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315049291860681022028269067 472573937791021533042403601)
            ·
              refine ⟨354430453343266149781802701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472573937791021533042403601 354430453343266149781802701)
              ·
                refine ⟨132911420003724806168176013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354430453343266149781802701 132911420003724806168176013)
                ·
                  refine ⟨49841782501396802313066005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132911420003724806168176013 49841782501396802313066005)
                  ·
                    refine ⟨2336333554752975108424969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49841782501396802313066005 2336333554752975108424969)
                    ·
                      refine ⟨1752250166064731331318727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336333554752975108424969 1752250166064731331318727)
                      ·
                        rfl

theorem cell23_3412495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 6, 2].length) (baseStart_3412495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412495 prefixEnd_3412495 := by exact prefixLift 3412495
  have htrace : WordTrace (prefixWord ++ tailWord_3412495) baseStart_3412495 baseEnd_3412495 := by
    simpa [prefixWord, tailWord_3412495, baseEnd_3412495] using wordTrace_append hprefix tailTrace_3412495
  have hstable : (prefixWord ++ tailWord_3412495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412495).length < 2 ^ (prefixWord ++ tailWord_3412495).sum := by decide
  have hdescent : baseEnd_3412495 < baseStart_3412495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412519 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3412519 : Nat := 118140960795 + 3412519 * 2 ^ 59
def prefixEnd_3412519 : Nat := 4983230072969 + 3 ^ 40 * 3412519 * 2
def baseEnd_3412519 : Nat := 1752262489600439237418617

theorem tailTrace_3412519 : CollatzResearch.WordTrace tailWord_3412519 prefixEnd_3412519 1752262489600439237418617 := by
  unfold tailWord_3412519
  simp only [CollatzResearch.WordTrace]
  refine ⟨124464793124033949690288611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82976528749355966460192407 124464793124033949690288611)
  ·
    refine ⟨186697189686050924535432917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124464793124033949690288611 186697189686050924535432917)
    ·
      refine ⟨4375715383266818543799209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 186697189686050924535432917 4375715383266818543799209)
      ·
        refine ⟨3281786537450113907849407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4375715383266818543799209 3281786537450113907849407)
        ·
          refine ⟨4922679806175170861774111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3281786537450113907849407 4922679806175170861774111)
          ·
            refine ⟨7384019709262756292661167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4922679806175170861774111 7384019709262756292661167)
            ·
              refine ⟨11076029563894134438991751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7384019709262756292661167 11076029563894134438991751)
              ·
                refine ⟨16614044345841201658487627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11076029563894134438991751 16614044345841201658487627)
                ·
                  refine ⟨24921066518761802487731441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16614044345841201658487627 24921066518761802487731441)
                  ·
                    refine ⟨18690799889071351865798581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24921066518761802487731441 18690799889071351865798581)
                    ·
                      refine ⟨1752262489600439237418617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18690799889071351865798581 1752262489600439237418617)
                      ·
                        rfl

theorem cell23_3412519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3412519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412519 prefixEnd_3412519 := by exact prefixLift 3412519
  have htrace : WordTrace (prefixWord ++ tailWord_3412519) baseStart_3412519 baseEnd_3412519 := by
    simpa [prefixWord, tailWord_3412519, baseEnd_3412519] using wordTrace_append hprefix tailTrace_3412519
  have hstable : (prefixWord ++ tailWord_3412519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412519).length < 2 ^ (prefixWord ++ tailWord_3412519).sum := by decide
  have hdescent : baseEnd_3412519 < baseStart_3412519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412535 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 6]
def baseStart_3412535 : Nat := 118140960795 + 3412535 * 2 ^ 59
def prefixEnd_3412535 : Nat := 4983230072969 + 3 ^ 40 * 3412535 * 2
def baseEnd_3412535 : Nat := 194696745032323463868727

theorem tailTrace_3412535 : CollatzResearch.WordTrace tailWord_3412535 prefixEnd_3412535 194696745032323463868727 := by
  unfold tailWord_3412535
  simp only [CollatzResearch.WordTrace]
  refine ⟨124465376691975984422871059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82976917794650656281914039 124465376691975984422871059)
  ·
    refine ⟨186698065037963976634306589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124465376691975984422871059 186698065037963976634306589)
    ·
      refine ⟨70011774389236491237864971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186698065037963976634306589 70011774389236491237864971)
      ·
        refine ⟨105017661583854736856797457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70011774389236491237864971 105017661583854736856797457)
        ·
          refine ⟨78763246187891052642598093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105017661583854736856797457 78763246187891052642598093)
          ·
            refine ⟨29536217320459144740974285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78763246187891052642598093 29536217320459144740974285)
            ·
              refine ⟨11076081495172179277865357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29536217320459144740974285 11076081495172179277865357)
              ·
                refine ⟨4153530560689567229199509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11076081495172179277865357 4153530560689567229199509)
                ·
                  refine ⟨194696745032323463868727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4153530560689567229199509 194696745032323463868727)
                  ·
                    rfl

theorem cell23_3412535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 6].length) (baseStart_3412535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412535 prefixEnd_3412535 := by exact prefixLift 3412535
  have htrace : WordTrace (prefixWord ++ tailWord_3412535) baseStart_3412535 baseEnd_3412535 := by
    simpa [prefixWord, tailWord_3412535, baseEnd_3412535] using wordTrace_append hprefix tailTrace_3412535
  have hstable : (prefixWord ++ tailWord_3412535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412535).length < 2 ^ (prefixWord ++ tailWord_3412535).sum := by decide
  have hdescent : baseEnd_3412535 < baseStart_3412535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412612 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_3412612 : Nat := 118140960795 + 3412612 * 2 ^ 59
def prefixEnd_3412612 : Nat := 4983230072969 + 3 ^ 40 * 3412612 * 2
def baseEnd_3412612 : Nat := 584103414433769124518563

theorem tailTrace_3412612 : CollatzResearch.WordTrace tailWord_3412612 prefixEnd_3412612 584103414433769124518563 := by
  unfold tailWord_3412612
  simp only [CollatzResearch.WordTrace]
  refine ⟨62234092556348513286712045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82978790075131351048949393 62234092556348513286712045)
  ·
    refine ⟨23337784708630692482517017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62234092556348513286712045 23337784708630692482517017)
    ·
      refine ⟨17503338531473019361887763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23337784708630692482517017 17503338531473019361887763)
      ·
        refine ⟨26255007797209529042831645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17503338531473019361887763 26255007797209529042831645)
        ·
          refine ⟨9845627923953573391061867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26255007797209529042831645 9845627923953573391061867)
          ·
            refine ⟨14768441885930360086592801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9845627923953573391061867 14768441885930360086592801)
            ·
              refine ⟨11076331414447770064944601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14768441885930360086592801 11076331414447770064944601)
              ·
                refine ⟨8307248560835827548708451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11076331414447770064944601 8307248560835827548708451)
                ·
                  refine ⟨12460872841253741323062677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8307248560835827548708451 12460872841253741323062677)
                  ·
                    refine ⟨584103414433769124518563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12460872841253741323062677 584103414433769124518563)
                    ·
                      rfl

theorem cell23_3412612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_3412612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412612 prefixEnd_3412612 := by exact prefixLift 3412612
  have htrace : WordTrace (prefixWord ++ tailWord_3412612) baseStart_3412612 baseEnd_3412612 := by
    simpa [prefixWord, tailWord_3412612, baseEnd_3412612] using wordTrace_append hprefix tailTrace_3412612
  have hstable : (prefixWord ++ tailWord_3412612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412612).length < 2 ^ (prefixWord ++ tailWord_3412612).sum := by decide
  have hdescent : baseEnd_3412612 < baseStart_3412612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412622 : List Nat := [4, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3412622 : Nat := 118140960795 + 3412622 * 2 ^ 59
def prefixEnd_3412622 : Nat := 4983230072969 + 3 ^ 40 * 3412622 * 2
def baseEnd_3412622 : Nat := 1752315378107852334430643

theorem tailTrace_3412622 : CollatzResearch.WordTrace tailWord_3412622 prefixEnd_3412622 1752315378107852334430643 := by
  unfold tailWord_3412622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15558568730332599785161015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82979033228440532187525413 15558568730332599785161015)
  ·
    refine ⟨23337853095498899677741523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15558568730332599785161015 23337853095498899677741523)
    ·
      refine ⟨35006779643248349516612285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23337853095498899677741523 35006779643248349516612285)
      ·
        refine ⟨13127542366218131068729607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35006779643248349516612285 13127542366218131068729607)
        ·
          refine ⟨19691313549327196603094411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13127542366218131068729607 19691313549327196603094411)
          ·
            refine ⟨29536970323990794904641617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19691313549327196603094411 29536970323990794904641617)
            ·
              refine ⟨22152727742993096178481213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29536970323990794904641617 22152727742993096178481213)
              ·
                refine ⟨8307272903622411066930455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22152727742993096178481213 8307272903622411066930455)
                ·
                  refine ⟨12460909355433616600395683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8307272903622411066930455 12460909355433616600395683)
                  ·
                    refine ⟨18691364033150424900593525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12460909355433616600395683 18691364033150424900593525)
                    ·
                      refine ⟨1752315378107852334430643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18691364033150424900593525 1752315378107852334430643)
                      ·
                        rfl

theorem cell23_3412622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3412622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412622 prefixEnd_3412622 := by exact prefixLift 3412622
  have htrace : WordTrace (prefixWord ++ tailWord_3412622) baseStart_3412622 baseEnd_3412622 := by
    simpa [prefixWord, tailWord_3412622, baseEnd_3412622] using wordTrace_append hprefix tailTrace_3412622
  have hstable : (prefixWord ++ tailWord_3412622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412622).length < 2 ^ (prefixWord ++ tailWord_3412622).sum := by decide
  have hdescent : baseEnd_3412622 < baseStart_3412622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412636 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_3412636 : Nat := 118140960795 + 3412636 * 2 ^ 59
def prefixEnd_3412636 : Nat := 4983230072969 + 3 ^ 40 * 3412636 * 2
def baseEnd_3412636 : Nat := 1752322566837015279655579

theorem tailTrace_3412636 : CollatzResearch.WordTrace tailWord_3412636 prefixEnd_3412636 1752322566837015279655579 := by
  unfold tailWord_3412636
  simp only [CollatzResearch.WordTrace]
  refine ⟨62234530232305039336148881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82979373643073385781531841 62234530232305039336148881)
  ·
    refine ⟨46675897674228779502111661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62234530232305039336148881 46675897674228779502111661)
    ·
      refine ⟨17503461627835792313291873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46675897674228779502111661 17503461627835792313291873)
      ·
        refine ⟨13127596220876844234968905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17503461627835792313291873 13127596220876844234968905)
        ·
          refine ⟨9845697165657633176226679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13127596220876844234968905 9845697165657633176226679)
          ·
            refine ⟨14768545748486449764340019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9845697165657633176226679 14768545748486449764340019)
            ·
              refine ⟨22152818622729674646510029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14768545748486449764340019 22152818622729674646510029)
              ·
                refine ⟨8307306983523627992441261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22152818622729674646510029 8307306983523627992441261)
                ·
                  refine ⟨3115240118821360497165473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8307306983523627992441261 3115240118821360497165473)
                  ·
                    refine ⟨2336430089116020372874105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3115240118821360497165473 2336430089116020372874105)
                    ·
                      refine ⟨1752322566837015279655579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336430089116020372874105 1752322566837015279655579)
                      ·
                        rfl

theorem cell23_3412636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_3412636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412636 prefixEnd_3412636 := by exact prefixLift 3412636
  have htrace : WordTrace (prefixWord ++ tailWord_3412636) baseStart_3412636 baseEnd_3412636 := by
    simpa [prefixWord, tailWord_3412636, baseEnd_3412636] using wordTrace_append hprefix tailTrace_3412636
  have hstable : (prefixWord ++ tailWord_3412636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412636).length < 2 ^ (prefixWord ++ tailWord_3412636).sum := by decide
  have hdescent : baseEnd_3412636 < baseStart_3412636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412669 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_3412669 : Nat := 118140960795 + 3412669 * 2 ^ 59
def prefixEnd_3412669 : Nat := 4983230072969 + 3 ^ 40 * 3412669 * 2
def baseEnd_3412669 : Nat := 1752339511698613650542927

theorem tailTrace_3412669 : CollatzResearch.WordTrace tailWord_3412669 prefixEnd_3412669 1752339511698613650542927 := by
  unfold tailWord_3412669
  simp only [CollatzResearch.WordTrace]
  refine ⟨124470264073490525308249061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82980176048993683538832707 124470264073490525308249061)
  ·
    refine ⟨23338174513779473495296699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124470264073490525308249061 23338174513779473495296699)
    ·
      refine ⟨35007261770669210242945049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23338174513779473495296699 35007261770669210242945049)
      ·
        refine ⟨26255446328001907682208787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35007261770669210242945049 26255446328001907682208787)
        ·
          refine ⟨39383169492002861523313181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26255446328001907682208787 39383169492002861523313181)
          ·
            refine ⟨14768688559501073071242443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39383169492002861523313181 14768688559501073071242443)
            ·
              refine ⟨22153032839251609606863665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14768688559501073071242443 22153032839251609606863665)
              ·
                refine ⟨16614774629438707205147749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22153032839251609606863665 16614774629438707205147749)
                ·
                  refine ⟨3115270243019757600965203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16614774629438707205147749 3115270243019757600965203)
                  ·
                    refine ⟨4672905364529636401447805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3115270243019757600965203 4672905364529636401447805)
                    ·
                      refine ⟨1752339511698613650542927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4672905364529636401447805 1752339511698613650542927)
                      ·
                        rfl

theorem cell23_3412669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_3412669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412669 prefixEnd_3412669 := by exact prefixLift 3412669
  have htrace : WordTrace (prefixWord ++ tailWord_3412669) baseStart_3412669 baseEnd_3412669 := by
    simpa [prefixWord, tailWord_3412669, baseEnd_3412669] using wordTrace_append hprefix tailTrace_3412669
  have hstable : (prefixWord ++ tailWord_3412669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412669).length < 2 ^ (prefixWord ++ tailWord_3412669).sum := by decide
  have hdescent : baseEnd_3412669 < baseStart_3412669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412703 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 2, 1, 3]
def baseStart_3412703 : Nat := 118140960795 + 3412703 * 2 ^ 59
def prefixEnd_3412703 : Nat := 4983230072969 + 3 ^ 40 * 3412703 * 2
def baseEnd_3412703 : Nat := 1752356970040866517517771

theorem tailTrace_3412703 : CollatzResearch.WordTrace tailWord_3412703 prefixEnd_3412703 1752356970040866517517771 := by
  unfold tailWord_3412703
  simp only [CollatzResearch.WordTrace]
  refine ⟨124471504155367349114986763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82981002770244899409991175 124471504155367349114986763)
  ·
    refine ⟨186707256233051023672480145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124471504155367349114986763 186707256233051023672480145)
    ·
      refine ⟨140030442174788267754360109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186707256233051023672480145 140030442174788267754360109)
      ·
        refine ⟨52511415815545600407885041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140030442174788267754360109 52511415815545600407885041)
        ·
          refine ⟨39383561861659200305913781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52511415815545600407885041 39383561861659200305913781)
          ·
            refine ⟨3692208924530550028679417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39383561861659200305913781 3692208924530550028679417)
            ·
              refine ⟨2769156693397912521509563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3692208924530550028679417 2769156693397912521509563)
              ·
                refine ⟨4153735040096868782264345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769156693397912521509563 4153735040096868782264345)
                ·
                  refine ⟨3115301280072651586698259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4153735040096868782264345 3115301280072651586698259)
                  ·
                    refine ⟨4672951920108977380047389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3115301280072651586698259 4672951920108977380047389)
                    ·
                      refine ⟨1752356970040866517517771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4672951920108977380047389 1752356970040866517517771)
                      ·
                        rfl

theorem cell23_3412703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 2, 1, 3].length) (baseStart_3412703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412703 prefixEnd_3412703 := by exact prefixLift 3412703
  have htrace : WordTrace (prefixWord ++ tailWord_3412703) baseStart_3412703 baseEnd_3412703 := by
    simpa [prefixWord, tailWord_3412703, baseEnd_3412703] using wordTrace_append hprefix tailTrace_3412703
  have hstable : (prefixWord ++ tailWord_3412703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412703).length < 2 ^ (prefixWord ++ tailWord_3412703).sum := by decide
  have hdescent : baseEnd_3412703 < baseStart_3412703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412715 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 9]
def baseStart_3412715 : Nat := 118140960795 + 3412715 * 2 ^ 59
def prefixEnd_3412715 : Nat := 4983230072969 + 3 ^ 40 * 3412715 * 2
def baseEnd_3412715 : Nat := 194707014645413385618635

theorem tailTrace_3412715 : CollatzResearch.WordTrace tailWord_3412715 prefixEnd_3412715 194707014645413385618635 := by
  unfold tailWord_3412715
  simp only [CollatzResearch.WordTrace]
  refine ⟨124471941831323875164423599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82981294554215916776282399 124471941831323875164423599)
  ·
    refine ⟨186707912746985812746635399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124471941831323875164423599 186707912746985812746635399)
    ·
      refine ⟨280061869120478719119953099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186707912746985812746635399 280061869120478719119953099)
      ·
        refine ⟨420092803680718078679929649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280061869120478719119953099 420092803680718078679929649)
        ·
          refine ⟨315069602760538559009947237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420092803680718078679929649 315069602760538559009947237)
          ·
            refine ⟨59075550517600979814365107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 315069602760538559009947237 59075550517600979814365107)
            ·
              refine ⟨88613325776401469721547661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59075550517600979814365107 88613325776401469721547661)
              ·
                refine ⟨33229997166150551145580373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88613325776401469721547661 33229997166150551145580373)
                ·
                  refine ⟨194707014645413385618635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33229997166150551145580373 194707014645413385618635)
                  ·
                    rfl

theorem cell23_3412715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 9].length) (baseStart_3412715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412715 prefixEnd_3412715 := by exact prefixLift 3412715
  have htrace : WordTrace (prefixWord ++ tailWord_3412715) baseStart_3412715 baseEnd_3412715 := by
    simpa [prefixWord, tailWord_3412715, baseEnd_3412715] using wordTrace_append hprefix tailTrace_3412715
  have hstable : (prefixWord ++ tailWord_3412715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412715).length < 2 ^ (prefixWord ++ tailWord_3412715).sum := by decide
  have hdescent : baseEnd_3412715 < baseStart_3412715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412726 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_3412726 : Nat := 118140960795 + 3412726 * 2 ^ 59
def prefixEnd_3412726 : Nat := 4983230072969 + 3 ^ 40 * 3412726 * 2
def baseEnd_3412726 : Nat := 1752368780095919927530165

theorem tailTrace_3412726 : CollatzResearch.WordTrace tailWord_3412726 prefixEnd_3412726 1752368780095919927530165 := by
  unfold tailWord_3412726
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779521439642751502692127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82981562022856016028716021 7779521439642751502692127)
  ·
    refine ⟨11669282159464127254038191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7779521439642751502692127 11669282159464127254038191)
    ·
      refine ⟨17503923239196190881057287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11669282159464127254038191 17503923239196190881057287)
      ·
        refine ⟨26255884858794286321585931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17503923239196190881057287 26255884858794286321585931)
        ·
          refine ⟨39383827288191429482378897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26255884858794286321585931 39383827288191429482378897)
          ·
            refine ⟨29537870466143572111784173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39383827288191429482378897 29537870466143572111784173)
            ·
              refine ⟨11076701424803839541919065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29537870466143572111784173 11076701424803839541919065)
              ·
                refine ⟨8307526068602879656439299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11076701424803839541919065 8307526068602879656439299)
                ·
                  refine ⟨12461289102904319484658949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8307526068602879656439299 12461289102904319484658949)
                  ·
                    refine ⟨2336491706794559903373553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12461289102904319484658949 2336491706794559903373553)
                    ·
                      refine ⟨1752368780095919927530165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336491706794559903373553 1752368780095919927530165)
                      ·
                        rfl

theorem cell23_3412726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_3412726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412726 prefixEnd_3412726 := by exact prefixLift 3412726
  have htrace : WordTrace (prefixWord ++ tailWord_3412726) baseStart_3412726 baseEnd_3412726 := by
    simpa [prefixWord, tailWord_3412726, baseEnd_3412726] using wordTrace_append hprefix tailTrace_3412726
  have hstable : (prefixWord ++ tailWord_3412726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412726).length < 2 ^ (prefixWord ++ tailWord_3412726).sum := by decide
  have hdescent : baseEnd_3412726 < baseStart_3412726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412743 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 2, 2, 2]
def baseStart_3412743 : Nat := 118140960795 + 3412743 * 2 ^ 59
def prefixEnd_3412743 : Nat := 4983230072969 + 3 ^ 40 * 3412743 * 2
def baseEnd_3412743 : Nat := 1752377509267046361017587

theorem tailTrace_3412743 : CollatzResearch.WordTrace tailWord_3412743 prefixEnd_3412743 1752377509267046361017587 := by
  unfold tailWord_3412743
  simp only [CollatzResearch.WordTrace]
  refine ⟨124472963075222435946442883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82981975383481623964295255 124472963075222435946442883)
  ·
    refine ⟨186709444612833653919664325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124472963075222435946442883 186709444612833653919664325)
    ·
      refine ⟨35008020864906310109937061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186709444612833653919664325 35008020864906310109937061)
      ·
        refine ⟨6564003912169933145613199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35008020864906310109937061 6564003912169933145613199)
        ·
          refine ⟨9846005868254899718419799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6564003912169933145613199 9846005868254899718419799)
          ·
            refine ⟨14769008802382349577629699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9846005868254899718419799 14769008802382349577629699)
            ·
              refine ⟨22153513203573524366444549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14769008802382349577629699 22153513203573524366444549)
              ·
                refine ⟨4153783725670035818708353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22153513203573524366444549 4153783725670035818708353)
                ·
                  refine ⟨3115337794252526864031265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4153783725670035818708353 3115337794252526864031265)
                  ·
                    refine ⟨2336503345689395148023449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3115337794252526864031265 2336503345689395148023449)
                    ·
                      refine ⟨1752377509267046361017587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336503345689395148023449 1752377509267046361017587)
                      ·
                        rfl

theorem cell23_3412743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_3412743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412743 prefixEnd_3412743 := by exact prefixLift 3412743
  have htrace : WordTrace (prefixWord ++ tailWord_3412743) baseStart_3412743 baseEnd_3412743 := by
    simpa [prefixWord, tailWord_3412743, baseEnd_3412743] using wordTrace_append hprefix tailTrace_3412743
  have hstable : (prefixWord ++ tailWord_3412743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412743).length < 2 ^ (prefixWord ++ tailWord_3412743).sum := by decide
  have hdescent : baseEnd_3412743 < baseStart_3412743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412762 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_3412762 : Nat := 118140960795 + 3412762 * 2 ^ 59
def prefixEnd_3412762 : Nat := 4983230072969 + 3 ^ 40 * 3412762 * 2
def baseEnd_3412762 : Nat := 584129088466493928893333

theorem tailTrace_3412762 : CollatzResearch.WordTrace tailWord_3412762 prefixEnd_3412762 584129088466493928893333 := by
  unfold tailWord_3412762
  simp only [CollatzResearch.WordTrace]
  refine ⟨31118414015538400547846135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82982437374769068127589693 31118414015538400547846135)
  ·
    refine ⟨46677621023307600821769203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31118414015538400547846135 46677621023307600821769203)
    ·
      refine ⟨70016431534961401232653805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46677621023307600821769203 70016431534961401232653805)
      ·
        refine ⟨26256161825610525462245177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70016431534961401232653805 26256161825610525462245177)
        ·
          refine ⟨19692121369207894096683883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26256161825610525462245177 19692121369207894096683883)
          ·
            refine ⟨29538182053811841145025825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19692121369207894096683883 29538182053811841145025825)
            ·
              refine ⟨22153636540358880858769369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29538182053811841145025825 22153636540358880858769369)
              ·
                refine ⟨16615227405269160644077027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22153636540358880858769369 16615227405269160644077027)
                ·
                  refine ⟨24922841107903740966115541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16615227405269160644077027 24922841107903740966115541)
                  ·
                    refine ⟨584129088466493928893333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24922841107903740966115541 584129088466493928893333)
                    ·
                      rfl

theorem cell23_3412762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_3412762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412762 prefixEnd_3412762 := by exact prefixLift 3412762
  have htrace : WordTrace (prefixWord ++ tailWord_3412762) baseStart_3412762 baseEnd_3412762 := by
    simpa [prefixWord, tailWord_3412762, baseEnd_3412762] using wordTrace_append hprefix tailTrace_3412762
  have hstable : (prefixWord ++ tailWord_3412762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412762).length < 2 ^ (prefixWord ++ tailWord_3412762).sum := by decide
  have hdescent : baseEnd_3412762 < baseStart_3412762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412769 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 2, 5, 2]
def baseStart_3412769 : Nat := 118140960795 + 3412769 * 2 ^ 59
def prefixEnd_3412769 : Nat := 4983230072969 + 3 ^ 40 * 3412769 * 2
def baseEnd_3412769 : Nat := 1752390859764063259292467

theorem tailTrace_3412769 : CollatzResearch.WordTrace tailWord_3412769 prefixEnd_3412769 1752390859764063259292467 := by
  unfold tailWord_3412769
  simp only [CollatzResearch.WordTrace]
  refine ⟨124473911373128242386889361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82982607582085494924592907 124473911373128242386889361)
  ·
    refine ⟨93355433529846181790167021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124473911373128242386889361 93355433529846181790167021)
    ·
      refine ⟨35008287573692318171312633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93355433529846181790167021 35008287573692318171312633)
      ·
        refine ⟨26256215680269238628484475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35008287573692318171312633 26256215680269238628484475)
        ·
          refine ⟨39384323520403857942726713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26256215680269238628484475 39384323520403857942726713)
          ·
            refine ⟨29538242640302893457045035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39384323520403857942726713 29538242640302893457045035)
            ·
              refine ⟨44307363960454340185567553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29538242640302893457045035 44307363960454340185567553)
              ·
                refine ⟨33230522970340755139175665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44307363960454340185567553 33230522970340755139175665)
                ·
                  refine ⟨24922892227755566354381749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33230522970340755139175665 24922892227755566354381749)
                  ·
                    refine ⟨2336521146352084345723289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24922892227755566354381749 2336521146352084345723289)
                    ·
                      refine ⟨1752390859764063259292467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336521146352084345723289 1752390859764063259292467)
                      ·
                        rfl

theorem cell23_3412769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_3412769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412769 prefixEnd_3412769 := by exact prefixLift 3412769
  have htrace : WordTrace (prefixWord ++ tailWord_3412769) baseStart_3412769 baseEnd_3412769 := by
    simpa [prefixWord, tailWord_3412769, baseEnd_3412769] using wordTrace_append hprefix tailTrace_3412769
  have hstable : (prefixWord ++ tailWord_3412769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412769).length < 2 ^ (prefixWord ++ tailWord_3412769).sum := by decide
  have hdescent : baseEnd_3412769 < baseStart_3412769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412809 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 3, 4]
def baseStart_3412809 : Nat := 118140960795 + 3412809 * 2 ^ 59
def prefixEnd_3412809 : Nat := 4983230072969 + 3 ^ 40 * 3412809 * 2
def baseEnd_3412809 : Nat := 584137132996747700930761

theorem tailTrace_3412809 : CollatzResearch.WordTrace tailWord_3412809 prefixEnd_3412809 584137132996747700930761 := by
  unfold tailWord_3412809
  simp only [CollatzResearch.WordTrace]
  refine ⟨124475370292983329218345481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82983580195322219478896987 124475370292983329218345481)
  ·
    refine ⟨93356527719737496913759111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124475370292983329218345481 93356527719737496913759111)
    ·
      refine ⟨140034791579606245370638667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93356527719737496913759111 140034791579606245370638667)
      ·
        refine ⟨210052187369409368055958001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140034791579606245370638667 210052187369409368055958001)
        ·
          refine ⟨157539140527057026041968501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210052187369409368055958001 157539140527057026041968501)
          ·
            refine ⟨14769294424411596191434547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157539140527057026041968501 14769294424411596191434547)
            ·
              refine ⟨22153941636617394287151821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14769294424411596191434547 22153941636617394287151821)
              ·
                refine ⟨8307728113731522857681933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22153941636617394287151821 8307728113731522857681933)
                ·
                  refine ⟨3115398042649321071630725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8307728113731522857681933 3115398042649321071630725)
                  ·
                    refine ⟨584137132996747700930761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3115398042649321071630725 584137132996747700930761)
                    ·
                      rfl

theorem cell23_3412809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 4].length) (baseStart_3412809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412809 prefixEnd_3412809 := by exact prefixLift 3412809
  have htrace : WordTrace (prefixWord ++ tailWord_3412809) baseStart_3412809 baseEnd_3412809 := by
    simpa [prefixWord, tailWord_3412809, baseEnd_3412809] using wordTrace_append hprefix tailTrace_3412809
  have hstable : (prefixWord ++ tailWord_3412809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412809).length < 2 ^ (prefixWord ++ tailWord_3412809).sum := by decide
  have hdescent : baseEnd_3412809 < baseStart_3412809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412893 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_3412893 : Nat := 118140960795 + 3412893 * 2 ^ 59
def prefixEnd_3412893 : Nat := 4983230072969 + 3 ^ 40 * 3412893 * 2
def baseEnd_3412893 : Nat := 1752454531365220774141897

theorem tailTrace_3412893 : CollatzResearch.WordTrace tailWord_3412893 prefixEnd_3412893 1752454531365220774141897 := by
  unfold tailWord_3412893
  simp only [CollatzResearch.WordTrace]
  refine ⟨124478434024679011564403333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82985622683119341042935555 124478434024679011564403333)
  ·
    refine ⟨23339706379627314668325625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124478434024679011564403333 23339706379627314668325625)
    ·
      refine ⟨17504779784720486001244219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23339706379627314668325625 17504779784720486001244219)
      ·
        refine ⟨26257169677080729001866329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17504779784720486001244219 26257169677080729001866329)
        ·
          refine ⟨19692877257810546751399747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26257169677080729001866329 19692877257810546751399747)
          ·
            refine ⟨29539315886715820127099621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19692877257810546751399747 29539315886715820127099621)
            ·
              refine ⟨5538621728759216273831179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29539315886715820127099621 5538621728759216273831179)
              ·
                refine ⟨8307932593138824410746769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5538621728759216273831179 8307932593138824410746769)
                ·
                  refine ⟨6230949444854118308060077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8307932593138824410746769 6230949444854118308060077)
                  ·
                    refine ⟨2336606041820294365522529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6230949444854118308060077 2336606041820294365522529)
                    ·
                      refine ⟨1752454531365220774141897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336606041820294365522529 1752454531365220774141897)
                      ·
                        rfl

theorem cell23_3412893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_3412893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412893 prefixEnd_3412893 := by exact prefixLift 3412893
  have htrace : WordTrace (prefixWord ++ tailWord_3412893) baseStart_3412893 baseEnd_3412893 := by
    simpa [prefixWord, tailWord_3412893, baseEnd_3412893] using wordTrace_append hprefix tailTrace_3412893
  have hstable : (prefixWord ++ tailWord_3412893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412893).length < 2 ^ (prefixWord ++ tailWord_3412893).sum := by decide
  have hdescent : baseEnd_3412893 < baseStart_3412893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412899 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 6, 4]
def baseStart_3412899 : Nat := 118140960795 + 3412899 * 2 ^ 59
def prefixEnd_3412899 : Nat := 4983230072969 + 3 ^ 40 * 3412899 * 2
def baseEnd_3412899 : Nat := 584152537416382583555623

theorem tailTrace_3412899 : CollatzResearch.WordTrace tailWord_3412899 prefixEnd_3412899 584152537416382583555623 := by
  unfold tailWord_3412899
  simp only [CollatzResearch.WordTrace]
  refine ⟨124478652862657274589121751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82985768575104849726081167 124478652862657274589121751)
  ·
    refine ⟨186717979293985911883682627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124478652862657274589121751 186717979293985911883682627)
    ·
      refine ⟨280076968940978867825523941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186717979293985911883682627 280076968940978867825523941)
      ·
        refine ⟨52514431676433537717285739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280076968940978867825523941 52514431676433537717285739)
        ·
          refine ⟨78771647514650306575928609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52514431676433537717285739 78771647514650306575928609)
          ·
            refine ⟨59078735635987729931946457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78771647514650306575928609 59078735635987729931946457)
            ·
              refine ⟨44309051726990797448959843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59078735635987729931946457 44309051726990797448959843)
              ·
                refine ⟨66463577590486196173439765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44309051726990797448959843 66463577590486196173439765)
                ·
                  refine ⟨3115480199554040445629989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66463577590486196173439765 3115480199554040445629989)
                  ·
                    refine ⟨584152537416382583555623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3115480199554040445629989 584152537416382583555623)
                    ·
                      rfl

theorem cell23_3412899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 4].length) (baseStart_3412899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412899 prefixEnd_3412899 := by exact prefixLift 3412899
  have htrace : WordTrace (prefixWord ++ tailWord_3412899) baseStart_3412899 baseEnd_3412899 := by
    simpa [prefixWord, tailWord_3412899, baseEnd_3412899] using wordTrace_append hprefix tailTrace_3412899
  have hstable : (prefixWord ++ tailWord_3412899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412899).length < 2 ^ (prefixWord ++ tailWord_3412899).sum := by decide
  have hdescent : baseEnd_3412899 < baseStart_3412899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412926 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_3412926 : Nat := 118140960795 + 3412926 * 2 ^ 59
def prefixEnd_3412926 : Nat := 4983230072969 + 3 ^ 40 * 3412926 * 2
def baseEnd_3412926 : Nat := 1752471476226819145029245

theorem tailTrace_3412926 : CollatzResearch.WordTrace tailWord_3412926 prefixEnd_3412926 1752471476226819145029245 := by
  unfold tailWord_3412926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15559954704194932275044329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82986425089039638800236421 15559954704194932275044329)
  ·
    refine ⟨11669966028146199206283247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15559954704194932275044329 11669966028146199206283247)
    ·
      refine ⟨17504949042219298809424871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11669966028146199206283247 17504949042219298809424871)
      ·
        refine ⟨26257423563328948214137307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17504949042219298809424871 26257423563328948214137307)
        ·
          refine ⟨39386135344993422321205961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26257423563328948214137307 39386135344993422321205961)
          ·
            refine ⟨29539601508745066740904471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39386135344993422321205961 29539601508745066740904471)
            ·
              refine ⟨44309402263117600111356707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29539601508745066740904471 44309402263117600111356707)
              ·
                refine ⟨66464103394676400167035061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44309402263117600111356707 66464103394676400167035061)
                ·
                  refine ⟨6231009693250912515659537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66464103394676400167035061 6231009693250912515659537)
                  ·
                    refine ⟨4673257269938184386744653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6231009693250912515659537 4673257269938184386744653)
                    ·
                      refine ⟨1752471476226819145029245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4673257269938184386744653 1752471476226819145029245)
                      ·
                        rfl

theorem cell23_3412926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_3412926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412926 prefixEnd_3412926 := by exact prefixLift 3412926
  have htrace : WordTrace (prefixWord ++ tailWord_3412926) baseStart_3412926 baseEnd_3412926 := by
    simpa [prefixWord, tailWord_3412926, baseEnd_3412926] using wordTrace_append hprefix tailTrace_3412926
  have hstable : (prefixWord ++ tailWord_3412926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412926).length < 2 ^ (prefixWord ++ tailWord_3412926).sum := by decide
  have hdescent : baseEnd_3412926 < baseStart_3412926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412957 : List Nat := [1, 4, 3, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_3412957 : Nat := 118140960795 + 3412957 * 2 ^ 59
def prefixEnd_3412957 : Nat := 4983230072969 + 3 ^ 40 * 3412957 * 2
def baseEnd_3412957 : Nat := 1752487394127108523741603

theorem tailTrace_3412957 : CollatzResearch.WordTrace tailWord_3412957 prefixEnd_3412957 1752487394127108523741603 := by
  unfold tailWord_3412957
  simp only [CollatzResearch.WordTrace]
  refine ⟨124480768296447150494733125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82987178864298100329822083 124480768296447150494733125)
  ·
    refine ⟨23340144055583840717762461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124480768296447150494733125 23340144055583840717762461)
    ·
      refine ⟨8752554020843940269160923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23340144055583840717762461 8752554020843940269160923)
      ·
        refine ⟨13128831031265910403741385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8752554020843940269160923 13128831031265910403741385)
        ·
          refine ⟨9846623273449432802806039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13128831031265910403741385 9846623273449432802806039)
          ·
            refine ⟨14769934910174149204209059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9846623273449432802806039 14769934910174149204209059)
            ·
              refine ⟨22154902365261223806313589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14769934910174149204209059 22154902365261223806313589)
              ·
                refine ⟨2077022096743239731841899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22154902365261223806313589 2077022096743239731841899)
                ·
                  refine ⟨3115533145114859597762849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077022096743239731841899 3115533145114859597762849)
                  ·
                    refine ⟨2336649858836144698322137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3115533145114859597762849 2336649858836144698322137)
                    ·
                      refine ⟨1752487394127108523741603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336649858836144698322137 1752487394127108523741603)
                      ·
                        rfl

theorem cell23_3412957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_3412957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3412957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3412957 prefixEnd_3412957 := by exact prefixLift 3412957
  have htrace : WordTrace (prefixWord ++ tailWord_3412957) baseStart_3412957 baseEnd_3412957 := by
    simpa [prefixWord, tailWord_3412957, baseEnd_3412957] using wordTrace_append hprefix tailTrace_3412957
  have hstable : (prefixWord ++ tailWord_3412957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412957).length < 2 ^ (prefixWord ++ tailWord_3412957).sum := by decide
  have hdescent : baseEnd_3412957 < baseStart_3412957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413000 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 1, 3, 2]
def baseStart_3413000 : Nat := 118140960795 + 3413000 * 2 ^ 59
def prefixEnd_3413000 : Nat := 4983230072969 + 3 ^ 40 * 3413000 * 2
def baseEnd_3413000 : Nat := 1752509473795251855503905

theorem tailTrace_3413000 : CollatzResearch.WordTrace tailWord_3413000 prefixEnd_3413000 1752509473795251855503905 := by
  unfold tailWord_3413000
  simp only [CollatzResearch.WordTrace]
  refine ⟨62241168317645684419274227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82988224423527579225698969 62241168317645684419274227)
  ·
    refine ⟨93361752476468526628911341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62241168317645684419274227 93361752476468526628911341)
    ·
      refine ⟨35010657178675697485841753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93361752476468526628911341 35010657178675697485841753)
      ·
        refine ⟨26257992884006773114381315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35010657178675697485841753 26257992884006773114381315)
        ·
          refine ⟨39386989326010159671571973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26257992884006773114381315 39386989326010159671571973)
          ·
            refine ⟨7385060498626904938419745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39386989326010159671571973 7385060498626904938419745)
            ·
              refine ⟨5538795373970178703814809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7385060498626904938419745 5538795373970178703814809)
              ·
                refine ⟨4154096530477634027861107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5538795373970178703814809 4154096530477634027861107)
                ·
                  refine ⟨6231144795716451041791661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154096530477634027861107 6231144795716451041791661)
                  ·
                    refine ⟨2336679298393669140671873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6231144795716451041791661 2336679298393669140671873)
                    ·
                      refine ⟨1752509473795251855503905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336679298393669140671873 1752509473795251855503905)
                      ·
                        rfl

theorem cell23_3413000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_3413000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413000 prefixEnd_3413000 := by exact prefixLift 3413000
  have htrace : WordTrace (prefixWord ++ tailWord_3413000) baseStart_3413000 baseEnd_3413000 := by
    simpa [prefixWord, tailWord_3413000, baseEnd_3413000] using wordTrace_append hprefix tailTrace_3413000
  have hstable : (prefixWord ++ tailWord_3413000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413000).length < 2 ^ (prefixWord ++ tailWord_3413000).sum := by decide
  have hdescent : baseEnd_3413000 < baseStart_3413000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413009 : List Nat := [1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_3413009 : Nat := 118140960795 + 3413009 * 2 ^ 59
def prefixEnd_3413009 : Nat := 4983230072969 + 3 ^ 40 * 3413009 * 2
def baseEnd_3413009 : Nat := 1752514095121142320291363

theorem tailTrace_3413009 : CollatzResearch.WordTrace tailWord_3413009 prefixEnd_3413009 1752514095121142320291363 := by
  unfold tailWord_3413009
  simp only [CollatzResearch.WordTrace]
  refine ⟨124482664892258763375626081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82988443261505842250417387 124482664892258763375626081)
  ·
    refine ⟨93361998669194072531719561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124482664892258763375626081 93361998669194072531719561)
    ·
      refine ⟨70021499001895554398789671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93361998669194072531719561 70021499001895554398789671)
      ·
        refine ⟨105032248502843331598184507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70021499001895554398789671 105032248502843331598184507)
        ·
          refine ⟨157548372754264997397276761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105032248502843331598184507 157548372754264997397276761)
          ·
            refine ⟨118161279565698748047957571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157548372754264997397276761 118161279565698748047957571)
            ·
              refine ⟨177241919348548122071936357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118161279565698748047957571 177241919348548122071936357)
              ·
                refine ⟨33232859877852772888488067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177241919348548122071936357 33232859877852772888488067)
                ·
                  refine ⟨49849289816779159332732101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33232859877852772888488067 49849289816779159332732101)
                  ·
                    refine ⟨9346741840646092374887269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49849289816779159332732101 9346741840646092374887269)
                    ·
                      refine ⟨1752514095121142320291363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9346741840646092374887269 1752514095121142320291363)
                      ·
                        rfl

theorem cell23_3413009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_3413009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413009 prefixEnd_3413009 := by exact prefixLift 3413009
  have htrace : WordTrace (prefixWord ++ tailWord_3413009) baseStart_3413009 baseEnd_3413009 := by
    simpa [prefixWord, tailWord_3413009, baseEnd_3413009] using wordTrace_append hprefix tailTrace_3413009
  have hstable : (prefixWord ++ tailWord_3413009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413009).length < 2 ^ (prefixWord ++ tailWord_3413009).sum := by decide
  have hdescent : baseEnd_3413009 < baseStart_3413009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413016 : List Nat := [2, 1, 2, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3413016 : Nat := 118140960795 + 3413016 * 2 ^ 59
def prefixEnd_3413016 : Nat := 4983230072969 + 3 ^ 40 * 3413016 * 2
def baseEnd_3413016 : Nat := 1752517689485723792903831

theorem tailTrace_3413016 : CollatzResearch.WordTrace tailWord_3413016 prefixEnd_3413016 1752517689485723792903831 := by
  unfold tailWord_3413016
  simp only [CollatzResearch.WordTrace]
  refine ⟨62241460101616701785565451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82988613468822269047420601 62241460101616701785565451)
  ·
    refine ⟨93362190152425052678348177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62241460101616701785565451 93362190152425052678348177)
    ·
      refine ⟨70021642614318789508761133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93362190152425052678348177 70021642614318789508761133)
      ·
        refine ⟨26258115980369546065785425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70021642614318789508761133 26258115980369546065785425)
        ·
          refine ⟨19693586985277159549339069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26258115980369546065785425 19693586985277159549339069)
          ·
            refine ⟨7385095119478934831002151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19693586985277159549339069 7385095119478934831002151)
            ·
              refine ⟨11077642679218402246503227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7385095119478934831002151 11077642679218402246503227)
              ·
                refine ⟨16616464018827603369754841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11077642679218402246503227 16616464018827603369754841)
                ·
                  refine ⟨12462348014120702527316131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16616464018827603369754841 12462348014120702527316131)
                  ·
                    refine ⟨18693522021181053790974197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12462348014120702527316131 18693522021181053790974197)
                    ·
                      refine ⟨1752517689485723792903831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18693522021181053790974197 1752517689485723792903831)
                      ·
                        rfl

theorem cell23_3413016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3413016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413016 prefixEnd_3413016 := by exact prefixLift 3413016
  have htrace : WordTrace (prefixWord ++ tailWord_3413016) baseStart_3413016 baseEnd_3413016 := by
    simpa [prefixWord, tailWord_3413016, baseEnd_3413016] using wordTrace_append hprefix tailTrace_3413016
  have hstable : (prefixWord ++ tailWord_3413016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413016).length < 2 ^ (prefixWord ++ tailWord_3413016).sum := by decide
  have hdescent : baseEnd_3413016 < baseStart_3413016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413029 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_3413029 : Nat := 118140960795 + 3413029 * 2 ^ 59
def prefixEnd_3413029 : Nat := 4983230072969 + 3 ^ 40 * 3413029 * 2
def baseEnd_3413029 : Nat := 1752524364734232242041271

theorem tailTrace_3413029 : CollatzResearch.WordTrace tailWord_3413029 prefixEnd_3413029 1752524364734232242041271 := by
  unfold tailWord_3413029
  simp only [CollatzResearch.WordTrace]
  refine ⟨124483394352186306791354141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82988929568124204527569427 124483394352186306791354141)
  ·
    refine ⟨46681272882069865046757803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124483394352186306791354141 46681272882069865046757803)
    ·
      refine ⟨70021909323104797570136705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46681272882069865046757803 70021909323104797570136705)
      ·
        refine ⟨52516431992328598177602529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70021909323104797570136705 52516431992328598177602529)
        ·
          refine ⟨39387323994246448633201897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52516431992328598177602529 39387323994246448633201897)
          ·
            refine ⟨29540492995684836474901423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39387323994246448633201897 29540492995684836474901423)
            ·
              refine ⟨44310739493527254712352135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29540492995684836474901423 44310739493527254712352135)
              ·
                refine ⟨66466109240290882068528203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44310739493527254712352135 66466109240290882068528203)
                ·
                  refine ⟨99699163860436323102792305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66466109240290882068528203 99699163860436323102792305)
                  ·
                    refine ⟨74774372895327242327094229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99699163860436323102792305 74774372895327242327094229)
                    ·
                      refine ⟨1752524364734232242041271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74774372895327242327094229 1752524364734232242041271)
                      ·
                        rfl

theorem cell23_3413029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_3413029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413029 prefixEnd_3413029 := by exact prefixLift 3413029
  have htrace : WordTrace (prefixWord ++ tailWord_3413029) baseStart_3413029 baseEnd_3413029 := by
    simpa [prefixWord, tailWord_3413029, baseEnd_3413029] using wordTrace_append hprefix tailTrace_3413029
  have hstable : (prefixWord ++ tailWord_3413029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413029).length < 2 ^ (prefixWord ++ tailWord_3413029).sum := by decide
  have hdescent : baseEnd_3413029 < baseStart_3413029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413059 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 7]
def baseStart_3413059 : Nat := 118140960795 + 3413059 * 2 ^ 59
def prefixEnd_3413059 : Nat := 4983230072969 + 3 ^ 40 * 3413059 * 2
def baseEnd_3413059 : Nat := 1752539769153867124666133

theorem tailTrace_3413059 : CollatzResearch.WordTrace tailWord_3413059 prefixEnd_3413059 1752539769153867124666133 := by
  unfold tailWord_3413059
  simp only [CollatzResearch.WordTrace]
  refine ⟨124484488542077621914946231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82989659028051747943297487 124484488542077621914946231)
  ·
    refine ⟨186726732813116432872419347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124484488542077621914946231 186726732813116432872419347)
    ·
      refine ⟨280090099219674649308629021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186726732813116432872419347 280090099219674649308629021)
      ·
        refine ⟨105033787207377993490735883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280090099219674649308629021 105033787207377993490735883)
        ·
          refine ⟨157550680811066990236103825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105033787207377993490735883 157550680811066990236103825)
          ·
            refine ⟨118163010608300242677077869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157550680811066990236103825 118163010608300242677077869)
            ·
              refine ⟨44311128978112591003904201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118163010608300242677077869 44311128978112591003904201)
              ·
                refine ⟨33233346733584443252928151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44311128978112591003904201 33233346733584443252928151)
                ·
                  refine ⟨49850020100376664879392227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33233346733584443252928151 49850020100376664879392227)
                  ·
                    refine ⟨74775030150564997319088341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49850020100376664879392227 74775030150564997319088341)
                    ·
                      refine ⟨1752539769153867124666133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74775030150564997319088341 1752539769153867124666133)
                      ·
                        rfl

theorem cell23_3413059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_3413059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413059 prefixEnd_3413059 := by exact prefixLift 3413059
  have htrace : WordTrace (prefixWord ++ tailWord_3413059) baseStart_3413059 baseEnd_3413059 := by
    simpa [prefixWord, tailWord_3413059, baseEnd_3413059] using wordTrace_append hprefix tailTrace_3413059
  have hstable : (prefixWord ++ tailWord_3413059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413059).length < 2 ^ (prefixWord ++ tailWord_3413059).sum := by decide
  have hdescent : baseEnd_3413059 < baseStart_3413059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413066 : List Nat := [3, 1, 2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_3413066 : Nat := 118140960795 + 3413066 * 2 ^ 59
def prefixEnd_3413066 : Nat := 4983230072969 + 3 ^ 40 * 3413066 * 2
def baseEnd_3413066 : Nat := 584181121172816199092867

theorem tailTrace_3413066 : CollatzResearch.WordTrace tailWord_3413066 prefixEnd_3413066 584181121172816199092867 := by
  unfold tailWord_3413066
  simp only [CollatzResearch.WordTrace]
  refine ⟨31121185963263065527612763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82989829235368174740300701 31121185963263065527612763)
  ·
    refine ⟨46681778944894598291419145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31121185963263065527612763 46681778944894598291419145)
    ·
      refine ⟨35011334208670948718564359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46681778944894598291419145 35011334208670948718564359)
      ·
        refine ⟨52517001313006423077846539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35011334208670948718564359 52517001313006423077846539)
        ·
          refine ⟨78775501969509634616769809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52517001313006423077846539 78775501969509634616769809)
          ·
            refine ⟨59081626477132225962577357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78775501969509634616769809 59081626477132225962577357)
            ·
              refine ⟨22155609928924584735966509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59081626477132225962577357 22155609928924584735966509)
              ·
                refine ⟨8308353723346719275987441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22155609928924584735966509 8308353723346719275987441)
                ·
                  refine ⟨6231265292510039456990581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8308353723346719275987441 6231265292510039456990581)
                  ·
                    refine ⟨584181121172816199092867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6231265292510039456990581 584181121172816199092867)
                    ·
                      rfl

theorem cell23_3413066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_3413066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413066 prefixEnd_3413066 := by exact prefixLift 3413066
  have htrace : WordTrace (prefixWord ++ tailWord_3413066) baseStart_3413066 baseEnd_3413066 := by
    simpa [prefixWord, tailWord_3413066, baseEnd_3413066] using wordTrace_append hprefix tailTrace_3413066
  have hstable : (prefixWord ++ tailWord_3413066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413066).length < 2 ^ (prefixWord ++ tailWord_3413066).sum := by decide
  have hdescent : baseEnd_3413066 < baseStart_3413066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413076 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_3413076 : Nat := 118140960795 + 3413076 * 2 ^ 59
def prefixEnd_3413076 : Nat := 4983230072969 + 3 ^ 40 * 3413076 * 2
def baseEnd_3413076 : Nat := 1752548498324993558153555

theorem tailTrace_3413076 : CollatzResearch.WordTrace tailWord_3413076 prefixEnd_3413076 1752548498324993558153555 := by
  unfold tailWord_3413076
  simp only [CollatzResearch.WordTrace]
  refine ⟨62242554291508016909157541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82990072388677355878876721 62242554291508016909157541)
  ·
    refine ⟨11670478929657753170467039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62242554291508016909157541 11670478929657753170467039)
    ·
      refine ⟨17505718394486629755700559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11670478929657753170467039 17505718394486629755700559)
      ·
        refine ⟨26258577591729944633550839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17505718394486629755700559 26258577591729944633550839)
        ·
          refine ⟨39387866387594916950326259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26258577591729944633550839 39387866387594916950326259)
          ·
            refine ⟨59081799581392375425489389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39387866387594916950326259 59081799581392375425489389)
            ·
              refine ⟨22155674843022140784558521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59081799581392375425489389 22155674843022140784558521)
              ·
                refine ⟨16616756132266605588418891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22155674843022140784558521 16616756132266605588418891)
                ·
                  refine ⟨24925134198399908382628337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16616756132266605588418891 24925134198399908382628337)
                  ·
                    refine ⟨18693850648799931286971253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24925134198399908382628337 18693850648799931286971253)
                    ·
                      refine ⟨1752548498324993558153555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18693850648799931286971253 1752548498324993558153555)
                      ·
                        rfl

theorem cell23_3413076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_3413076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413076 prefixEnd_3413076 := by exact prefixLift 3413076
  have htrace : WordTrace (prefixWord ++ tailWord_3413076) baseStart_3413076 baseEnd_3413076 := by
    simpa [prefixWord, tailWord_3413076, baseEnd_3413076] using wordTrace_append hprefix tailTrace_3413076
  have hstable : (prefixWord ++ tailWord_3413076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413076).length < 2 ^ (prefixWord ++ tailWord_3413076).sum := by decide
  have hdescent : baseEnd_3413076 < baseStart_3413076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413090 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_3413090 : Nat := 118140960795 + 3413090 * 2 ^ 59
def prefixEnd_3413090 : Nat := 4983230072969 + 3 ^ 40 * 3413090 * 2
def baseEnd_3413090 : Nat := 1752555687054156503378491

theorem tailTrace_3413090 : CollatzResearch.WordTrace tailWord_3413090 prefixEnd_3413090 1752555687054156503378491 := by
  unfold tailWord_3413090
  simp only [CollatzResearch.WordTrace]
  refine ⟨31121404801241328552331181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82990412803310209472883149 31121404801241328552331181)
  ·
    refine ⟨11670526800465498207124193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31121404801241328552331181 11670526800465498207124193)
    ·
      refine ⟨8752895100349123655343145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11670526800465498207124193 8752895100349123655343145)
      ·
        refine ⟨6564671325261842741507359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8752895100349123655343145 6564671325261842741507359)
        ·
          refine ⟨9847006987892764112261039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6564671325261842741507359 9847006987892764112261039)
          ·
            refine ⟨14770510481839146168391559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9847006987892764112261039 14770510481839146168391559)
            ·
              refine ⟨22155765722758719252587339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14770510481839146168391559 22155765722758719252587339)
              ·
                refine ⟨33233648584138078878881009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22155765722758719252587339 33233648584138078878881009)
                ·
                  refine ⟨24925236438103559159160757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33233648584138078878881009 24925236438103559159160757)
                  ·
                    refine ⟨2336740916072208671171321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24925236438103559159160757 2336740916072208671171321)
                    ·
                      refine ⟨1752555687054156503378491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336740916072208671171321 1752555687054156503378491)
                      ·
                        rfl

theorem cell23_3413090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_3413090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413090 prefixEnd_3413090 := by exact prefixLift 3413090
  have htrace : WordTrace (prefixWord ++ tailWord_3413090) baseStart_3413090 baseEnd_3413090 := by
    simpa [prefixWord, tailWord_3413090, baseEnd_3413090] using wordTrace_append hprefix tailTrace_3413090
  have hstable : (prefixWord ++ tailWord_3413090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413090).length < 2 ^ (prefixWord ++ tailWord_3413090).sum := by decide
  have hdescent : baseEnd_3413090 < baseStart_3413090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413103 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 2, 4, 2]
def baseStart_3413103 : Nat := 118140960795 + 3413103 * 2 ^ 59
def prefixEnd_3413103 : Nat := 4983230072969 + 3 ^ 40 * 3413103 * 2
def baseEnd_3413103 : Nat := 1752562362302664952515931

theorem tailTrace_3413103 : CollatzResearch.WordTrace tailWord_3413103 prefixEnd_3413103 1752562362302664952515931 := by
  unfold tailWord_3413103
  simp only [CollatzResearch.WordTrace]
  refine ⟨124486093353918217429547963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82990728902612144953031975 124486093353918217429547963)
  ·
    refine ⟨186729140030877326144321945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124486093353918217429547963 186729140030877326144321945)
    ·
      refine ⟨140046855023157994608241459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186729140030877326144321945 140046855023157994608241459)
      ·
        refine ⟨210070282534736991912362189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140046855023157994608241459 210070282534736991912362189)
        ·
          refine ⟨78776355950526371967135821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210070282534736991912362189 78776355950526371967135821)
          ·
            refine ⟨29541133481447389487675933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78776355950526371967135821 29541133481447389487675933)
            ·
              refine ⟨11077925055542771057878475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29541133481447389487675933 11077925055542771057878475)
              ·
                refine ⟨16616887583314156586817713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11077925055542771057878475 16616887583314156586817713)
                ·
                  refine ⟨12462665687485617440113285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16616887583314156586817713 12462665687485617440113285)
                  ·
                    refine ⟨2336749816403553270021241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12462665687485617440113285 2336749816403553270021241)
                    ·
                      refine ⟨1752562362302664952515931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336749816403553270021241 1752562362302664952515931)
                      ·
                        rfl

theorem cell23_3413103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 4, 2].length) (baseStart_3413103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413103 prefixEnd_3413103 := by exact prefixLift 3413103
  have htrace : WordTrace (prefixWord ++ tailWord_3413103) baseStart_3413103 baseEnd_3413103 := by
    simpa [prefixWord, tailWord_3413103, baseEnd_3413103] using wordTrace_append hprefix tailTrace_3413103
  have hstable : (prefixWord ++ tailWord_3413103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413103).length < 2 ^ (prefixWord ++ tailWord_3413103).sum := by decide
  have hdescent : baseEnd_3413103 < baseStart_3413103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413143 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 6]
def baseStart_3413143 : Nat := 118140960795 + 3413143 * 2 ^ 59
def prefixEnd_3413143 : Nat := 4983230072969 + 3 ^ 40 * 3413143 * 2
def baseEnd_3413143 : Nat := 194731433503204977335083

theorem tailTrace_3413143 : CollatzResearch.WordTrace tailWord_3413143 prefixEnd_3413143 194731433503204977335083 := by
  unfold tailWord_3413143
  simp only [CollatzResearch.WordTrace]
  refine ⟨124487552273773304261004083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82991701515848869507336055 124487552273773304261004083)
  ·
    refine ⟨186731328410659956391506125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124487552273773304261004083 186731328410659956391506125)
    ·
      refine ⟨70024248153997483646814797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186731328410659956391506125 70024248153997483646814797)
      ·
        refine ⟨26259093057749056367555549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70024248153997483646814797 26259093057749056367555549)
        ·
          refine ⟨9847159896655896137833331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26259093057749056367555549 9847159896655896137833331)
          ·
            refine ⟨14770739844983844206749997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9847159896655896137833331 14770739844983844206749997)
            ·
              refine ⟨5539027441868941577531249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14770739844983844206749997 5539027441868941577531249)
              ·
                refine ⟨4154270581401706183148437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5539027441868941577531249 4154270581401706183148437)
                ·
                  refine ⟨194731433503204977335083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4154270581401706183148437 194731433503204977335083)
                  ·
                    rfl

theorem cell23_3413143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 6].length) (baseStart_3413143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413143 prefixEnd_3413143 := by exact prefixLift 3413143
  have htrace : WordTrace (prefixWord ++ tailWord_3413143) baseStart_3413143 baseEnd_3413143 := by
    simpa [prefixWord, tailWord_3413143, baseEnd_3413143] using wordTrace_append hprefix tailTrace_3413143
  have hstable : (prefixWord ++ tailWord_3413143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413143).length < 2 ^ (prefixWord ++ tailWord_3413143).sum := by decide
  have hdescent : baseEnd_3413143 < baseStart_3413143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413170 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_3413170 : Nat := 118140960795 + 3413170 * 2 ^ 59
def prefixEnd_3413170 : Nat := 4983230072969 + 3 ^ 40 * 3413170 * 2
def baseEnd_3413170 : Nat := 1752596765506516190378123

theorem tailTrace_3413170 : CollatzResearch.WordTrace tailWord_3413170 prefixEnd_3413170 1752596765506516190378123 := by
  unfold tailWord_3413170
  simp only [CollatzResearch.WordTrace]
  refine ⟨31122134261168871968059241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82992358029783658581491309 31122134261168871968059241)
  ·
    refine ⟨23341600695876653976044431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31122134261168871968059241 23341600695876653976044431)
    ·
      refine ⟨35012401043814980964066647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23341600695876653976044431 35012401043814980964066647)
      ·
        refine ⟨52518601565722471446099971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35012401043814980964066647 52518601565722471446099971)
        ·
          refine ⟨78777902348583707169149957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52518601565722471446099971 78777902348583707169149957)
          ·
            refine ⟨14770856690359445094215617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78777902348583707169149957 14770856690359445094215617)
            ·
              refine ⟨11078142517769583820661713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14770856690359445094215617 11078142517769583820661713)
              ·
                refine ⟨8308606888327187865496285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11078142517769583820661713 8308606888327187865496285)
                ·
                  refine ⟨3115727583122695449561107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8308606888327187865496285 3115727583122695449561107)
                  ·
                    refine ⟨4673591374684043174341661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3115727583122695449561107 4673591374684043174341661)
                    ·
                      refine ⟨1752596765506516190378123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4673591374684043174341661 1752596765506516190378123)
                      ·
                        rfl

theorem cell23_3413170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_3413170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413170 prefixEnd_3413170 := by exact prefixLift 3413170
  have htrace : WordTrace (prefixWord ++ tailWord_3413170) baseStart_3413170 baseEnd_3413170 := by
    simpa [prefixWord, tailWord_3413170, baseEnd_3413170] using wordTrace_append hprefix tailTrace_3413170
  have hstable : (prefixWord ++ tailWord_3413170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413170).length < 2 ^ (prefixWord ++ tailWord_3413170).sum := by decide
  have hdescent : baseEnd_3413170 < baseStart_3413170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413180 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 1, 5, 2]
def baseStart_3413180 : Nat := 118140960795 + 3413180 * 2 ^ 59
def prefixEnd_3413180 : Nat := 4983230072969 + 3 ^ 40 * 3413180 * 2
def baseEnd_3413180 : Nat := 1752601900313061151253077

theorem tailTrace_3413180 : CollatzResearch.WordTrace tailWord_3413180 prefixEnd_3413180 1752601900313061151253077 := by
  unfold tailWord_3413180
  simp only [CollatzResearch.WordTrace]
  refine ⟨62244450887319629790050497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82992601183092839720067329 62244450887319629790050497)
  ·
    refine ⟨46683338165489722342537873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62244450887319629790050497 46683338165489722342537873)
    ·
      refine ⟨35012503624117291756903405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46683338165489722342537873 35012503624117291756903405)
      ·
        refine ⟨13129688859043984408838777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35012503624117291756903405 13129688859043984408838777)
        ·
          refine ⟨9847266644282988306629083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13129688859043984408838777 9847266644282988306629083)
          ·
            refine ⟨14770899966424482459943625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9847266644282988306629083 14770899966424482459943625)
            ·
              refine ⟨11078174974818361844957719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14770899966424482459943625 11078174974818361844957719)
              ·
                refine ⟨16617262462227542767436579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11078174974818361844957719 16617262462227542767436579)
                ·
                  refine ⟨24925893693341314151154869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16617262462227542767436579 24925893693341314151154869)
                  ·
                    refine ⟨2336802533750748201670769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24925893693341314151154869 2336802533750748201670769)
                    ·
                      refine ⟨1752601900313061151253077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2336802533750748201670769 1752601900313061151253077)
                      ·
                        rfl

theorem cell23_3413180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_3413180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413180 prefixEnd_3413180 := by exact prefixLift 3413180
  have htrace : WordTrace (prefixWord ++ tailWord_3413180) baseStart_3413180 baseEnd_3413180 := by
    simpa [prefixWord, tailWord_3413180, baseEnd_3413180] using wordTrace_append hprefix tailTrace_3413180
  have hstable : (prefixWord ++ tailWord_3413180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413180).length < 2 ^ (prefixWord ++ tailWord_3413180).sum := by decide
  have hdescent : baseEnd_3413180 < baseStart_3413180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413216 : List Nat := [2, 1, 1, 3, 1, 4, 1, 10]
def baseStart_3413216 : Nat := 118140960795 + 3413216 * 2 ^ 59
def prefixEnd_3413216 : Nat := 4983230072969 + 3 ^ 40 * 3413216 * 2
def baseEnd_3413216 : Nat := 64911866133949000385293

theorem tailTrace_3413216 : CollatzResearch.WordTrace tailWord_3413216 prefixEnd_3413216 64911866133949000385293 := by
  unfold tailWord_3413216
  simp only [CollatzResearch.WordTrace]
  refine ⟨62245107401254418864205751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82993476535005891818941001 62245107401254418864205751)
  ·
    refine ⟨93367661101881628296308627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62245107401254418864205751 93367661101881628296308627)
    ·
      refine ⟨140051491652822442444462941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93367661101881628296308627 140051491652822442444462941)
      ·
        refine ⟨52519309369808415916673603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140051491652822442444462941 52519309369808415916673603)
        ·
          refine ⟨78778964054712623875010405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52519309369808415916673603 78778964054712623875010405)
          ·
            refine ⟨14771055760258616976564451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78778964054712623875010405 14771055760258616976564451)
            ·
              refine ⟨22156583640387925464846677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14771055760258616976564451 22156583640387925464846677)
              ·
                refine ⟨64911866133949000385293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22156583640387925464846677 64911866133949000385293)
                ·
                  rfl

theorem cell23_3413216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 10].length) (baseStart_3413216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413216 prefixEnd_3413216 := by exact prefixLift 3413216
  have htrace : WordTrace (prefixWord ++ tailWord_3413216) baseStart_3413216 baseEnd_3413216 := by
    simpa [prefixWord, tailWord_3413216, baseEnd_3413216] using wordTrace_append hprefix tailTrace_3413216
  have hstable : (prefixWord ++ tailWord_3413216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413216).length < 2 ^ (prefixWord ++ tailWord_3413216).sum := by decide
  have hdescent : baseEnd_3413216 < baseStart_3413216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413247 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 1, 2, 3]
def baseStart_3413247 : Nat := 118140960795 + 3413247 * 2 ^ 59
def prefixEnd_3413247 : Nat := 4983230072969 + 3 ^ 40 * 3413247 * 2
def baseEnd_3413247 : Nat := 1752636303516912389115269

theorem tailTrace_3413247 : CollatzResearch.WordTrace tailWord_3413247 prefixEnd_3413247 1752636303516912389115269 := by
  unfold tailWord_3413247
  simp only [CollatzResearch.WordTrace]
  refine ⟨124491345465396530022789995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82994230310264353348526663 124491345465396530022789995)
  ·
    refine ⟨186737018198094795034184993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124491345465396530022789995 186737018198094795034184993)
    ·
      refine ⟨140052763648571096275638745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186737018198094795034184993 140052763648571096275638745)
      ·
        refine ⟨105039572736428322206729059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140052763648571096275638745 105039572736428322206729059)
        ·
          refine ⟨157559359104642483310093589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105039572736428322206729059 157559359104642483310093589)
          ·
            refine ⟨7385594958030116405160637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157559359104642483310093589 7385594958030116405160637)
            ·
              refine ⟨2769598109261293651935239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7385594958030116405160637 2769598109261293651935239)
              ·
                refine ⟨4154397163891940477902859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769598109261293651935239 4154397163891940477902859)
                ·
                  refine ⟨6231595745837910716854289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154397163891940477902859 6231595745837910716854289)
                  ·
                    refine ⟨4673696809378433037640717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6231595745837910716854289 4673696809378433037640717)
                    ·
                      refine ⟨1752636303516912389115269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4673696809378433037640717 1752636303516912389115269)
                      ·
                        rfl

theorem cell23_3413247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 2, 3].length) (baseStart_3413247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413247 prefixEnd_3413247 := by exact prefixLift 3413247
  have htrace : WordTrace (prefixWord ++ tailWord_3413247) baseStart_3413247 baseEnd_3413247 := by
    simpa [prefixWord, tailWord_3413247, baseEnd_3413247] using wordTrace_append hprefix tailTrace_3413247
  have hstable : (prefixWord ++ tailWord_3413247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413247).length < 2 ^ (prefixWord ++ tailWord_3413247).sum := by decide
  have hdescent : baseEnd_3413247 < baseStart_3413247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413250 : List Nat := [3, 4, 1, 1, 4, 10]
def baseStart_3413250 : Nat := 118140960795 + 3413250 * 2 ^ 59
def prefixEnd_3413250 : Nat := 4983230072969 + 3 ^ 40 * 3413250 * 2
def baseEnd_3413250 : Nat := 7212501415468625009785

theorem tailTrace_3413250 : CollatzResearch.WordTrace tailWord_3413250 prefixEnd_3413250 7212501415468625009785 := by
  unfold tailWord_3413250
  simp only [CollatzResearch.WordTrace]
  refine ⟨31122863721096415383787301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82994303256257107690099469 31122863721096415383787301)
  ·
    refine ⟨5835536947705577884460119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31122863721096415383787301 5835536947705577884460119)
    ·
      refine ⟨8753305421558366826690179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5835536947705577884460119 8753305421558366826690179)
      ·
        refine ⟨13129958132337550240035269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8753305421558366826690179 13129958132337550240035269)
        ·
          refine ⟨2461867149813290670006613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13129958132337550240035269 2461867149813290670006613)
          ·
            refine ⟨7212501415468625009785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2461867149813290670006613 7212501415468625009785)
            ·
              rfl

theorem cell23_3413250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 10].length) (baseStart_3413250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413250 prefixEnd_3413250 := by exact prefixLift 3413250
  have htrace : WordTrace (prefixWord ++ tailWord_3413250) baseStart_3413250 baseEnd_3413250 := by
    simpa [prefixWord, tailWord_3413250, baseEnd_3413250] using wordTrace_append hprefix tailTrace_3413250
  have hstable : (prefixWord ++ tailWord_3413250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413250).length < 2 ^ (prefixWord ++ tailWord_3413250).sum := by decide
  have hdescent : baseEnd_3413250 < baseStart_3413250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413277 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3413277 : Nat := 118140960795 + 3413277 * 2 ^ 59
def prefixEnd_3413277 : Nat := 4983230072969 + 3 ^ 40 * 3413277 * 2
def baseEnd_3413277 : Nat := 1752651707936547271740131

theorem tailTrace_3413277 : CollatzResearch.WordTrace tailWord_3413277 prefixEnd_3413277 1752651707936547271740131 := by
  unfold tailWord_3413277
  simp only [CollatzResearch.WordTrace]
  refine ⟨124492439655287845146382085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82994959770191896764254723 124492439655287845146382085)
  ·
    refine ⟨23342332435366470964946641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124492439655287845146382085 23342332435366470964946641)
    ·
      refine ⟨17506749326524853223709981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23342332435366470964946641 17506749326524853223709981)
      ·
        refine ⟨6565030997446819958891243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17506749326524853223709981 6565030997446819958891243)
        ·
          refine ⟨9847546496170229938336865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6565030997446819958891243 9847546496170229938336865)
          ·
            refine ⟨7385659872127672453752649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9847546496170229938336865 7385659872127672453752649)
            ·
              refine ⟨5539244904095754340314487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7385659872127672453752649 5539244904095754340314487)
              ·
                refine ⟨8308867356143631510471731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539244904095754340314487 8308867356143631510471731)
                ·
                  refine ⟨12463301034215447265707597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8308867356143631510471731 12463301034215447265707597)
                  ·
                    refine ⟨4673737887830792724640349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12463301034215447265707597 4673737887830792724640349)
                    ·
                      refine ⟨1752651707936547271740131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4673737887830792724640349 1752651707936547271740131)
                      ·
                        rfl

theorem cell23_3413277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3413277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413277 prefixEnd_3413277 := by exact prefixLift 3413277
  have htrace : WordTrace (prefixWord ++ tailWord_3413277) baseStart_3413277 baseEnd_3413277 := by
    simpa [prefixWord, tailWord_3413277, baseEnd_3413277] using wordTrace_append hprefix tailTrace_3413277
  have hstable : (prefixWord ++ tailWord_3413277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413277).length < 2 ^ (prefixWord ++ tailWord_3413277).sum := by decide
  have hdescent : baseEnd_3413277 < baseStart_3413277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413357 : List Nat := [1, 5, 1, 1, 1, 3, 3, 3, 5]
def baseStart_3413357 : Nat := 118140960795 + 3413357 * 2 ^ 59
def prefixEnd_3413357 : Nat := 4983230072969 + 3 ^ 40 * 3413357 * 2
def baseEnd_3413357 : Nat := 194743642932100773193307

theorem tailTrace_3413357 : CollatzResearch.WordTrace tailWord_3413357 prefixEnd_3413357 194743642932100773193307 := by
  unfold tailWord_3413357
  simp only [CollatzResearch.WordTrace]
  refine ⟨124495357494998018809294325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82996904996665345872862883 124495357494998018809294325)
  ·
    refine ⟨11671439765156064263371343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124495357494998018809294325 11671439765156064263371343)
    ·
      refine ⟨17507159647734096395057015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11671439765156064263371343 17507159647734096395057015)
      ·
        refine ⟨26260739471601144592585523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17507159647734096395057015 26260739471601144592585523)
        ·
          refine ⟨39391109207401716888878285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26260739471601144592585523 39391109207401716888878285)
          ·
            refine ⟨14771665952775643833329357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39391109207401716888878285 14771665952775643833329357)
            ·
              refine ⟨5539374732290866437498509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14771665952775643833329357 5539374732290866437498509)
              ·
                refine ⟨2077265524609074914061941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5539374732290866437498509 2077265524609074914061941)
                ·
                  refine ⟨194743642932100773193307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2077265524609074914061941 194743642932100773193307)
                  ·
                    rfl

theorem cell23_3413357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_3413357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413357 prefixEnd_3413357 := by exact prefixLift 3413357
  have htrace : WordTrace (prefixWord ++ tailWord_3413357) baseStart_3413357 baseEnd_3413357 := by
    simpa [prefixWord, tailWord_3413357, baseEnd_3413357] using wordTrace_append hprefix tailTrace_3413357
  have hstable : (prefixWord ++ tailWord_3413357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413357).length < 2 ^ (prefixWord ++ tailWord_3413357).sum := by decide
  have hdescent : baseEnd_3413357 < baseStart_3413357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413380 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_3413380 : Nat := 118140960795 + 3413380 * 2 ^ 59
def prefixEnd_3413380 : Nat := 4983230072969 + 3 ^ 40 * 3413380 * 2
def baseEnd_3413380 : Nat := 1752704596443960368752157

theorem tailTrace_3413380 : CollatzResearch.WordTrace tailWord_3413380 prefixEnd_3413380 1752704596443960368752157 := by
  unfold tailWord_3413380
  simp only [CollatzResearch.WordTrace]
  refine ⟨62248098186957346868690797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82997464249276462491587729 62248098186957346868690797)
  ·
    refine ⟨23343036820109005075759049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62248098186957346868690797 23343036820109005075759049)
    ·
      refine ⟨17507277615081753806819287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23343036820109005075759049 17507277615081753806819287)
      ·
        refine ⟨26260916422622630710228931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17507277615081753806819287 26260916422622630710228931)
        ·
          refine ⟨39391374633933946065343397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26260916422622630710228931 39391374633933946065343397)
          ·
            refine ⟨7385882743862614887251887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39391374633933946065343397 7385882743862614887251887)
            ·
              refine ⟨11078824115793922330877831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7385882743862614887251887 11078824115793922330877831)
              ·
                refine ⟨16618236173690883496316747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11078824115793922330877831 16618236173690883496316747)
                ·
                  refine ⟨24927354260536325244475121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16618236173690883496316747 24927354260536325244475121)
                  ·
                    refine ⟨18695515695402243933356341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24927354260536325244475121 18695515695402243933356341)
                    ·
                      refine ⟨1752704596443960368752157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18695515695402243933356341 1752704596443960368752157)
                      ·
                        rfl

theorem cell23_3413380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_3413380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413380 prefixEnd_3413380 := by exact prefixLift 3413380
  have htrace : WordTrace (prefixWord ++ tailWord_3413380) baseStart_3413380 baseEnd_3413380 := by
    simpa [prefixWord, tailWord_3413380, baseEnd_3413380] using wordTrace_append hprefix tailTrace_3413380
  have hstable : (prefixWord ++ tailWord_3413380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413380).length < 2 ^ (prefixWord ++ tailWord_3413380).sum := by decide
  have hdescent : baseEnd_3413380 < baseStart_3413380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413404 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 2, 5]
def baseStart_3413404 : Nat := 118140960795 + 3413404 * 2 ^ 59
def prefixEnd_3413404 : Nat := 4983230072969 + 3 ^ 40 * 3413404 * 2
def baseEnd_3413404 : Nat := 584238973326556091617349

theorem tailTrace_3413404 : CollatzResearch.WordTrace tailWord_3413404 prefixEnd_3413404 584238973326556091617349 := by
  unfold tailWord_3413404
  simp only [CollatzResearch.WordTrace]
  refine ⟨62248535862913872918127633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82998047817218497224170177 62248535862913872918127633)
  ·
    refine ⟨46686401897185404688595725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62248535862913872918127633 46686401897185404688595725)
    ·
      refine ⟨17507400711444526758223397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46686401897185404688595725 17507400711444526758223397)
      ·
        refine ⟨3282637633395848767166887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17507400711444526758223397 3282637633395848767166887)
        ·
          refine ⟨4923956450093773150750331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3282637633395848767166887 4923956450093773150750331)
          ·
            refine ⟨7385934675140659726125497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4923956450093773150750331 7385934675140659726125497)
            ·
              refine ⟨5539451006355494794594123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7385934675140659726125497 5539451006355494794594123)
              ·
                refine ⟨8309176509533242191891185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539451006355494794594123 8309176509533242191891185)
                ·
                  refine ⟨6231882382149931643918389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8309176509533242191891185 6231882382149931643918389)
                  ·
                    refine ⟨584238973326556091617349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6231882382149931643918389 584238973326556091617349)
                    ·
                      rfl

theorem cell23_3413404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_3413404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413404 prefixEnd_3413404 := by exact prefixLift 3413404
  have htrace : WordTrace (prefixWord ++ tailWord_3413404) baseStart_3413404 baseEnd_3413404 := by
    simpa [prefixWord, tailWord_3413404, baseEnd_3413404] using wordTrace_append hprefix tailTrace_3413404
  have hstable : (prefixWord ++ tailWord_3413404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413404).length < 2 ^ (prefixWord ++ tailWord_3413404).sum := by decide
  have hdescent : baseEnd_3413404 < baseStart_3413404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413407 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3413407 : Nat := 118140960795 + 3413407 * 2 ^ 59
def prefixEnd_3413407 : Nat := 4983230072969 + 3 ^ 40 * 3413407 * 2
def baseEnd_3413407 : Nat := 1752718460421631763114533

theorem tailTrace_3413407 : CollatzResearch.WordTrace tailWord_3413407 prefixEnd_3413407 1752718460421631763114533 := by
  unfold tailWord_3413407
  simp only [CollatzResearch.WordTrace]
  refine ⟨124497181144816877348614475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82998120763211251565742983 124497181144816877348614475)
  ·
    refine ⟨186745771717225316022921713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124497181144816877348614475 186745771717225316022921713)
    ·
      refine ⟨140059328787918987017191285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186745771717225316022921713 140059328787918987017191285)
      ·
        refine ⟨13130562073867405032861683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140059328787918987017191285 13130562073867405032861683)
        ·
          refine ⟨19695843110801107549292525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13130562073867405032861683 19695843110801107549292525)
          ·
            refine ⟨7385941166550415330984697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19695843110801107549292525 7385941166550415330984697)
            ·
              refine ⟨5539455874912811498238523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7385941166550415330984697 5539455874912811498238523)
              ·
                refine ⟨8309183812369217247357785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539455874912811498238523 8309183812369217247357785)
                ·
                  refine ⟨6231887859276912935518339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8309183812369217247357785 6231887859276912935518339)
                  ·
                    refine ⟨9347831788915369403277509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6231887859276912935518339 9347831788915369403277509)
                    ·
                      refine ⟨1752718460421631763114533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9347831788915369403277509 1752718460421631763114533)
                      ·
                        rfl

theorem cell23_3413407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3413407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413407 prefixEnd_3413407 := by exact prefixLift 3413407
  have htrace : WordTrace (prefixWord ++ tailWord_3413407) baseStart_3413407 baseEnd_3413407 := by
    simpa [prefixWord, tailWord_3413407, baseEnd_3413407] using wordTrace_append hprefix tailTrace_3413407
  have hstable : (prefixWord ++ tailWord_3413407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413407).length < 2 ^ (prefixWord ++ tailWord_3413407).sum := by decide
  have hdescent : baseEnd_3413407 < baseStart_3413407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413413 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 8]
def baseStart_3413413 : Nat := 118140960795 + 3413413 * 2 ^ 59
def prefixEnd_3413413 : Nat := 4983230072969 + 3 ^ 40 * 3413413 * 2
def baseEnd_3413413 : Nat := 194746837922839859959945

theorem tailTrace_3413413 : CollatzResearch.WordTrace tailWord_3413413 prefixEnd_3413413 194746837922839859959945 := by
  unfold tailWord_3413413
  simp only [CollatzResearch.WordTrace]
  refine ⟨124497399982795140373332893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82998266655196760248888595 124497399982795140373332893)
  ·
    refine ⟨46686524993548177639999835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124497399982795140373332893 46686524993548177639999835)
    ·
      refine ⟨70029787490322266459999753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46686524993548177639999835 70029787490322266459999753)
      ·
        refine ⟨52522340617741699844999815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70029787490322266459999753 52522340617741699844999815)
        ·
          refine ⟨78783510926612549767499723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52522340617741699844999815 78783510926612549767499723)
          ·
            refine ⟨118175266389918824651249585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78783510926612549767499723 118175266389918824651249585)
            ·
              refine ⟨88631449792439118488437189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118175266389918824651249585 88631449792439118488437189)
              ·
                refine ⟨16618396836082334716581973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88631449792439118488437189 16618396836082334716581973)
                ·
                  refine ⟨194746837922839859959945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16618396836082334716581973 194746837922839859959945)
                  ·
                    rfl

theorem cell23_3413413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_3413413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413413 prefixEnd_3413413 := by exact prefixLift 3413413
  have htrace : WordTrace (prefixWord ++ tailWord_3413413) baseStart_3413413 baseEnd_3413413 := by
    simpa [prefixWord, tailWord_3413413, baseEnd_3413413] using wordTrace_append hprefix tailTrace_3413413
  have hstable : (prefixWord ++ tailWord_3413413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413413).length < 2 ^ (prefixWord ++ tailWord_3413413).sum := by decide
  have hdescent : baseEnd_3413413 < baseStart_3413413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413500 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3413500 : Nat := 118140960795 + 3413500 * 2 ^ 59
def prefixEnd_3413500 : Nat := 4983230072969 + 3 ^ 40 * 3413500 * 2
def baseEnd_3413500 : Nat := 1752766214122499899251605

theorem tailTrace_3413500 : CollatzResearch.WordTrace tailWord_3413500 prefixEnd_3413500 1752766214122499899251605 := by
  unfold tailWord_3413500
  simp only [CollatzResearch.WordTrace]
  refine ⟨62250286566739977115874977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83000382088986636154499969 62250286566739977115874977)
  ·
    refine ⟨46687714925054982836906233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62250286566739977115874977 46687714925054982836906233)
    ·
      refine ⟨35015786193791237127679675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46687714925054982836906233 35015786193791237127679675)
      ·
        refine ⟨52523679290686855691519513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35015786193791237127679675 52523679290686855691519513)
        ·
          refine ⟨39392759468015141768639635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52523679290686855691519513 39392759468015141768639635)
          ·
            refine ⟨59089139202022712652959453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39392759468015141768639635 59089139202022712652959453)
            ·
              refine ⟨22158427200758517244859795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59089139202022712652959453 22158427200758517244859795)
              ·
                refine ⟨33237640801137775867289693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22158427200758517244859795 33237640801137775867289693)
                ·
                  refine ⟨12464115300426665950233635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33237640801137775867289693 12464115300426665950233635)
                  ·
                    refine ⟨18696172950639998925350453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12464115300426665950233635 18696172950639998925350453)
                    ·
                      refine ⟨1752766214122499899251605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18696172950639998925350453 1752766214122499899251605)
                      ·
                        rfl

theorem cell23_3413500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3413500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413500 prefixEnd_3413500 := by exact prefixLift 3413500
  have htrace : WordTrace (prefixWord ++ tailWord_3413500) baseStart_3413500 baseEnd_3413500 := by
    simpa [prefixWord, tailWord_3413500, baseEnd_3413500] using wordTrace_append hprefix tailTrace_3413500
  have hstable : (prefixWord ++ tailWord_3413500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413500).length < 2 ^ (prefixWord ++ tailWord_3413500).sum := by decide
  have hdescent : baseEnd_3413500 < baseStart_3413500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413514 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_3413514 : Nat := 118140960795 + 3413514 * 2 ^ 59
def prefixEnd_3413514 : Nat := 4983230072969 + 3 ^ 40 * 3413514 * 2
def baseEnd_3413514 : Nat := 1752773402851662844476541

theorem tailTrace_3413514 : CollatzResearch.WordTrace tailWord_3413514 prefixEnd_3413514 1752773402851662844476541 := by
  unfold tailWord_3413514
  simp only [CollatzResearch.WordTrace]
  refine ⟨31125270938857308655689899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83000722503619489748506397 31125270938857308655689899)
  ·
    refine ⟨46687906408285962983534849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31125270938857308655689899 46687906408285962983534849)
    ·
      refine ⟨35015929806214472237651137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46687906408285962983534849 35015929806214472237651137)
      ·
        refine ⟨26261947354660854178238353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35015929806214472237651137 26261947354660854178238353)
        ·
          refine ⟨19696460515995640633678765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26261947354660854178238353 19696460515995640633678765)
          ·
            refine ⟨7386172693498365237629537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19696460515995640633678765 7386172693498365237629537)
            ·
              refine ⟨5539629520123773928222153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7386172693498365237629537 5539629520123773928222153)
              ·
                refine ⟨4154722140092830446166615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5539629520123773928222153 4154722140092830446166615)
                ·
                  refine ⟨6232083210139245669249923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154722140092830446166615 6232083210139245669249923)
                  ·
                    refine ⟨9348124815208868503874885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6232083210139245669249923 9348124815208868503874885)
                    ·
                      refine ⟨1752773402851662844476541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9348124815208868503874885 1752773402851662844476541)
                      ·
                        rfl

theorem cell23_3413514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_3413514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413514 prefixEnd_3413514 := by exact prefixLift 3413514
  have htrace : WordTrace (prefixWord ++ tailWord_3413514) baseStart_3413514 baseEnd_3413514 := by
    simpa [prefixWord, tailWord_3413514, baseEnd_3413514] using wordTrace_append hprefix tailTrace_3413514
  have hstable : (prefixWord ++ tailWord_3413514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413514).length < 2 ^ (prefixWord ++ tailWord_3413514).sum := by decide
  have hdescent : baseEnd_3413514 < baseStart_3413514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413581 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3413581 : Nat := 118140960795 + 3413581 * 2 ^ 59
def prefixEnd_3413581 : Nat := 4983230072969 + 3 ^ 40 * 3413581 * 2
def baseEnd_3413581 : Nat := 1752807806055514082338733

theorem tailTrace_3413581 : CollatzResearch.WordTrace tailWord_3413581 prefixEnd_3413581 1752807806055514082338733 := by
  unfold tailWord_3413581
  simp only [CollatzResearch.WordTrace]
  refine ⟨124503527446186505065448597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83002351630791003376965731 124503527446186505065448597)
  ·
    refine ⟨5836102849039992424942903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124503527446186505065448597 5836102849039992424942903)
    ·
      refine ⟨8754154273559988637414355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5836102849039992424942903 8754154273559988637414355)
      ·
        refine ⟨13131231410339982956121533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8754154273559988637414355 13131231410339982956121533)
        ·
          refine ⟨4924211778877493608545575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13131231410339982956121533 4924211778877493608545575)
          ·
            refine ⟨7386317668316240412818363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924211778877493608545575 7386317668316240412818363)
            ·
              refine ⟨11079476502474360619227545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7386317668316240412818363 11079476502474360619227545)
              ·
                refine ⟨8309607376855770464420659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11079476502474360619227545 8309607376855770464420659)
                ·
                  refine ⟨12464411065283655696630989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8309607376855770464420659 12464411065283655696630989)
                  ·
                    refine ⟨4674154149481370886236621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12464411065283655696630989 4674154149481370886236621)
                    ·
                      refine ⟨1752807806055514082338733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4674154149481370886236621 1752807806055514082338733)
                      ·
                        rfl

theorem cell23_3413581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3413581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413581 prefixEnd_3413581 := by exact prefixLift 3413581
  have htrace : WordTrace (prefixWord ++ tailWord_3413581) baseStart_3413581 baseEnd_3413581 := by
    simpa [prefixWord, tailWord_3413581, baseEnd_3413581] using wordTrace_append hprefix tailTrace_3413581
  have hstable : (prefixWord ++ tailWord_3413581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413581).length < 2 ^ (prefixWord ++ tailWord_3413581).sum := by decide
  have hdescent : baseEnd_3413581 < baseStart_3413581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413600 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_3413600 : Nat := 118140960795 + 3413600 * 2 ^ 59
def prefixEnd_3413600 : Nat := 4983230072969 + 3 ^ 40 * 3413600 * 2
def baseEnd_3413600 : Nat := 1752817562187949508001145

theorem tailTrace_3413600 : CollatzResearch.WordTrace tailWord_3413600 prefixEnd_3413600 1752817562187949508001145 := by
  unfold tailWord_3413600
  simp only [CollatzResearch.WordTrace]
  refine ⟨62252110216558835655195127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83002813622078447540260169 62252110216558835655195127)
  ·
    refine ⟨93378165324838253482792691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62252110216558835655195127 93378165324838253482792691)
    ·
      refine ⟨140067247987257380224189037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93378165324838253482792691 140067247987257380224189037)
      ·
        refine ⟨52525217995221517584070889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140067247987257380224189037 52525217995221517584070889)
        ·
          refine ⟨39393913496416138188053167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52525217995221517584070889 39393913496416138188053167)
          ·
            refine ⟨59090870244624207282079751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39393913496416138188053167 59090870244624207282079751)
            ·
              refine ⟨88636305366936310923119627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59090870244624207282079751 88636305366936310923119627)
              ·
                refine ⟨132954458050404466384679441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88636305366936310923119627 132954458050404466384679441)
                ·
                  refine ⟨99715843537803349788509581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132954458050404466384679441 99715843537803349788509581)
                  ·
                    refine ⟨37393441326676256170691093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99715843537803349788509581 37393441326676256170691093)
                    ·
                      refine ⟨1752817562187949508001145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37393441326676256170691093 1752817562187949508001145)
                      ·
                        rfl

theorem cell23_3413600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_3413600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413600 prefixEnd_3413600 := by exact prefixLift 3413600
  have htrace : WordTrace (prefixWord ++ tailWord_3413600) baseStart_3413600 baseEnd_3413600 := by
    simpa [prefixWord, tailWord_3413600, baseEnd_3413600] using wordTrace_append hprefix tailTrace_3413600
  have hstable : (prefixWord ++ tailWord_3413600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413600).length < 2 ^ (prefixWord ++ tailWord_3413600).sum := by decide
  have hdescent : baseEnd_3413600 < baseStart_3413600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413607 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_3413607 : Nat := 118140960795 + 3413607 * 2 ^ 59
def prefixEnd_3413607 : Nat := 4983230072969 + 3 ^ 40 * 3413607 * 2
def baseEnd_3413607 : Nat := 1752821156552530980613613

theorem tailTrace_3413607 : CollatzResearch.WordTrace tailWord_3413607 prefixEnd_3413607 1752821156552530980613613 := by
  unfold tailWord_3413607
  simp only [CollatzResearch.WordTrace]
  refine ⟨124504475744092311505895075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83002983829394874337263383 124504475744092311505895075)
  ·
    refine ⟨186756713616138467258842613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124504475744092311505895075 186756713616138467258842613)
    ·
      refine ⟨17508441901512981305516495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186756713616138467258842613 17508441901512981305516495)
      ·
        refine ⟨26262662852269471958274743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17508441901512981305516495 26262662852269471958274743)
        ·
          refine ⟨39393994278404207937412115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26262662852269471958274743 39393994278404207937412115)
          ·
            refine ⟨59090991417606311906118173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39393994278404207937412115 59090991417606311906118173)
            ·
              refine ⟨22159121781602366964794315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59090991417606311906118173 22159121781602366964794315)
              ·
                refine ⟨33238682672403550447191473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22159121781602366964794315 33238682672403550447191473)
                ·
                  refine ⟨24929012004302662835393605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33238682672403550447191473 24929012004302662835393605)
                  ·
                    refine ⟨4674189750806749281636301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24929012004302662835393605 4674189750806749281636301)
                    ·
                      refine ⟨1752821156552530980613613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4674189750806749281636301 1752821156552530980613613)
                      ·
                        rfl

theorem cell23_3413607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_3413607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413607 prefixEnd_3413607 := by exact prefixLift 3413607
  have htrace : WordTrace (prefixWord ++ tailWord_3413607) baseStart_3413607 baseEnd_3413607 := by
    simpa [prefixWord, tailWord_3413607, baseEnd_3413607] using wordTrace_append hprefix tailTrace_3413607
  have hstable : (prefixWord ++ tailWord_3413607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413607).length < 2 ^ (prefixWord ++ tailWord_3413607).sum := by decide
  have hdescent : baseEnd_3413607 < baseStart_3413607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413614 : List Nat := [4, 1, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_3413614 : Nat := 118140960795 + 3413614 * 2 ^ 59
def prefixEnd_3413614 : Nat := 4983230072969 + 3 ^ 40 * 3413614 * 2
def baseEnd_3413614 : Nat := 584274916972370817742027

theorem tailTrace_3413614 : CollatzResearch.WordTrace tailWord_3413614 prefixEnd_3413614 584274916972370817742027 := by
  unfold tailWord_3413614
  simp only [CollatzResearch.WordTrace]
  refine ⟨15563091381883368962674987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83003154036711301134266597 15563091381883368962674987)
  ·
    refine ⟨23344637072825053444012481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15563091381883368962674987 23344637072825053444012481)
    ·
      refine ⟨17508477804618790083009361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23344637072825053444012481 17508477804618790083009361)
      ·
        refine ⟨13131358353464092562257021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17508477804618790083009361 13131358353464092562257021)
        ·
          refine ⟨4924259382549034710846383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13131358353464092562257021 4924259382549034710846383)
          ·
            refine ⟨7386389073823552066269575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924259382549034710846383 7386389073823552066269575)
            ·
              refine ⟨11079583610735328099404363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7386389073823552066269575 11079583610735328099404363)
              ·
                refine ⟨16619375416102992149106545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11079583610735328099404363 16619375416102992149106545)
                ·
                  refine ⟨12464531562077244111829909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16619375416102992149106545 12464531562077244111829909)
                  ·
                    refine ⟨584274916972370817742027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12464531562077244111829909 584274916972370817742027)
                    ·
                      rfl

theorem cell23_3413614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_3413614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413614 prefixEnd_3413614 := by exact prefixLift 3413614
  have htrace : WordTrace (prefixWord ++ tailWord_3413614) baseStart_3413614 baseEnd_3413614 := by
    simpa [prefixWord, tailWord_3413614, baseEnd_3413614] using wordTrace_append hprefix tailTrace_3413614
  have hstable : (prefixWord ++ tailWord_3413614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413614).length < 2 ^ (prefixWord ++ tailWord_3413614).sum := by decide
  have hdescent : baseEnd_3413614 < baseStart_3413614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413621 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_3413621 : Nat := 118140960795 + 3413621 * 2 ^ 59
def prefixEnd_3413621 : Nat := 4983230072969 + 3 ^ 40 * 3413621 * 2
def baseEnd_3413621 : Nat := 1752828345281693925838549

theorem tailTrace_3413621 : CollatzResearch.WordTrace tailWord_3413621 prefixEnd_3413621 1752828345281693925838549 := by
  unfold tailWord_3413621
  simp only [CollatzResearch.WordTrace]
  refine ⟨124504986366041591896904717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83003324244027727931269811 124504986366041591896904717)
  ·
    refine ⟨46689369887265596961339269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124504986366041591896904717 46689369887265596961339269)
    ·
      refine ⟨8754256853862299430251113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46689369887265596961339269 8754256853862299430251113)
      ·
        refine ⟨6565692640396724572688335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8754256853862299430251113 6565692640396724572688335)
        ·
          refine ⟨9848538960595086859032503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6565692640396724572688335 9848538960595086859032503)
          ·
            refine ⟨14772808440892630288548755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9848538960595086859032503 14772808440892630288548755)
            ·
              refine ⟨22159212661338945432823133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14772808440892630288548755 22159212661338945432823133)
              ·
                refine ⟨8309704748002104537308675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22159212661338945432823133 8309704748002104537308675)
                ·
                  refine ⟨12464557122003156805963013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8309704748002104537308675 12464557122003156805963013)
                  ·
                    refine ⟨2337104460375591901118065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12464557122003156805963013 2337104460375591901118065)
                    ·
                      refine ⟨1752828345281693925838549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2337104460375591901118065 1752828345281693925838549)
                      ·
                        rfl

theorem cell23_3413621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_3413621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413621 prefixEnd_3413621 := by exact prefixLift 3413621
  have htrace : WordTrace (prefixWord ++ tailWord_3413621) baseStart_3413621 baseEnd_3413621 := by
    simpa [prefixWord, tailWord_3413621, baseEnd_3413621] using wordTrace_append hprefix tailTrace_3413621
  have hstable : (prefixWord ++ tailWord_3413621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413621).length < 2 ^ (prefixWord ++ tailWord_3413621).sum := by decide
  have hdescent : baseEnd_3413621 < baseStart_3413621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413637 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 1, 5, 3]
def baseStart_3413637 : Nat := 118140960795 + 3413637 * 2 ^ 59
def prefixEnd_3413637 : Nat := 4983230072969 + 3 ^ 40 * 3413637 * 2
def baseEnd_3413637 : Nat := 1752836560972165863238475

theorem tailTrace_3413637 : CollatzResearch.WordTrace tailWord_3413637 prefixEnd_3413637 1752836560972165863238475 := by
  unfold tailWord_3413637
  simp only [CollatzResearch.WordTrace]
  refine ⟨124505569933983626629487165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83003713289322417752991443 124505569933983626629487165)
  ·
    refine ⟨46689588725243859986057687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124505569933983626629487165 46689588725243859986057687)
    ·
      refine ⟨70034383087865789979086531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46689588725243859986057687 70034383087865789979086531)
      ·
        refine ⟨105051574631798684968629797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70034383087865789979086531 105051574631798684968629797)
        ·
          refine ⟨19697170243462253431618087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105051574631798684968629797 19697170243462253431618087)
          ·
            refine ⟨29545755365193380147427131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19697170243462253431618087 29545755365193380147427131)
            ·
              refine ⟨44318633047790070221140697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29545755365193380147427131 44318633047790070221140697)
              ·
                refine ⟨33238974785842552665855523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44318633047790070221140697 33238974785842552665855523)
                ·
                  refine ⟨49858462178763828998783285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33238974785842552665855523 49858462178763828998783285)
                  ·
                    refine ⟨4674230829259108968635933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49858462178763828998783285 4674230829259108968635933)
                    ·
                      refine ⟨1752836560972165863238475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4674230829259108968635933 1752836560972165863238475)
                      ·
                        rfl

theorem cell23_3413637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_3413637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413637 prefixEnd_3413637 := by exact prefixLift 3413637
  have htrace : WordTrace (prefixWord ++ tailWord_3413637) baseStart_3413637 baseEnd_3413637 := by
    simpa [prefixWord, tailWord_3413637, baseEnd_3413637] using wordTrace_append hprefix tailTrace_3413637
  have hstable : (prefixWord ++ tailWord_3413637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413637).length < 2 ^ (prefixWord ++ tailWord_3413637).sum := by decide
  have hdescent : baseEnd_3413637 < baseStart_3413637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413644 : List Nat := [2, 2, 1, 2, 1, 1, 6, 3, 5]
def baseStart_3413644 : Nat := 118140960795 + 3413644 * 2 ^ 59
def prefixEnd_3413644 : Nat := 4983230072969 + 3 ^ 40 * 3413644 * 2
def baseEnd_3413644 : Nat := 194760017259638592872327

theorem tailTrace_3413644 : CollatzResearch.WordTrace tailWord_3413644 prefixEnd_3413644 194760017259638592872327 := by
  unfold tailWord_3413644
  simp only [CollatzResearch.WordTrace]
  refine ⟨62252912622479133412495993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83003883496638844549994657 62252912622479133412495993)
  ·
    refine ⟨46689684466859350059371995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62252912622479133412495993 46689684466859350059371995)
    ·
      refine ⟨70034526700289025089057993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46689684466859350059371995 70034526700289025089057993)
      ·
        refine ⟨52525895025216768816793495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70034526700289025089057993 52525895025216768816793495)
        ·
          refine ⟨78788842537825153225190243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52525895025216768816793495 78788842537825153225190243)
          ·
            refine ⟨118183263806737729837785365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78788842537825153225190243 118183263806737729837785365)
            ·
              refine ⟨5539840490940831086146189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118183263806737729837785365 5539840490940831086146189)
              ·
                refine ⟨2077440184102811657304821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5539840490940831086146189 2077440184102811657304821)
                ·
                  refine ⟨194760017259638592872327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2077440184102811657304821 194760017259638592872327)
                  ·
                    rfl

theorem cell23_3413644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_3413644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413644 prefixEnd_3413644 := by exact prefixLift 3413644
  have htrace : WordTrace (prefixWord ++ tailWord_3413644) baseStart_3413644 baseEnd_3413644 := by
    simpa [prefixWord, tailWord_3413644, baseEnd_3413644] using wordTrace_append hprefix tailTrace_3413644
  have hstable : (prefixWord ++ tailWord_3413644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413644).length < 2 ^ (prefixWord ++ tailWord_3413644).sum := by decide
  have hdescent : baseEnd_3413644 < baseStart_3413644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413672 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3413672 : Nat := 118140960795 + 3413672 * 2 ^ 59
def prefixEnd_3413672 : Nat := 4983230072969 + 3 ^ 40 * 3413672 * 2
def baseEnd_3413672 : Nat := 1752854532795073226300815

theorem tailTrace_3413672 : CollatzResearch.WordTrace tailWord_3413672 prefixEnd_3413672 1752854532795073226300815 := by
  unfold tailWord_3413672
  simp only [CollatzResearch.WordTrace]
  refine ⟨62253423244428413803505635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83004564325904551738007513 62253423244428413803505635)
  ·
    refine ⟨93380134866642620705258453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62253423244428413803505635 93380134866642620705258453)
    ·
      refine ⟨2188596910936936422779495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 93380134866642620705258453 2188596910936936422779495)
      ·
        refine ⟨3282895366405404634169243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188596910936936422779495 3282895366405404634169243)
        ·
          refine ⟨4924343049608106951253865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3282895366405404634169243 4924343049608106951253865)
          ·
            refine ⟨3693257287206080213440399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4924343049608106951253865 3693257287206080213440399)
            ·
              refine ⟨5539885930809120320160599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693257287206080213440399 5539885930809120320160599)
              ·
                refine ⟨8309828896213680480240899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539885930809120320160599 8309828896213680480240899)
                ·
                  refine ⟨12464743344320520720361349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8309828896213680480240899 12464743344320520720361349)
                  ·
                    refine ⟨2337139377060097635067753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12464743344320520720361349 2337139377060097635067753)
                    ·
                      refine ⟨1752854532795073226300815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2337139377060097635067753 1752854532795073226300815)
                      ·
                        rfl

theorem cell23_3413672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3413672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413672 prefixEnd_3413672 := by exact prefixLift 3413672
  have htrace : WordTrace (prefixWord ++ tailWord_3413672) baseStart_3413672 baseEnd_3413672 := by
    simpa [prefixWord, tailWord_3413672, baseEnd_3413672] using wordTrace_append hprefix tailTrace_3413672
  have hstable : (prefixWord ++ tailWord_3413672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413672).length < 2 ^ (prefixWord ++ tailWord_3413672).sum := by decide
  have hdescent : baseEnd_3413672 < baseStart_3413672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413694 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_3413694 : Nat := 118140960795 + 3413694 * 2 ^ 59
def prefixEnd_3413694 : Nat := 4983230072969 + 3 ^ 40 * 3413694 * 2
def baseEnd_3413694 : Nat := 1752865829369472140225713

theorem tailTrace_3413694 : CollatzResearch.WordTrace tailWord_3413694 prefixEnd_3413694 1752865829369472140225713 := by
  unfold tailWord_3413694
  simp only [CollatzResearch.WordTrace]
  refine ⟨15563456111847140670539017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83005099263184750242874757 15563456111847140670539017)
  ·
    refine ⟨11672592083885355502904263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15563456111847140670539017 11672592083885355502904263)
    ·
      refine ⟨17508888125828033254356395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11672592083885355502904263 17508888125828033254356395)
      ·
        refine ⟨26263332188742049881534593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17508888125828033254356395 26263332188742049881534593)
        ·
          refine ⟨19697499141556537411150945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26263332188742049881534593 19697499141556537411150945)
          ·
            refine ⟨14773124356167403058363209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19697499141556537411150945 14773124356167403058363209)
            ·
              refine ⟨11079843267125552293772407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14773124356167403058363209 11079843267125552293772407)
              ·
                refine ⟨16619764900688328440658611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11079843267125552293772407 16619764900688328440658611)
                ·
                  refine ⟨24929647351032492660987917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16619764900688328440658611 24929647351032492660987917)
                  ·
                    refine ⟨9348617756637184747870469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24929647351032492660987917 9348617756637184747870469)
                    ·
                      refine ⟨1752865829369472140225713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9348617756637184747870469 1752865829369472140225713)
                      ·
                        rfl

theorem cell23_3413694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_3413694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413694 prefixEnd_3413694 := by exact prefixLift 3413694
  have htrace : WordTrace (prefixWord ++ tailWord_3413694) baseStart_3413694 baseEnd_3413694 := by
    simpa [prefixWord, tailWord_3413694, baseEnd_3413694] using wordTrace_append hprefix tailTrace_3413694
  have hstable : (prefixWord ++ tailWord_3413694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413694).length < 2 ^ (prefixWord ++ tailWord_3413694).sum := by decide
  have hdescent : baseEnd_3413694 < baseStart_3413694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413718 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3413718 : Nat := 118140960795 + 3413718 * 2 ^ 59
def prefixEnd_3413718 : Nat := 4983230072969 + 3 ^ 40 * 3413718 * 2
def baseEnd_3413718 : Nat := 1752878152905180046325603

theorem tailTrace_3413718 : CollatzResearch.WordTrace tailWord_3413718 prefixEnd_3413718 1752878152905180046325603 := by
  unfold tailWord_3413718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7781782765418136091449113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83005682831126784975457205 7781782765418136091449113)
  ·
    refine ⟨5836337074063602068586835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7781782765418136091449113 5836337074063602068586835)
    ·
      refine ⟨8754505611095403102880253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5836337074063602068586835 8754505611095403102880253)
      ·
        refine ⟨3282939604160776163580095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8754505611095403102880253 3282939604160776163580095)
        ·
          refine ⟨4924409406241164245370143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3282939604160776163580095 4924409406241164245370143)
          ·
            refine ⟨7386614109361746368055215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924409406241164245370143 7386614109361746368055215)
            ·
              refine ⟨11079921164042619552082823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7386614109361746368055215 11079921164042619552082823)
              ·
                refine ⟨16619881746063929328124235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11079921164042619552082823 16619881746063929328124235)
                ·
                  refine ⟨24929822619095893992186353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16619881746063929328124235 24929822619095893992186353)
                  ·
                    refine ⟨18697366964321920494139765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24929822619095893992186353 18697366964321920494139765)
                    ·
                      refine ⟨1752878152905180046325603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18697366964321920494139765 1752878152905180046325603)
                      ·
                        rfl

theorem cell23_3413718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3413718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413718 prefixEnd_3413718 := by exact prefixLift 3413718
  have htrace : WordTrace (prefixWord ++ tailWord_3413718) baseStart_3413718 baseEnd_3413718 := by
    simpa [prefixWord, tailWord_3413718, baseEnd_3413718] using wordTrace_append hprefix tailTrace_3413718
  have hstable : (prefixWord ++ tailWord_3413718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413718).length < 2 ^ (prefixWord ++ tailWord_3413718).sum := by decide
  have hdescent : baseEnd_3413718 < baseStart_3413718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413721 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 3, 4]
def baseStart_3413721 : Nat := 118140960795 + 3413721 * 2 ^ 59
def prefixEnd_3413721 : Nat := 4983230072969 + 3 ^ 40 * 3413721 * 2
def baseEnd_3413721 : Nat := 584293231115714511529363

theorem tailTrace_3413721 : CollatzResearch.WordTrace tailWord_3413721 prefixEnd_3413721 584293231115714511529363 := by
  unfold tailWord_3413721
  simp only [CollatzResearch.WordTrace]
  refine ⟨124508633665679308975545017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83005755777119539317030011 124508633665679308975545017)
  ·
    refine ⟨93381475249259481731658763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124508633665679308975545017 93381475249259481731658763)
    ·
      refine ⟨140072212873889222597488145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93381475249259481731658763 140072212873889222597488145)
      ·
        refine ⟨105054159655416916948116109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140072212873889222597488145 105054159655416916948116109)
        ·
          refine ⟨39395309870781343855543541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105054159655416916948116109 39395309870781343855543541)
          ·
            refine ⟨3693310300385750986457207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39395309870781343855543541 3693310300385750986457207)
            ·
              refine ⟨5539965450578626479685811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693310300385750986457207 5539965450578626479685811)
              ·
                refine ⟨8309948175867939719528717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539965450578626479685811 8309948175867939719528717)
                ·
                  refine ⟨3116230565950477394823269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8309948175867939719528717 3116230565950477394823269)
                  ·
                    refine ⟨584293231115714511529363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3116230565950477394823269 584293231115714511529363)
                    ·
                      rfl

theorem cell23_3413721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 4].length) (baseStart_3413721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413721 prefixEnd_3413721 := by exact prefixLift 3413721
  have htrace : WordTrace (prefixWord ++ tailWord_3413721) baseStart_3413721 baseEnd_3413721 := by
    simpa [prefixWord, tailWord_3413721, baseEnd_3413721] using wordTrace_append hprefix tailTrace_3413721
  have hstable : (prefixWord ++ tailWord_3413721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413721).length < 2 ^ (prefixWord ++ tailWord_3413721).sum := by decide
  have hdescent : baseEnd_3413721 < baseStart_3413721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413757 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_3413757 : Nat := 118140960795 + 3413757 * 2 ^ 59
def prefixEnd_3413757 : Nat := 4983230072969 + 3 ^ 40 * 3413757 * 2
def baseEnd_3413757 : Nat := 1752898178650705393737923

theorem tailTrace_3413757 : CollatzResearch.WordTrace tailWord_3413757 prefixEnd_3413757 1752898178650705393737923 := by
  unfold tailWord_3413757
  simp only [CollatzResearch.WordTrace]
  refine ⟨124509946693548887123855525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83006631129032591415903683 124509946693548887123855525)
  ·
    refine ⟨23345615005040416335722911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124509946693548887123855525 23345615005040416335722911)
    ·
      refine ⟨35018422507560624503584367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23345615005040416335722911 35018422507560624503584367)
      ·
        refine ⟨52527633761340936755376551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35018422507560624503584367 52527633761340936755376551)
        ·
          refine ⟨78791450642011405133064827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52527633761340936755376551 78791450642011405133064827)
          ·
            refine ⟨118187175963017107699597241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78791450642011405133064827 118187175963017107699597241)
            ·
              refine ⟨88640381972262830774697931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118187175963017107699597241 88640381972262830774697931)
              ·
                refine ⟨132960572958394246162046897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88640381972262830774697931 132960572958394246162046897)
                ·
                  refine ⟨99720429718795684621535173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132960572958394246162046897 99720429718795684621535173)
                  ·
                    refine ⟨18697580572274190866537845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99720429718795684621535173 18697580572274190866537845)
                    ·
                      refine ⟨1752898178650705393737923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18697580572274190866537845 1752898178650705393737923)
                      ·
                        rfl

theorem cell23_3413757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_3413757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413757 prefixEnd_3413757 := by exact prefixLift 3413757
  have htrace : WordTrace (prefixWord ++ tailWord_3413757) baseStart_3413757 baseEnd_3413757 := by
    simpa [prefixWord, tailWord_3413757, baseEnd_3413757] using wordTrace_append hprefix tailTrace_3413757
  have hstable : (prefixWord ++ tailWord_3413757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413757).length < 2 ^ (prefixWord ++ tailWord_3413757).sum := by decide
  have hdescent : baseEnd_3413757 < baseStart_3413757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413771 : List Nat := [1, 1, 1, 1, 5, 1, 4, 2, 2, 3, 2]
def baseStart_3413771 : Nat := 118140960795 + 3413771 * 2 ^ 59
def prefixEnd_3413771 : Nat := 4983230072969 + 3 ^ 40 * 3413771 * 2
def baseEnd_3413771 : Nat := 1752905367379868338962859

theorem tailTrace_3413771 : CollatzResearch.WordTrace tailWord_3413771 prefixEnd_3413771 1752905367379868338962859 := by
  unfold tailWord_3413771
  simp only [CollatzResearch.WordTrace]
  refine ⟨124510457315498167514865167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83006971543665445009910111 124510457315498167514865167)
  ·
    refine ⟨186765685973247251272297751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124510457315498167514865167 186765685973247251272297751)
    ·
      refine ⟨280148528959870876908446627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186765685973247251272297751 280148528959870876908446627)
      ·
        refine ⟨420222793439806315362669941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280148528959870876908446627 420222793439806315362669941)
        ·
          refine ⟨39395886884981842065250307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 420222793439806315362669941 39395886884981842065250307)
          ·
            refine ⟨59093830327472763097875461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39395886884981842065250307 59093830327472763097875461)
            ·
              refine ⟨11080093186401143080851649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59093830327472763097875461 11080093186401143080851649)
              ·
                refine ⟨8310069889800857310638737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11080093186401143080851649 8310069889800857310638737)
                ·
                  refine ⟨6232552417350642982979053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8310069889800857310638737 6232552417350642982979053)
                  ·
                    refine ⟨2337207156506491118617145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6232552417350642982979053 2337207156506491118617145)
                    ·
                      refine ⟨1752905367379868338962859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2337207156506491118617145 1752905367379868338962859)
                      ·
                        rfl

theorem cell23_3413771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 3, 2].length) (baseStart_3413771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413771 prefixEnd_3413771 := by exact prefixLift 3413771
  have htrace : WordTrace (prefixWord ++ tailWord_3413771) baseStart_3413771 baseEnd_3413771 := by
    simpa [prefixWord, tailWord_3413771, baseEnd_3413771] using wordTrace_append hprefix tailTrace_3413771
  have hstable : (prefixWord ++ tailWord_3413771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413771).length < 2 ^ (prefixWord ++ tailWord_3413771).sum := by decide
  have hdescent : baseEnd_3413771 < baseStart_3413771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413777 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 5, 6]
def baseStart_3413777 : Nat := 118140960795 + 3413777 * 2 ^ 59
def prefixEnd_3413777 : Nat := 4983230072969 + 3 ^ 40 * 3413777 * 2
def baseEnd_3413777 : Nat := 584302816087931771829277

theorem tailTrace_3413777 : CollatzResearch.WordTrace tailWord_3413777 prefixEnd_3413777 584302816087931771829277 := by
  unfold tailWord_3413777
  simp only [CollatzResearch.WordTrace]
  refine ⟨124510676153476430539583585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83007117435650953693055723 124510676153476430539583585)
  ·
    refine ⟨93383007115107322904687689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124510676153476430539583585 93383007115107322904687689)
    ·
      refine ⟨70037255336330492178515767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93383007115107322904687689 70037255336330492178515767)
      ·
        refine ⟨105055883004495738267773651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70037255336330492178515767 105055883004495738267773651)
        ·
          refine ⟨157583824506743607401660477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105055883004495738267773651 157583824506743607401660477)
          ·
            refine ⟨59093934190028852775622679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157583824506743607401660477 59093934190028852775622679)
            ·
              refine ⟨88640901285043279163434019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59093934190028852775622679 88640901285043279163434019)
              ·
                refine ⟨132961351927564918745151029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88640901285043279163434019 132961351927564918745151029)
                ·
                  refine ⟨12465126743209211132357909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132961351927564918745151029 12465126743209211132357909)
                  ·
                    refine ⟨584302816087931771829277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12465126743209211132357909 584302816087931771829277)
                    ·
                      rfl

theorem cell23_3413777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_3413777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413777 prefixEnd_3413777 := by exact prefixLift 3413777
  have htrace : WordTrace (prefixWord ++ tailWord_3413777) baseStart_3413777 baseEnd_3413777 := by
    simpa [prefixWord, tailWord_3413777, baseEnd_3413777] using wordTrace_append hprefix tailTrace_3413777
  have hstable : (prefixWord ++ tailWord_3413777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413777).length < 2 ^ (prefixWord ++ tailWord_3413777).sum := by decide
  have hdescent : baseEnd_3413777 < baseStart_3413777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413784 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_3413784 : Nat := 118140960795 + 3413784 * 2 ^ 59
def prefixEnd_3413784 : Nat := 4983230072969 + 3 ^ 40 * 3413784 * 2
def baseEnd_3413784 : Nat := 1752912042628376788100299

theorem tailTrace_3413784 : CollatzResearch.WordTrace tailWord_3413784 prefixEnd_3413784 1752912042628376788100299 := by
  unfold tailWord_3413784
  simp only [CollatzResearch.WordTrace]
  refine ⟨62255465732225535367544203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83007287642967380490058937 62255465732225535367544203)
  ·
    refine ⟨93383198598338303051316305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62255465732225535367544203 93383198598338303051316305)
    ·
      refine ⟨70037398948753727288487229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93383198598338303051316305 70037398948753727288487229)
      ·
        refine ⟨26264024605782647733182711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70037398948753727288487229 26264024605782647733182711)
        ·
          refine ⟨39396036908673971599774067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26264024605782647733182711 39396036908673971599774067)
          ·
            refine ⟨59094055363010957399661101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39396036908673971599774067 59094055363010957399661101)
            ·
              refine ⟨22160270761129109024872913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59094055363010957399661101 22160270761129109024872913)
              ·
                refine ⟨16620203070846831768654685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22160270761129109024872913 16620203070846831768654685)
                ·
                  refine ⟨6232576151567561913245507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16620203070846831768654685 6232576151567561913245507)
                  ·
                    refine ⟨9348864227351342869868261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6232576151567561913245507 9348864227351342869868261)
                    ·
                      refine ⟨1752912042628376788100299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9348864227351342869868261 1752912042628376788100299)
                      ·
                        rfl

theorem cell23_3413784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_3413784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413784 prefixEnd_3413784 := by exact prefixLift 3413784
  have htrace : WordTrace (prefixWord ++ tailWord_3413784) baseStart_3413784 baseEnd_3413784 := by
    simpa [prefixWord, tailWord_3413784, baseEnd_3413784] using wordTrace_append hprefix tailTrace_3413784
  have hstable : (prefixWord ++ tailWord_3413784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413784).length < 2 ^ (prefixWord ++ tailWord_3413784).sum := by decide
  have hdescent : baseEnd_3413784 < baseStart_3413784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413812 : List Nat := [2, 5, 1, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_3413812 : Nat := 118140960795 + 3413812 * 2 ^ 59
def prefixEnd_3413812 : Nat := 4983230072969 + 3 ^ 40 * 3413812 * 2
def baseEnd_3413812 : Nat := 1752926420086702678550171

theorem tailTrace_3413812 : CollatzResearch.WordTrace tailWord_3413812 prefixEnd_3413812 1752926420086702678550171 := by
  unfold tailWord_3413812
  simp only [CollatzResearch.WordTrace]
  refine ⟨62255976354174815758553845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83007968472233087678071793 62255976354174815758553845)
  ·
    refine ⟨5836497783203888977364423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62255976354174815758553845 5836497783203888977364423)
    ·
      refine ⟨8754746674805833466046635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5836497783203888977364423 8754746674805833466046635)
      ·
        refine ⟨13132120012208750199069953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8754746674805833466046635 13132120012208750199069953)
        ·
          refine ⟨9849090009156562649302465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13132120012208750199069953 9849090009156562649302465)
          ·
            refine ⟨7386817506867421986976849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9849090009156562649302465 7386817506867421986976849)
            ·
              refine ⟨5540113130150566490232637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7386817506867421986976849 5540113130150566490232637)
              ·
                refine ⟨2077542423806462433837239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5540113130150566490232637 2077542423806462433837239)
                ·
                  refine ⟨3116313635709693650755859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077542423806462433837239 3116313635709693650755859)
                  ·
                    refine ⟨4674470453564540476133789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3116313635709693650755859 4674470453564540476133789)
                    ·
                      refine ⟨1752926420086702678550171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4674470453564540476133789 1752926420086702678550171)
                      ·
                        rfl

theorem cell23_3413812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_3413812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413812 prefixEnd_3413812 := by exact prefixLift 3413812
  have htrace : WordTrace (prefixWord ++ tailWord_3413812) baseStart_3413812 baseEnd_3413812 := by
    simpa [prefixWord, tailWord_3413812, baseEnd_3413812] using wordTrace_append hprefix tailTrace_3413812
  have hstable : (prefixWord ++ tailWord_3413812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413812).length < 2 ^ (prefixWord ++ tailWord_3413812).sum := by decide
  have hdescent : baseEnd_3413812 < baseStart_3413812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413818 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4]
def baseStart_3413818 : Nat := 118140960795 + 3413818 * 2 ^ 59
def prefixEnd_3413818 : Nat := 4983230072969 + 3 ^ 40 * 3413818 * 2
def baseEnd_3413818 : Nat := 1752929500970629655075143

theorem tailTrace_3413818 : CollatzResearch.WordTrace tailWord_3413818 prefixEnd_3413818 1752929500970629655075143 := by
  unfold tailWord_3413818
  simp only [CollatzResearch.WordTrace]
  refine ⟨31128042886581973635456527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83008114364218596361217405 31128042886581973635456527)
  ·
    refine ⟨46692064329872960453184791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31128042886581973635456527 46692064329872960453184791)
    ·
      refine ⟨70038096494809440679777187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46692064329872960453184791 70038096494809440679777187)
      ·
        refine ⟨105057144742214161019665781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70038096494809440679777187 105057144742214161019665781)
        ·
          refine ⟨9849107319582577595593667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105057144742214161019665781 9849107319582577595593667)
          ·
            refine ⟨14773660979373866393390501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9849107319582577595593667 14773660979373866393390501)
            ·
              refine ⟨2770061433632599948760719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14773660979373866393390501 2770061433632599948760719)
              ·
                refine ⟨4155092150448899923141079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770061433632599948760719 4155092150448899923141079)
                ·
                  refine ⟨6232638225673349884711619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4155092150448899923141079 6232638225673349884711619)
                  ·
                    refine ⟨9348957338510024827067429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6232638225673349884711619 9348957338510024827067429)
                    ·
                      refine ⟨1752929500970629655075143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9348957338510024827067429 1752929500970629655075143)
                      ·
                        rfl

theorem cell23_3413818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4].length) (baseStart_3413818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413818 prefixEnd_3413818 := by exact prefixLift 3413818
  have htrace : WordTrace (prefixWord ++ tailWord_3413818) baseStart_3413818 baseEnd_3413818 := by
    simpa [prefixWord, tailWord_3413818, baseEnd_3413818] using wordTrace_append hprefix tailTrace_3413818
  have hstable : (prefixWord ++ tailWord_3413818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413818).length < 2 ^ (prefixWord ++ tailWord_3413818).sum := by decide
  have hdescent : baseEnd_3413818 < baseStart_3413818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413858 : List Nat := [3, 3, 2, 1, 2, 3, 2, 7]
def baseStart_3413858 : Nat := 118140960795 + 3413858 * 2 ^ 59
def prefixEnd_3413858 : Nat := 4983230072969 + 3 ^ 40 * 3413858 * 2
def baseEnd_3413858 : Nat := 64924075562844796243517

theorem tailTrace_3413858 : CollatzResearch.WordTrace tailWord_3413858 prefixEnd_3413858 64924075562844796243517 := by
  unfold tailWord_3413858
  simp only [CollatzResearch.WordTrace]
  refine ⟨31128407616545745343320557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83009086977455320915521485 31128407616545745343320557)
  ·
    refine ⟨11673152856204654503745209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31128407616545745343320557 11673152856204654503745209)
    ·
      refine ⟨8754864642153490877808907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11673152856204654503745209 8754864642153490877808907)
      ·
        refine ⟨13132296963230236316713361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8754864642153490877808907 13132296963230236316713361)
        ·
          refine ⟨9849222722422677237535021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13132296963230236316713361 9849222722422677237535021)
          ·
            refine ⟨3693458520908503964075633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9849222722422677237535021 3693458520908503964075633)
            ·
              refine ⟨2770093890681377973056725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3693458520908503964075633 2770093890681377973056725)
              ·
                refine ⟨64924075562844796243517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2770093890681377973056725 64924075562844796243517)
                ·
                  rfl

theorem cell23_3413858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 7].length) (baseStart_3413858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413858 prefixEnd_3413858 := by exact prefixLift 3413858
  have htrace : WordTrace (prefixWord ++ tailWord_3413858) baseStart_3413858 baseEnd_3413858 := by
    simpa [prefixWord, tailWord_3413858, baseEnd_3413858] using wordTrace_append hprefix tailTrace_3413858
  have hstable : (prefixWord ++ tailWord_3413858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413858).length < 2 ^ (prefixWord ++ tailWord_3413858).sum := by decide
  have hdescent : baseEnd_3413858 < baseStart_3413858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413864 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3413864 : Nat := 118140960795 + 3413864 * 2 ^ 59
def prefixEnd_3413864 : Nat := 4983230072969 + 3 ^ 40 * 3413864 * 2
def baseEnd_3413864 : Nat := 1752953121080736475099931

theorem tailTrace_3413864 : CollatzResearch.WordTrace tailWord_3413864 prefixEnd_3413864 1752953121080736475099931 := by
  unfold tailWord_3413864
  simp only [CollatzResearch.WordTrace]
  refine ⟨62256924652080622199000323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83009232869440829598667097 62256924652080622199000323)
  ·
    refine ⟨93385386978120933298500485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62256924652080622199000323 93385386978120933298500485)
    ·
      refine ⟨17509760058397674993468841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93385386978120933298500485 17509760058397674993468841)
      ·
        refine ⟨13132320043798256245101631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17509760058397674993468841 13132320043798256245101631)
        ·
          refine ⟨19698480065697384367652447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13132320043798256245101631 19698480065697384367652447)
          ·
            refine ⟨29547720098546076551478671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19698480065697384367652447 29547720098546076551478671)
            ·
              refine ⟨44321580147819114827218007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29547720098546076551478671 44321580147819114827218007)
              ·
                refine ⟨66482370221728672240827011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44321580147819114827218007 66482370221728672240827011)
                ·
                  refine ⟨99723555332593008361240517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66482370221728672240827011 99723555332593008361240517)
                  ·
                    refine ⟨18698166624861189067732597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99723555332593008361240517 18698166624861189067732597)
                    ·
                      refine ⟨1752953121080736475099931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18698166624861189067732597 1752953121080736475099931)
                      ·
                        rfl

theorem cell23_3413864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3413864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413864 prefixEnd_3413864 := by exact prefixLift 3413864
  have htrace : WordTrace (prefixWord ++ tailWord_3413864) baseStart_3413864 baseEnd_3413864 := by
    simpa [prefixWord, tailWord_3413864, baseEnd_3413864] using wordTrace_append hprefix tailTrace_3413864
  have hstable : (prefixWord ++ tailWord_3413864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413864).length < 2 ^ (prefixWord ++ tailWord_3413864).sum := by decide
  have hdescent : baseEnd_3413864 < baseStart_3413864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413874 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_3413874 : Nat := 118140960795 + 3413874 * 2 ^ 59
def prefixEnd_3413874 : Nat := 4983230072969 + 3 ^ 40 * 3413874 * 2
def baseEnd_3413874 : Nat := 1752958255887281435974885

theorem tailTrace_3413874 : CollatzResearch.WordTrace tailWord_3413874 prefixEnd_3413874 1752958255887281435974885 := by
  unfold tailWord_3413874
  simp only [CollatzResearch.WordTrace]
  refine ⟨31128553508531254026466169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83009476022750010737243117 31128553508531254026466169)
  ·
    refine ⟨23346415131398440519849627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31128553508531254026466169 23346415131398440519849627)
    ·
      refine ⟨35019622697097660779774441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23346415131398440519849627 35019622697097660779774441)
      ·
        refine ⟨26264717022823245584830831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35019622697097660779774441 26264717022823245584830831)
        ·
          refine ⟨39397075534234868377246247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26264717022823245584830831 39397075534234868377246247)
          ·
            refine ⟨59095613301352302565869371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39397075534234868377246247 59095613301352302565869371)
            ·
              refine ⟨88643419952028453848804057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59095613301352302565869371 88643419952028453848804057)
              ·
                refine ⟨66482564964021340386603043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88643419952028453848804057 66482564964021340386603043)
                ·
                  refine ⟨99723847446032010579904565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66482564964021340386603043 99723847446032010579904565)
                  ·
                    refine ⟨9349110698065500991866053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99723847446032010579904565 9349110698065500991866053)
                    ·
                      refine ⟨1752958255887281435974885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9349110698065500991866053 1752958255887281435974885)
                      ·
                        rfl

theorem cell23_3413874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_3413874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413874 prefixEnd_3413874 := by exact prefixLift 3413874
  have htrace : WordTrace (prefixWord ++ tailWord_3413874) baseStart_3413874 baseEnd_3413874 := by
    simpa [prefixWord, tailWord_3413874, baseEnd_3413874] using wordTrace_append hprefix tailTrace_3413874
  have hstable : (prefixWord ++ tailWord_3413874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413874).length < 2 ^ (prefixWord ++ tailWord_3413874).sum := by decide
  have hdescent : baseEnd_3413874 < baseStart_3413874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413886 : List Nat := [4, 2, 3, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_3413886 : Nat := 118140960795 + 3413886 * 2 ^ 59
def prefixEnd_3413886 : Nat := 4983230072969 + 3 ^ 40 * 3413886 * 2
def baseEnd_3413886 : Nat := 1752964417655135389024831

theorem tailTrace_3413886 : CollatzResearch.WordTrace tailWord_3413886 prefixEnd_3413886 1752964417655135389024831 := by
  unfold tailWord_3413886
  simp only [CollatzResearch.WordTrace]
  refine ⟨15564331463760192769412689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83009767806721028103534341 15564331463760192769412689)
  ·
    refine ⟨11673248597820144577059517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15564331463760192769412689 11673248597820144577059517)
    ·
      refine ⟨4377468224182554216397319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11673248597820144577059517 4377468224182554216397319)
      ·
        refine ⟨6566202336273831324595979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4377468224182554216397319 6566202336273831324595979)
        ·
          refine ⟨9849303504410746986893969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6566202336273831324595979 9849303504410746986893969)
          ·
            refine ⟨7386977628308060240170477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9849303504410746986893969 7386977628308060240170477)
            ·
              refine ⟨2770116610615522590063929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7386977628308060240170477 2770116610615522590063929)
              ·
                refine ⟨2077587457961641942547947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770116610615522590063929 2077587457961641942547947)
                ·
                  refine ⟨3116381186942462913821921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077587457961641942547947 3116381186942462913821921)
                  ·
                    refine ⟨2337285890206847185366441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3116381186942462913821921 2337285890206847185366441)
                    ·
                      refine ⟨1752964417655135389024831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2337285890206847185366441 1752964417655135389024831)
                      ·
                        rfl

theorem cell23_3413886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_3413886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413886 prefixEnd_3413886 := by exact prefixLift 3413886
  have htrace : WordTrace (prefixWord ++ tailWord_3413886) baseStart_3413886 baseEnd_3413886 := by
    simpa [prefixWord, tailWord_3413886, baseEnd_3413886] using wordTrace_append hprefix tailTrace_3413886
  have hstable : (prefixWord ++ tailWord_3413886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413886).length < 2 ^ (prefixWord ++ tailWord_3413886).sum := by decide
  have hdescent : baseEnd_3413886 < baseStart_3413886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413902 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3]
def baseStart_3413902 : Nat := 118140960795 + 3413902 * 2 ^ 59
def prefixEnd_3413902 : Nat := 4983230072969 + 3 ^ 40 * 3413902 * 2
def baseEnd_3413902 : Nat := 1752972633345607326424757

theorem tailTrace_3413902 : CollatzResearch.WordTrace tailWord_3413902 prefixEnd_3413902 1752972633345607326424757 := by
  unfold tailWord_3413902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15564404409752947110985495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83010156852015717925255973 15564404409752947110985495)
  ·
    refine ⟨23346606614629420666478243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15564404409752947110985495 23346606614629420666478243)
    ·
      refine ⟨35019909921944130999717365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23346606614629420666478243 35019909921944130999717365)
      ·
        refine ⟨3283116555182262281223503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35019909921944130999717365 3283116555182262281223503)
        ·
          refine ⟨4924674832773393421835255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283116555182262281223503 4924674832773393421835255)
          ·
            refine ⟨7387012249160090132752883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924674832773393421835255 7387012249160090132752883)
            ·
              refine ⟨11080518373740135199129325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387012249160090132752883 11080518373740135199129325)
              ·
                refine ⟨4155194390152550699673497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11080518373740135199129325 4155194390152550699673497)
                ·
                  refine ⟨3116395792614413024755123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4155194390152550699673497 3116395792614413024755123)
                  ·
                    refine ⟨4674593688921619537132685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3116395792614413024755123 4674593688921619537132685)
                    ·
                      refine ⟨1752972633345607326424757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4674593688921619537132685 1752972633345607326424757)
                      ·
                        rfl

theorem cell23_3413902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_3413902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413902 prefixEnd_3413902 := by exact prefixLift 3413902
  have htrace : WordTrace (prefixWord ++ tailWord_3413902) baseStart_3413902 baseEnd_3413902 := by
    simpa [prefixWord, tailWord_3413902, baseEnd_3413902] using wordTrace_append hprefix tailTrace_3413902
  have hstable : (prefixWord ++ tailWord_3413902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413902).length < 2 ^ (prefixWord ++ tailWord_3413902).sum := by decide
  have hdescent : baseEnd_3413902 < baseStart_3413902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413951 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 1, 7, 2]
def baseStart_3413951 : Nat := 118140960795 + 3413951 * 2 ^ 59
def prefixEnd_3413951 : Nat := 4983230072969 + 3 ^ 40 * 3413951 * 2
def baseEnd_3413951 : Nat := 1752997793897677634712031

theorem tailTrace_3413951 : CollatzResearch.WordTrace tailWord_3413951 prefixEnd_3413951 1752997793897677634712031 := by
  unfold tailWord_3413951
  simp only [CollatzResearch.WordTrace]
  refine ⟨124517022454846058256417707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83011348303230705504278471 124517022454846058256417707)
  ·
    refine ⟨186775533682269087384626561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124517022454846058256417707 186775533682269087384626561)
    ·
      refine ⟨140081650261701815538469921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186775533682269087384626561 140081650261701815538469921)
      ·
        refine ⟨105061237696276361653852441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140081650261701815538469921 105061237696276361653852441)
        ·
          refine ⟨78795928272207271240389331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105061237696276361653852441 78795928272207271240389331)
          ·
            refine ⟨118193892408310906860583997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78795928272207271240389331 118193892408310906860583997)
            ·
              refine ⟨44322709653116590072718999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118193892408310906860583997 44322709653116590072718999)
              ·
                refine ⟨66484064479674885109078499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44322709653116590072718999 66484064479674885109078499)
                ·
                  refine ⟨99726096719512327663617749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66484064479674885109078499 99726096719512327663617749)
                  ·
                    refine ⟨2337330391863570179616041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 99726096719512327663617749 2337330391863570179616041)
                    ·
                      refine ⟨1752997793897677634712031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2337330391863570179616041 1752997793897677634712031)
                      ·
                        rfl

theorem cell23_3413951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 7, 2].length) (baseStart_3413951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3413951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3413951 prefixEnd_3413951 := by exact prefixLift 3413951
  have htrace : WordTrace (prefixWord ++ tailWord_3413951) baseStart_3413951 baseEnd_3413951 := by
    simpa [prefixWord, tailWord_3413951, baseEnd_3413951] using wordTrace_append hprefix tailTrace_3413951
  have hstable : (prefixWord ++ tailWord_3413951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413951).length < 2 ^ (prefixWord ++ tailWord_3413951).sum := by decide
  have hdescent : baseEnd_3413951 < baseStart_3413951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414042 : List Nat := [3, 1, 1, 3, 1, 5, 1, 3, 1, 4]
def baseStart_3414042 : Nat := 118140960795 + 3414042 * 2 ^ 59
def prefixEnd_3414042 : Nat := 4983230072969 + 3 ^ 40 * 3414042 * 2
def baseEnd_3414042 : Nat := 584348173545745592891371

theorem tailTrace_3414042 : CollatzResearch.WordTrace tailWord_3414042 prefixEnd_3414042 584348173545745592891371 := by
  unfold tailWord_3414042
  simp only [CollatzResearch.WordTrace]
  refine ⟨31130085374379095199495095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83013560998344253865320253 31130085374379095199495095)
  ·
    refine ⟨46695128061568642799242643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31130085374379095199495095 46695128061568642799242643)
    ·
      refine ⟨70042692092352964198863965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46695128061568642799242643 70042692092352964198863965)
      ·
        refine ⟨26266009534632361574573987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70042692092352964198863965 26266009534632361574573987)
        ·
          refine ⟨39399014301948542361860981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26266009534632361574573987 39399014301948542361860981)
          ·
            refine ⟨3693657590807675846424467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39399014301948542361860981 3693657590807675846424467)
            ·
              refine ⟨5540486386211513769636701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693657590807675846424467 5540486386211513769636701)
              ·
                refine ⟨2077682394829317663613763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5540486386211513769636701 2077682394829317663613763)
                ·
                  refine ⟨3116523592243976495420645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077682394829317663613763 3116523592243976495420645)
                  ·
                    refine ⟨584348173545745592891371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3116523592243976495420645 584348173545745592891371)
                    ·
                      rfl

theorem cell23_3414042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_3414042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414042 prefixEnd_3414042 := by exact prefixLift 3414042
  have htrace : WordTrace (prefixWord ++ tailWord_3414042) baseStart_3414042 baseEnd_3414042 := by
    simpa [prefixWord, tailWord_3414042, baseEnd_3414042] using wordTrace_append hprefix tailTrace_3414042
  have hstable : (prefixWord ++ tailWord_3414042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414042).length < 2 ^ (prefixWord ++ tailWord_3414042).sum := by decide
  have hdescent : baseEnd_3414042 < baseStart_3414042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414065 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 3, 1, 3]
def baseStart_3414065 : Nat := 118140960795 + 3414065 * 2 ^ 59
def prefixEnd_3414065 : Nat := 4983230072969 + 3 ^ 40 * 3414065 * 2
def baseEnd_3414065 : Nat := 1753056330692290188686507

theorem tailTrace_3414065 : CollatzResearch.WordTrace tailWord_3414065 prefixEnd_3414065 1753056330692290188686507 := by
  unfold tailWord_3414065
  simp only [CollatzResearch.WordTrace]
  refine ⟨124521180376433055726067649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83014120250955370484045099 124521180376433055726067649)
  ·
    refine ⟨93390885282324791794550737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124521180376433055726067649 93390885282324791794550737)
    ·
      refine ⟨70043163961743593845913053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93390885282324791794550737 70043163961743593845913053)
      ·
        refine ⟨26266186485653847692217395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70043163961743593845913053 26266186485653847692217395)
        ·
          refine ⟨39399279728480771538326093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26266186485653847692217395 39399279728480771538326093)
          ·
            refine ⟨14774729898180289326872285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39399279728480771538326093 14774729898180289326872285)
            ·
              refine ⟨5540523711817608497577107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14774729898180289326872285 5540523711817608497577107)
              ·
                refine ⟨8310785567726412746365661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5540523711817608497577107 8310785567726412746365661)
                ·
                  refine ⟨3116544587897404779887123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8310785567726412746365661 3116544587897404779887123)
                  ·
                    refine ⟨4674816881846107169830685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3116544587897404779887123 4674816881846107169830685)
                    ·
                      refine ⟨1753056330692290188686507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4674816881846107169830685 1753056330692290188686507)
                      ·
                        rfl

theorem cell23_3414065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_3414065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414065 prefixEnd_3414065 := by exact prefixLift 3414065
  have htrace : WordTrace (prefixWord ++ tailWord_3414065) baseStart_3414065 baseEnd_3414065 := by
    simpa [prefixWord, tailWord_3414065, baseEnd_3414065] using wordTrace_append hprefix tailTrace_3414065
  have hstable : (prefixWord ++ tailWord_3414065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414065).length < 2 ^ (prefixWord ++ tailWord_3414065).sum := by decide
  have hdescent : baseEnd_3414065 < baseStart_3414065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414072 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 6]
def baseStart_3414072 : Nat := 118140960795 + 3414072 * 2 ^ 59
def prefixEnd_3414072 : Nat := 4983230072969 + 3 ^ 40 * 3414072 * 2
def baseEnd_3414072 : Nat := 194784436117430184588775

theorem tailTrace_3414072 : CollatzResearch.WordTrace tailWord_3414072 prefixEnd_3414072 194784436117430184588775 := by
  unfold tailWord_3414072
  simp only [CollatzResearch.WordTrace]
  refine ⟨62260717843703847960786235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83014290458271797281048313 62260717843703847960786235)
  ·
    refine ⟨93391076765555771941179353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62260717843703847960786235 93391076765555771941179353)
    ·
      refine ⟨70043307574166828955884515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93391076765555771941179353 70043307574166828955884515)
      ·
        refine ⟨105064961361250243433826773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70043307574166828955884515 105064961361250243433826773)
        ·
          refine ⟨2462460031904302580480315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 105064961361250243433826773 2462460031904302580480315)
          ·
            refine ⟨3693690047856453870720473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462460031904302580480315 3693690047856453870720473)
            ·
              refine ⟨2770267535892340403040355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3693690047856453870720473 2770267535892340403040355)
              ·
                refine ⟨4155401303838510604560533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770267535892340403040355 4155401303838510604560533)
                ·
                  refine ⟨194784436117430184588775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4155401303838510604560533 194784436117430184588775)
                  ·
                    rfl

theorem cell23_3414072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 6].length) (baseStart_3414072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414072 prefixEnd_3414072 := by exact prefixLift 3414072
  have htrace : WordTrace (prefixWord ++ tailWord_3414072) baseStart_3414072 baseEnd_3414072 := by
    simpa [prefixWord, tailWord_3414072, baseEnd_3414072] using wordTrace_append hprefix tailTrace_3414072
  have hstable : (prefixWord ++ tailWord_3414072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414072).length < 2 ^ (prefixWord ++ tailWord_3414072).sum := by decide
  have hdescent : baseEnd_3414072 < baseStart_3414072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414088 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_3414088 : Nat := 118140960795 + 3414088 * 2 ^ 59
def prefixEnd_3414088 : Nat := 4983230072969 + 3 ^ 40 * 3414088 * 2
def baseEnd_3414088 : Nat := 1753068140747343598698901

theorem tailTrace_3414088 : CollatzResearch.WordTrace tailWord_3414088 prefixEnd_3414088 1753068140747343598698901 := by
  unfold tailWord_3414088
  simp only [CollatzResearch.WordTrace]
  refine ⟨62261009627674865327077459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83014679503566487102769945 62261009627674865327077459)
  ·
    refine ⟨93391514441512297990616189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62261009627674865327077459 93391514441512297990616189)
    ·
      refine ⟨35021817915567111746481071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93391514441512297990616189 35021817915567111746481071)
      ·
        refine ⟨52532726873350667619721607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35021817915567111746481071 52532726873350667619721607)
        ·
          refine ⟨78799090310026001429582411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52532726873350667619721607 78799090310026001429582411)
          ·
            refine ⟨118198635465039002144373617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78799090310026001429582411 118198635465039002144373617)
            ·
              refine ⟨88648976598779251608280213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118198635465039002144373617 88648976598779251608280213)
              ·
                refine ⟨4155420778067777419138135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88648976598779251608280213 4155420778067777419138135)
                ·
                  refine ⟨6233131167101666128707203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4155420778067777419138135 6233131167101666128707203)
                  ·
                    refine ⟨9349696750652499193060805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6233131167101666128707203 9349696750652499193060805)
                    ·
                      refine ⟨1753068140747343598698901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9349696750652499193060805 1753068140747343598698901)
                      ·
                        rfl

theorem cell23_3414088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_3414088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414088 prefixEnd_3414088 := by exact prefixLift 3414088
  have htrace : WordTrace (prefixWord ++ tailWord_3414088) baseStart_3414088 baseEnd_3414088 := by
    simpa [prefixWord, tailWord_3414088, baseEnd_3414088] using wordTrace_append hprefix tailTrace_3414088
  have hstable : (prefixWord ++ tailWord_3414088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414088).length < 2 ^ (prefixWord ++ tailWord_3414088).sum := by decide
  have hdescent : baseEnd_3414088 < baseStart_3414088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414091 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 3]
def baseStart_3414091 : Nat := 118140960795 + 3414091 * 2 ^ 59
def prefixEnd_3414091 : Nat := 4983230072969 + 3 ^ 40 * 3414091 * 2
def baseEnd_3414091 : Nat := 1753069681189307086961387

theorem tailTrace_3414091 : CollatzResearch.WordTrace tailWord_3414091 prefixEnd_3414091 1753069681189307086961387 := by
  unfold tailWord_3414091
  simp only [CollatzResearch.WordTrace]
  refine ⟨124522128674338862166514127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83014752449559241444342751 124522128674338862166514127)
  ·
    refine ⟨186783193011508293249771191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124522128674338862166514127 186783193011508293249771191)
    ·
      refine ⟨280174789517262439874656787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186783193011508293249771191 280174789517262439874656787)
      ·
        refine ⟨420262184275893659811985181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280174789517262439874656787 420262184275893659811985181)
        ·
          refine ⟨157598319103460122429494443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420262184275893659811985181 157598319103460122429494443)
          ·
            refine ⟨236397478655190183644241665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157598319103460122429494443 236397478655190183644241665)
            ·
              refine ⟨177298108991392637733181249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236397478655190183644241665 177298108991392637733181249)
              ·
                refine ⟨132973581743544478299885937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177298108991392637733181249 132973581743544478299885937)
                ·
                  refine ⟨99730186307658358724914453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132973581743544478299885937 99730186307658358724914453)
                  ·
                    refine ⟨4674852483171485565230365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99730186307658358724914453 4674852483171485565230365)
                    ·
                      refine ⟨1753069681189307086961387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4674852483171485565230365 1753069681189307086961387)
                      ·
                        rfl

theorem cell23_3414091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 3].length) (baseStart_3414091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414091 prefixEnd_3414091 := by exact prefixLift 3414091
  have htrace : WordTrace (prefixWord ++ tailWord_3414091) baseStart_3414091 baseEnd_3414091 := by
    simpa [prefixWord, tailWord_3414091, baseEnd_3414091] using wordTrace_append hprefix tailTrace_3414091
  have hstable : (prefixWord ++ tailWord_3414091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414091).length < 2 ^ (prefixWord ++ tailWord_3414091).sum := by decide
  have hdescent : baseEnd_3414091 < baseStart_3414091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414105 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 1, 1, 4]
def baseStart_3414105 : Nat := 118140960795 + 3414105 * 2 ^ 59
def prefixEnd_3414105 : Nat := 4983230072969 + 3 ^ 40 * 3414105 * 2
def baseEnd_3414105 : Nat := 1753076869918470032186323

theorem tailTrace_3414105 : CollatzResearch.WordTrace tailWord_3414105 prefixEnd_3414105 1753076869918470032186323 := by
  unfold tailWord_3414105
  simp only [CollatzResearch.WordTrace]
  refine ⟨124522639296288142557523769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83015092864192095038349179 124522639296288142557523769)
  ·
    refine ⟨93391979472216106918142827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124522639296288142557523769 93391979472216106918142827)
    ·
      refine ⟨140087969208324160377214241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93391979472216106918142827 140087969208324160377214241)
      ·
        refine ⟨105065976906243120282910681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140087969208324160377214241 105065976906243120282910681)
        ·
          refine ⟨78799482679682340212183011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105065976906243120282910681 78799482679682340212183011)
          ·
            refine ⟨118199224019523510318274517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78799482679682340212183011 118199224019523510318274517)
            ·
              refine ⟨2770294312957582273084559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 118199224019523510318274517 2770294312957582273084559)
              ·
                refine ⟨4155441469436373409626839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770294312957582273084559 4155441469436373409626839)
                ·
                  refine ⟨6233162204154560114440259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4155441469436373409626839 6233162204154560114440259)
                  ·
                    refine ⟨9349743306231840171660389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6233162204154560114440259 9349743306231840171660389)
                    ·
                      refine ⟨1753076869918470032186323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9349743306231840171660389 1753076869918470032186323)
                      ·
                        rfl

theorem cell23_3414105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 1, 1, 4].length) (baseStart_3414105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414105 prefixEnd_3414105 := by exact prefixLift 3414105
  have htrace : WordTrace (prefixWord ++ tailWord_3414105) baseStart_3414105 baseEnd_3414105 := by
    simpa [prefixWord, tailWord_3414105, baseEnd_3414105] using wordTrace_append hprefix tailTrace_3414105
  have hstable : (prefixWord ++ tailWord_3414105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414105).length < 2 ^ (prefixWord ++ tailWord_3414105).sum := by decide
  have hdescent : baseEnd_3414105 < baseStart_3414105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414110 : List Nat := [4, 4, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3414110 : Nat := 118140960795 + 3414110 * 2 ^ 59
def prefixEnd_3414110 : Nat := 4983230072969 + 3 ^ 40 * 3414110 * 2
def baseEnd_3414110 : Nat := 584359812440580837541267

theorem tailTrace_3414110 : CollatzResearch.WordTrace tailWord_3414110 prefixEnd_3414110 584359812440580837541267 := by
  unfold tailWord_3414110
  simp only [CollatzResearch.WordTrace]
  refine ⟨15565352707658753551431973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83015214440846685607637189 15565352707658753551431973)
  ·
    refine ⟨2918503632686016290893495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15565352707658753551431973 2918503632686016290893495)
    ·
      refine ⟨4377755449029024436340243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918503632686016290893495 4377755449029024436340243)
      ·
        refine ⟨6566633173543536654510365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4377755449029024436340243 6566633173543536654510365)
        ·
          refine ⟨2462487440078826245441387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6566633173543536654510365 2462487440078826245441387)
          ·
            refine ⟨3693731160118239368162081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462487440078826245441387 3693731160118239368162081)
            ·
              refine ⟨2770298370088679526121561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3693731160118239368162081 2770298370088679526121561)
              ·
                refine ⟨2077723777566509644591171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770298370088679526121561 2077723777566509644591171)
                ·
                  refine ⟨3116585666349764466886757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077723777566509644591171 3116585666349764466886757)
                  ·
                    refine ⟨584359812440580837541267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3116585666349764466886757 584359812440580837541267)
                    ·
                      rfl

theorem cell23_3414110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3414110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414110 prefixEnd_3414110 := by exact prefixLift 3414110
  have htrace : WordTrace (prefixWord ++ tailWord_3414110) baseStart_3414110 baseEnd_3414110 := by
    simpa [prefixWord, tailWord_3414110, baseEnd_3414110] using wordTrace_append hprefix tailTrace_3414110
  have hstable : (prefixWord ++ tailWord_3414110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414110).length < 2 ^ (prefixWord ++ tailWord_3414110).sum := by decide
  have hdescent : baseEnd_3414110 < baseStart_3414110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414128 : List Nat := [2, 1, 1, 1, 5, 4, 1, 8]
def baseStart_3414128 : Nat := 118140960795 + 3414128 * 2 ^ 59
def prefixEnd_3414128 : Nat := 4983230072969 + 3 ^ 40 * 3414128 * 2
def baseEnd_3414128 : Nat := 64929210369389757118471

theorem tailTrace_3414128 : CollatzResearch.WordTrace tailWord_3414128 prefixEnd_3414128 64929210369389757118471 := by
  unfold tailWord_3414128
  simp only [CollatzResearch.WordTrace]
  refine ⟨62261739087602408742805519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83015652116803211657074025 62261739087602408742805519)
  ·
    refine ⟨93392608631403613114208279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62261739087602408742805519 93392608631403613114208279)
    ·
      refine ⟨140088912947105419671312419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93392608631403613114208279 140088912947105419671312419)
      ·
        refine ⟨210133369420658129506968629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140088912947105419671312419 210133369420658129506968629)
        ·
          refine ⟨19700003383186699641278309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210133369420658129506968629 19700003383186699641278309)
          ·
            refine ⟨3693750634347506182739683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19700003383186699641278309 3693750634347506182739683)
            ·
              refine ⟨5540625951521259274109525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693750634347506182739683 5540625951521259274109525)
              ·
                refine ⟨64929210369389757118471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5540625951521259274109525 64929210369389757118471)
                ·
                  rfl

theorem cell23_3414128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 8].length) (baseStart_3414128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414128 prefixEnd_3414128 := by exact prefixLift 3414128
  have htrace : WordTrace (prefixWord ++ tailWord_3414128) baseStart_3414128 baseEnd_3414128 := by
    simpa [prefixWord, tailWord_3414128, baseEnd_3414128] using wordTrace_append hprefix tailTrace_3414128
  have hstable : (prefixWord ++ tailWord_3414128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414128).length < 2 ^ (prefixWord ++ tailWord_3414128).sum := by decide
  have hdescent : baseEnd_3414128 < baseStart_3414128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414145 : List Nat := [1, 2, 4, 2, 3, 1, 3, 7]
def baseStart_3414145 : Nat := 118140960795 + 3414145 * 2 ^ 59
def prefixEnd_3414145 : Nat := 4983230072969 + 3 ^ 40 * 3414145 * 2
def baseEnd_3414145 : Nat := 64929533672024069469857

theorem tailTrace_3414145 : CollatzResearch.WordTrace tailWord_3414145 prefixEnd_3414145 64929533672024069469857 := by
  unfold tailWord_3414145
  simp only [CollatzResearch.WordTrace]
  refine ⟨124524098216143229388979889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83016065477428819592653259 124524098216143229388979889)
  ·
    refine ⟨93393073662107422041734917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124524098216143229388979889 93393073662107422041734917)
    ·
      refine ⟨17511201311645141632825297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93393073662107422041734917 17511201311645141632825297)
      ·
        refine ⟨13133400983733856224618973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17511201311645141632825297 13133400983733856224618973)
        ·
          refine ⟨4925025368900196084232115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13133400983733856224618973 4925025368900196084232115)
          ·
            refine ⟨7387538053350294126348173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925025368900196084232115 7387538053350294126348173)
            ·
              refine ⟨2770326770006360297380565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7387538053350294126348173 2770326770006360297380565)
              ·
                refine ⟨64929533672024069469857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2770326770006360297380565 64929533672024069469857)
                ·
                  rfl

theorem cell23_3414145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 7].length) (baseStart_3414145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414145 prefixEnd_3414145 := by exact prefixLift 3414145
  have htrace : WordTrace (prefixWord ++ tailWord_3414145) baseStart_3414145 baseEnd_3414145 := by
    simpa [prefixWord, tailWord_3414145, baseEnd_3414145] using wordTrace_append hprefix tailTrace_3414145
  have hstable : (prefixWord ++ tailWord_3414145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414145).length < 2 ^ (prefixWord ++ tailWord_3414145).sum := by decide
  have hdescent : baseEnd_3414145 < baseStart_3414145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414171 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 4, 6]
def baseStart_3414171 : Nat := 118140960795 + 3414171 * 2 ^ 59
def prefixEnd_3414171 : Nat := 4983230072969 + 3 ^ 40 * 3414171 * 2
def baseEnd_3414171 : Nat := 584370253213888924653673

theorem tailTrace_3414171 : CollatzResearch.WordTrace tailWord_3414171 prefixEnd_3414171 584370253213888924653673 := by
  unfold tailWord_3414171
  simp only [CollatzResearch.WordTrace]
  refine ⟨124525046514049035829426367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83016697676032690552950911 124525046514049035829426367)
  ·
    refine ⟨186787569771073553744139551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124525046514049035829426367 186787569771073553744139551)
    ·
      refine ⟨280181354656610330616209327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186787569771073553744139551 280181354656610330616209327)
      ·
        refine ⟨420272031984915495924313991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280181354656610330616209327 420272031984915495924313991)
        ·
          refine ⟨630408047977373243886470987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420272031984915495924313991 630408047977373243886470987)
          ·
            refine ⟨945612071966059865829706481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630408047977373243886470987 945612071966059865829706481)
            ·
              refine ⟨709209053974544899372279861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 945612071966059865829706481 709209053974544899372279861)
              ·
                refine ⟨66488348810113584316151237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 709209053974544899372279861 66488348810113584316151237)
                ·
                  refine ⟨12466565401896297059278357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66488348810113584316151237 12466565401896297059278357)
                  ·
                    refine ⟨584370253213888924653673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12466565401896297059278357 584370253213888924653673)
                    ·
                      rfl

theorem cell23_3414171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 6].length) (baseStart_3414171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414171 prefixEnd_3414171 := by exact prefixLift 3414171
  have htrace : WordTrace (prefixWord ++ tailWord_3414171) baseStart_3414171 baseEnd_3414171 := by
    simpa [prefixWord, tailWord_3414171, baseEnd_3414171] using wordTrace_append hprefix tailTrace_3414171
  have hstable : (prefixWord ++ tailWord_3414171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414171).length < 2 ^ (prefixWord ++ tailWord_3414171).sum := by decide
  have hdescent : baseEnd_3414171 < baseStart_3414171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414196 : List Nat := [2, 5, 3, 1, 1, 2, 2, 7]
def baseStart_3414196 : Nat := 118140960795 + 3414196 * 2 ^ 59
def prefixEnd_3414196 : Nat := 4983230072969 + 3 ^ 40 * 3414196 * 2
def baseEnd_3414196 : Nat := 64930503579927006524015

theorem tailTrace_3414196 : CollatzResearch.WordTrace tailWord_3414196 prefixEnd_3414196 64930503579927006524015 := by
  unfold tailWord_3414196
  simp only [CollatzResearch.WordTrace]
  refine ⟨62262979169479232549543221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83017305559305643399390961 62262979169479232549543221)
  ·
    refine ⟨5837154297138678051519677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62262979169479232549543221 5837154297138678051519677)
    ·
      refine ⟨2188932861427004269319879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5837154297138678051519677 2188932861427004269319879)
      ·
        refine ⟨3283399292140506403979819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188932861427004269319879 3283399292140506403979819)
        ·
          refine ⟨4925098938210759605969729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283399292140506403979819 4925098938210759605969729)
          ·
            refine ⟨3693824203658069704477297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4925098938210759605969729 3693824203658069704477297)
            ·
              refine ⟨2770368152743552278357973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3693824203658069704477297 2770368152743552278357973)
              ·
                refine ⟨64930503579927006524015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2770368152743552278357973 64930503579927006524015)
                ·
                  rfl

theorem cell23_3414196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 7].length) (baseStart_3414196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414196 prefixEnd_3414196 := by exact prefixLift 3414196
  have htrace : WordTrace (prefixWord ++ tailWord_3414196) baseStart_3414196 baseEnd_3414196 := by
    simpa [prefixWord, tailWord_3414196, baseEnd_3414196] using wordTrace_append hprefix tailTrace_3414196
  have hstable : (prefixWord ++ tailWord_3414196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414196).length < 2 ^ (prefixWord ++ tailWord_3414196).sum := by decide
  have hdescent : baseEnd_3414196 < baseStart_3414196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414305 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_3414305 : Nat := 118140960795 + 3414305 * 2 ^ 59
def prefixEnd_3414305 : Nat := 4983230072969 + 3 ^ 40 * 3414305 * 2
def baseEnd_3414305 : Nat := 1753179566049369249685403

theorem tailTrace_3414305 : CollatzResearch.WordTrace tailWord_3414305 prefixEnd_3414305 1753179566049369249685403 := by
  unfold tailWord_3414305
  simp only [CollatzResearch.WordTrace]
  refine ⟨124529933895563576714804369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83019955930375717809869579 124529933895563576714804369)
  ·
    refine ⟨93397450421672682536103277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124529933895563576714804369 93397450421672682536103277)
    ·
      refine ⟨35024043908127255951038729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93397450421672682536103277 35024043908127255951038729)
      ·
        refine ⟨26268032931095441963279047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35024043908127255951038729 26268032931095441963279047)
        ·
          refine ⟨39402049396643162944918571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26268032931095441963279047 39402049396643162944918571)
          ·
            refine ⟨59103074094964744417377857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39402049396643162944918571 59103074094964744417377857)
            ·
              refine ⟨44327305571223558313033393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59103074094964744417377857 44327305571223558313033393)
              ·
                refine ⟨33245479178417668734775045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44327305571223558313033393 33245479178417668734775045)
                ·
                  refine ⟨6233527345953312887770321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33245479178417668734775045 6233527345953312887770321)
                  ·
                    refine ⟨4675145509464984665827741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6233527345953312887770321 4675145509464984665827741)
                    ·
                      refine ⟨1753179566049369249685403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4675145509464984665827741 1753179566049369249685403)
                      ·
                        rfl

theorem cell23_3414305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_3414305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414305 prefixEnd_3414305 := by exact prefixLift 3414305
  have htrace : WordTrace (prefixWord ++ tailWord_3414305) baseStart_3414305 baseEnd_3414305 := by
    simpa [prefixWord, tailWord_3414305, baseEnd_3414305] using wordTrace_append hprefix tailTrace_3414305
  have hstable : (prefixWord ++ tailWord_3414305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414305).length < 2 ^ (prefixWord ++ tailWord_3414305).sum := by decide
  have hdescent : baseEnd_3414305 < baseStart_3414305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414322 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_3414322 : Nat := 118140960795 + 3414322 * 2 ^ 59
def prefixEnd_3414322 : Nat := 4983230072969 + 3 ^ 40 * 3414322 * 2
def baseEnd_3414322 : Nat := 1753188295220495683172825

theorem tailTrace_3414322 : CollatzResearch.WordTrace tailWord_3414322 prefixEnd_3414322 1753188295220495683172825 := by
  unfold tailWord_3414322
  simp only [CollatzResearch.WordTrace]
  refine ⟨31132638484125497154543305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83020369291001325745448813 31132638484125497154543305)
  ·
    refine ⟨23349478863094122865907479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31132638484125497154543305 23349478863094122865907479)
    ·
      refine ⟨35024218294641184298861219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23349478863094122865907479 35024218294641184298861219)
      ·
        refine ⟨52536327441961776448291829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35024218294641184298861219 52536327441961776448291829)
        ·
          refine ⟨4925280697683916542027359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52536327441961776448291829 4925280697683916542027359)
          ·
            refine ⟨7387921046525874813041039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925280697683916542027359 7387921046525874813041039)
            ·
              refine ⟨11081881569788812219561559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387921046525874813041039 11081881569788812219561559)
              ·
                refine ⟨16622822354683218329342339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11081881569788812219561559 16622822354683218329342339)
                ·
                  refine ⟨24934233532024827494013509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16622822354683218329342339 24934233532024827494013509)
                  ·
                    refine ⟨4675168787254655155127533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24934233532024827494013509 4675168787254655155127533)
                    ·
                      refine ⟨1753188295220495683172825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4675168787254655155127533 1753188295220495683172825)
                      ·
                        rfl

theorem cell23_3414322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_3414322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414322 prefixEnd_3414322 := by exact prefixLift 3414322
  have htrace : WordTrace (prefixWord ++ tailWord_3414322) baseStart_3414322 baseEnd_3414322 := by
    simpa [prefixWord, tailWord_3414322, baseEnd_3414322] using wordTrace_append hprefix tailTrace_3414322
  have hstable : (prefixWord ++ tailWord_3414322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414322).length < 2 ^ (prefixWord ++ tailWord_3414322).sum := by decide
  have hdescent : baseEnd_3414322 < baseStart_3414322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414329 : List Nat := [1, 2, 1, 6, 1, 1, 1, 5, 1, 4]
def baseStart_3414329 : Nat := 118140960795 + 3414329 * 2 ^ 59
def prefixEnd_3414329 : Nat := 4983230072969 + 3 ^ 40 * 3414329 * 2
def baseEnd_3414329 : Nat := 584397296528359051928431

theorem tailTrace_3414329 : CollatzResearch.WordTrace tailWord_3414329 prefixEnd_3414329 584397296528359051928431 := by
  unfold tailWord_3414329
  simp only [CollatzResearch.WordTrace]
  refine ⟨124530809247476628813678041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83020539498317752542452027 124530809247476628813678041)
  ·
    refine ⟨93398106935607471610258531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124530809247476628813678041 93398106935607471610258531)
    ·
      refine ⟨140097160403411207415387797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93398106935607471610258531 140097160403411207415387797)
      ·
        refine ⟨6567054393909900347596303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140097160403411207415387797 6567054393909900347596303)
        ·
          refine ⟨9850581590864850521394455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6567054393909900347596303 9850581590864850521394455)
          ·
            refine ⟨14775872386297275782091683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9850581590864850521394455 14775872386297275782091683)
            ·
              refine ⟨22163808579445913673137525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14775872386297275782091683 22163808579445913673137525)
              ·
                refine ⟨2077857054323054406856643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22163808579445913673137525 2077857054323054406856643)
                ·
                  refine ⟨3116785581484581610284965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077857054323054406856643 3116785581484581610284965)
                  ·
                    refine ⟨584397296528359051928431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3116785581484581610284965 584397296528359051928431)
                    ·
                      rfl

theorem cell23_3414329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 5, 1, 4].length) (baseStart_3414329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414329 prefixEnd_3414329 := by exact prefixLift 3414329
  have htrace : WordTrace (prefixWord ++ tailWord_3414329) baseStart_3414329 baseEnd_3414329 := by
    simpa [prefixWord, tailWord_3414329, baseEnd_3414329] using wordTrace_append hprefix tailTrace_3414329
  have hstable : (prefixWord ++ tailWord_3414329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414329).length < 2 ^ (prefixWord ++ tailWord_3414329).sum := by decide
  have hdescent : baseEnd_3414329 < baseStart_3414329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414352 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 3, 1, 3]
def baseStart_3414352 : Nat := 118140960795 + 3414352 * 2 ^ 59
def prefixEnd_3414352 : Nat := 4983230072969 + 3 ^ 40 * 3414352 * 2
def baseEnd_3414352 : Nat := 1753203699640130565797687

theorem tailTrace_3414352 : CollatzResearch.WordTrace tailWord_3414352 prefixEnd_3414352 1753203699640130565797687 := by
  unfold tailWord_3414352
  simp only [CollatzResearch.WordTrace]
  refine ⟨62265824063196651870882655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83021098750928869161176873 62265824063196651870882655)
  ·
    refine ⟨93398736094794977806323983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62265824063196651870882655 93398736094794977806323983)
    ·
      refine ⟨140098104142192466709485975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93398736094794977806323983 140098104142192466709485975)
      ·
        refine ⟨210147156213288700064228963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140098104142192466709485975 210147156213288700064228963)
        ·
          refine ⟨315220734319933050096343445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210147156213288700064228963 315220734319933050096343445)
          ·
            refine ⟨14775971921246861723266099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 315220734319933050096343445 14775971921246861723266099)
            ·
              refine ⟨22163957881870292584899149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14775971921246861723266099 22163957881870292584899149)
              ·
                refine ⟨8311484205701359719337181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22163957881870292584899149 8311484205701359719337181)
                ·
                  refine ⟨3116806577138009894751443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8311484205701359719337181 3116806577138009894751443)
                  ·
                    refine ⟨4675209865707014842127165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3116806577138009894751443 4675209865707014842127165)
                    ·
                      refine ⟨1753203699640130565797687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4675209865707014842127165 1753203699640130565797687)
                      ·
                        rfl

theorem cell23_3414352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3, 1, 3].length) (baseStart_3414352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414352 prefixEnd_3414352 := by exact prefixLift 3414352
  have htrace : WordTrace (prefixWord ++ tailWord_3414352) baseStart_3414352 baseEnd_3414352 := by
    simpa [prefixWord, tailWord_3414352, baseEnd_3414352] using wordTrace_append hprefix tailTrace_3414352
  have hstable : (prefixWord ++ tailWord_3414352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414352).length < 2 ^ (prefixWord ++ tailWord_3414352).sum := by decide
  have hdescent : baseEnd_3414352 < baseStart_3414352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414372 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_3414372 : Nat := 118140960795 + 3414372 * 2 ^ 59
def prefixEnd_3414372 : Nat := 4983230072969 + 3 ^ 40 * 3414372 * 2
def baseEnd_3414372 : Nat := 584404656417740162515865

theorem tailTrace_3414372 : CollatzResearch.WordTrace tailWord_3414372 prefixEnd_3414372 584404656417740162515865 := by
  unfold tailWord_3414372
  simp only [CollatzResearch.WordTrace]
  refine ⟨62266188793160423578746685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83021585057547231438328913 62266188793160423578746685)
  ·
    refine ⟨23349820797435158842030007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62266188793160423578746685 23349820797435158842030007)
    ·
      refine ⟨35024731196152738263045011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23349820797435158842030007 35024731196152738263045011)
      ·
        refine ⟨52537096794229107394567517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35024731196152738263045011 52537096794229107394567517)
        ·
          refine ⟨19701411297835915272962819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52537096794229107394567517 19701411297835915272962819)
          ·
            refine ⟨29552116946753872909444229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19701411297835915272962819 29552116946753872909444229)
            ·
              refine ⟨5541021927516351170520793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29552116946753872909444229 5541021927516351170520793)
              ·
                refine ⟨4155766445637263377890595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5541021927516351170520793 4155766445637263377890595)
                ·
                  refine ⟨6233649668455895066835893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4155766445637263377890595 6233649668455895066835893)
                  ·
                    refine ⟨584404656417740162515865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6233649668455895066835893 584404656417740162515865)
                    ·
                      rfl

theorem cell23_3414372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_3414372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414372 prefixEnd_3414372 := by exact prefixLift 3414372
  have htrace : WordTrace (prefixWord ++ tailWord_3414372) baseStart_3414372 baseEnd_3414372 := by
    simpa [prefixWord, tailWord_3414372, baseEnd_3414372] using wordTrace_append hprefix tailTrace_3414372
  have hstable : (prefixWord ++ tailWord_3414372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414372).length < 2 ^ (prefixWord ++ tailWord_3414372).sum := by decide
  have hdescent : baseEnd_3414372 < baseStart_3414372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414386 : List Nat := [3, 2, 1, 2, 1, 3, 3, 3, 1, 1, 3]
def baseStart_3414386 : Nat := 118140960795 + 3414386 * 2 ^ 59
def prefixEnd_3414386 : Nat := 4983230072969 + 3 ^ 40 * 3414386 * 2
def baseEnd_3414386 : Nat := 1753221157982383432772531

theorem tailTrace_3414386 : CollatzResearch.WordTrace tailWord_3414386 prefixEnd_3414386 1753221157982383432772531 := by
  unfold tailWord_3414386
  simp only [CollatzResearch.WordTrace]
  refine ⟨31133222052067531887125753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83021925472180085032335341 31133222052067531887125753)
  ·
    refine ⟨23349916539050648915344315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31133222052067531887125753 23349916539050648915344315)
    ·
      refine ⟨35024874808575973373016473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23349916539050648915344315 35024874808575973373016473)
      ·
        refine ⟨26268656106431980029762355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35024874808575973373016473 26268656106431980029762355)
        ·
          refine ⟨39402984159647970044643533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26268656106431980029762355 39402984159647970044643533)
          ·
            refine ⟨14776119059867988766741325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39402984159647970044643533 14776119059867988766741325)
            ·
              refine ⟨5541044647450495787527997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14776119059867988766741325 5541044647450495787527997)
              ·
                refine ⟨2077891742793935920322999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5541044647450495787527997 2077891742793935920322999)
                ·
                  refine ⟨3116837614190903880484499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077891742793935920322999 3116837614190903880484499)
                  ·
                    refine ⟨4675256421286355820726749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3116837614190903880484499 4675256421286355820726749)
                    ·
                      refine ⟨1753221157982383432772531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4675256421286355820726749 1753221157982383432772531)
                      ·
                        rfl

theorem cell23_3414386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_3414386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414386 prefixEnd_3414386 := by exact prefixLift 3414386
  have htrace : WordTrace (prefixWord ++ tailWord_3414386) baseStart_3414386 baseEnd_3414386 := by
    simpa [prefixWord, tailWord_3414386, baseEnd_3414386] using wordTrace_append hprefix tailTrace_3414386
  have hstable : (prefixWord ++ tailWord_3414386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414386).length < 2 ^ (prefixWord ++ tailWord_3414386).sum := by decide
  have hdescent : baseEnd_3414386 < baseStart_3414386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414395 : List Nat := [1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 5]
def baseStart_3414395 : Nat := 118140960795 + 3414395 * 2 ^ 59
def prefixEnd_3414395 : Nat := 4983230072969 + 3 ^ 40 * 3414395 * 2
def baseEnd_3414395 : Nat := 1753225779308273897559989

theorem tailTrace_3414395 : CollatzResearch.WordTrace tailWord_3414395 prefixEnd_3414395 1753225779308273897559989 := by
  unfold tailWord_3414395
  simp only [CollatzResearch.WordTrace]
  refine ⟨124533216465237522085580639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83022144310158348057053759 124533216465237522085580639)
  ·
    refine ⟨186799824697856283128370959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124533216465237522085580639 186799824697856283128370959)
    ·
      refine ⟨280199737046784424692556439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186799824697856283128370959 280199737046784424692556439)
      ·
        refine ⟨420299605570176637038834659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280199737046784424692556439 420299605570176637038834659)
        ·
          refine ⟨630449408355264955558251989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420299605570176637038834659 630449408355264955558251989)
          ·
            refine ⟨14776158008326522395896531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 630449408355264955558251989 14776158008326522395896531)
            ·
              refine ⟨22164237012489783593844797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14776158008326522395896531 22164237012489783593844797)
              ·
                refine ⟨8311588879683668847691799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22164237012489783593844797 8311588879683668847691799)
                ·
                  refine ⟨12467383319525503271537699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8311588879683668847691799 12467383319525503271537699)
                  ·
                    refine ⟨18701074979288254907306549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12467383319525503271537699 18701074979288254907306549)
                    ·
                      refine ⟨1753225779308273897559989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18701074979288254907306549 1753225779308273897559989)
                      ·
                        rfl

theorem cell23_3414395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 5].length) (baseStart_3414395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414395 prefixEnd_3414395 := by exact prefixLift 3414395
  have htrace : WordTrace (prefixWord ++ tailWord_3414395) baseStart_3414395 baseEnd_3414395 := by
    simpa [prefixWord, tailWord_3414395, baseEnd_3414395] using wordTrace_append hprefix tailTrace_3414395
  have hstable : (prefixWord ++ tailWord_3414395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414395).length < 2 ^ (prefixWord ++ tailWord_3414395).sum := by decide
  have hdescent : baseEnd_3414395 < baseStart_3414395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414403 : List Nat := [1, 1, 1, 3, 6, 1, 3, 2, 1, 1, 3]
def baseStart_3414403 : Nat := 118140960795 + 3414403 * 2 ^ 59
def prefixEnd_3414403 : Nat := 4983230072969 + 3 ^ 40 * 3414403 * 2
def baseEnd_3414403 : Nat := 1753229887153509866259953

theorem tailTrace_3414403 : CollatzResearch.WordTrace tailWord_3414403 prefixEnd_3414403 1753229887153509866259953 := by
  unfold tailWord_3414403
  simp only [CollatzResearch.WordTrace]
  refine ⟨124533508249208539451871863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83022338832805692967914575 124533508249208539451871863)
  ·
    refine ⟨186800262373812809177807795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124533508249208539451871863 186800262373812809177807795)
    ·
      refine ⟨280200393560719213766711693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186800262373812809177807795 280200393560719213766711693)
      ·
        refine ⟨105075147585269705162516885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280200393560719213766711693 105075147585269705162516885)
        ·
          refine ⟨4925397543059517429492979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105075147585269705162516885 4925397543059517429492979)
          ·
            refine ⟨7388096314589276144239469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925397543059517429492979 7388096314589276144239469)
            ·
              refine ⟨2770536117970978554089801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7388096314589276144239469 2770536117970978554089801)
              ·
                refine ⟨2077902088478233915567351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770536117970978554089801 2077902088478233915567351)
                ·
                  refine ⟨3116853132717350873351027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077902088478233915567351 3116853132717350873351027)
                  ·
                    refine ⟨4675279699076026310026541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3116853132717350873351027 4675279699076026310026541)
                    ·
                      refine ⟨1753229887153509866259953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4675279699076026310026541 1753229887153509866259953)
                      ·
                        rfl

theorem cell23_3414403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 1, 1, 3].length) (baseStart_3414403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414403 prefixEnd_3414403 := by exact prefixLift 3414403
  have htrace : WordTrace (prefixWord ++ tailWord_3414403) baseStart_3414403 baseEnd_3414403 := by
    simpa [prefixWord, tailWord_3414403, baseEnd_3414403] using wordTrace_append hprefix tailTrace_3414403
  have hstable : (prefixWord ++ tailWord_3414403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414403).length < 2 ^ (prefixWord ++ tailWord_3414403).sum := by decide
  have hdescent : baseEnd_3414403 < baseStart_3414403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414429 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_3414429 : Nat := 118140960795 + 3414429 * 2 ^ 59
def prefixEnd_3414429 : Nat := 4983230072969 + 3 ^ 40 * 3414429 * 2
def baseEnd_3414429 : Nat := 1753243237650526764534833

theorem tailTrace_3414429 : CollatzResearch.WordTrace tailWord_3414429 prefixEnd_3414429 1753243237650526764534833 := by
  unfold tailWord_3414429
  simp only [CollatzResearch.WordTrace]
  refine ⟨124534456547114345892318341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83022971031409563928212227 124534456547114345892318341)
  ·
    refine ⟨23350210602583939854809689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124534456547114345892318341 23350210602583939854809689)
    ·
      refine ⟨17512657951937954891107267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23350210602583939854809689 17512657951937954891107267)
      ·
        refine ⟨26268986927906932336660901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17512657951937954891107267 26268986927906932336660901)
        ·
          refine ⟨4925435048982549813123919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26268986927906932336660901 4925435048982549813123919)
          ·
            refine ⟨7388152573473824719685879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925435048982549813123919 7388152573473824719685879)
            ·
              refine ⟨11082228860210737079528819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388152573473824719685879 11082228860210737079528819)
              ·
                refine ⟨16623343290316105619293229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11082228860210737079528819 16623343290316105619293229)
                ·
                  refine ⟨6233753733868539607234961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16623343290316105619293229 6233753733868539607234961)
                  ·
                    refine ⟨4675315300401404705426221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6233753733868539607234961 4675315300401404705426221)
                    ·
                      refine ⟨1753243237650526764534833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4675315300401404705426221 1753243237650526764534833)
                      ·
                        rfl

theorem cell23_3414429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_3414429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414429 prefixEnd_3414429 := by exact prefixLift 3414429
  have htrace : WordTrace (prefixWord ++ tailWord_3414429) baseStart_3414429 baseEnd_3414429 := by
    simpa [prefixWord, tailWord_3414429, baseEnd_3414429] using wordTrace_append hprefix tailTrace_3414429
  have hstable : (prefixWord ++ tailWord_3414429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414429).length < 2 ^ (prefixWord ++ tailWord_3414429).sum := by decide
  have hdescent : baseEnd_3414429 < baseStart_3414429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414460 : List Nat := [2, 2, 2, 4, 1, 1, 4, 2, 1, 2, 2]
def baseStart_3414460 : Nat := 118140960795 + 3414460 * 2 ^ 59
def prefixEnd_3414460 : Nat := 4983230072969 + 3 ^ 40 * 3414460 * 2
def baseEnd_3414460 : Nat := 1753259155550816143247191

theorem tailTrace_3414460 : CollatzResearch.WordTrace tailWord_3414460 prefixEnd_3414460 1753259155550816143247191 := by
  unfold tailWord_3414460
  simp only [CollatzResearch.WordTrace]
  refine ⟨62267793605001019093348417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83023724806668025457797889 62267793605001019093348417)
  ·
    refine ⟨46700845203750764320011313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62267793605001019093348417 46700845203750764320011313)
    ·
      refine ⟨35025633902813073240008485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46700845203750764320011313 35025633902813073240008485)
      ·
        refine ⟨6567306356777451232501591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35025633902813073240008485 6567306356777451232501591)
        ·
          refine ⟨9850959535166176848752387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6567306356777451232501591 9850959535166176848752387)
          ·
            refine ⟨14776439302749265273128581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9850959535166176848752387 14776439302749265273128581)
            ·
              refine ⟨2770582369265487238711609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14776439302749265273128581 2770582369265487238711609)
              ·
                refine ⟨2077936776949115429033707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770582369265487238711609 2077936776949115429033707)
                ·
                  refine ⟨3116905165423673143550561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077936776949115429033707 3116905165423673143550561)
                  ·
                    refine ⟨2337678874067754857662921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3116905165423673143550561 2337678874067754857662921)
                    ·
                      refine ⟨1753259155550816143247191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2337678874067754857662921 1753259155550816143247191)
                      ·
                        rfl

theorem cell23_3414460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_3414460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414460 prefixEnd_3414460 := by exact prefixLift 3414460
  have htrace : WordTrace (prefixWord ++ tailWord_3414460) baseStart_3414460 baseEnd_3414460 := by
    simpa [prefixWord, tailWord_3414460, baseEnd_3414460] using wordTrace_append hprefix tailTrace_3414460
  have hstable : (prefixWord ++ tailWord_3414460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414460).length < 2 ^ (prefixWord ++ tailWord_3414460).sum := by decide
  have hdescent : baseEnd_3414460 < baseStart_3414460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414486 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_3414486 : Nat := 118140960795 + 3414486 * 2 ^ 59
def prefixEnd_3414486 : Nat := 4983230072969 + 3 ^ 40 * 3414486 * 2
def baseEnd_3414486 : Nat := 1753272506047833041522071

theorem tailTrace_3414486 : CollatzResearch.WordTrace tailWord_3414486 prefixEnd_3414486 1753272506047833041522071 := by
  unfold tailWord_3414486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7783533469244240289196457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83024357005271896418095541 7783533469244240289196457)
  ·
    refine ⟨5837650101933180216897343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7783533469244240289196457 5837650101933180216897343)
    ·
      refine ⟨8756475152899770325346015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5837650101933180216897343 8756475152899770325346015)
      ·
        refine ⟨13134712729349655488019023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8756475152899770325346015 13134712729349655488019023)
        ·
          refine ⟨19702069094024483232028535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13134712729349655488019023 19702069094024483232028535)
          ·
            refine ⟨29553103641036724848042803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19702069094024483232028535 29553103641036724848042803)
            ·
              refine ⟨44329655461555087272064205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29553103641036724848042803 44329655461555087272064205)
              ·
                refine ⟨16623620798083157727024077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44329655461555087272064205 16623620798083157727024077)
                ·
                  refine ⟨6233857799281184147634029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16623620798083157727024077 6233857799281184147634029)
                  ·
                    refine ⟨2337696674730444055362761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6233857799281184147634029 2337696674730444055362761)
                    ·
                      refine ⟨1753272506047833041522071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2337696674730444055362761 1753272506047833041522071)
                      ·
                        rfl

theorem cell23_3414486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_3414486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414486 prefixEnd_3414486 := by exact prefixLift 3414486
  have htrace : WordTrace (prefixWord ++ tailWord_3414486) baseStart_3414486 baseEnd_3414486 := by
    simpa [prefixWord, tailWord_3414486, baseEnd_3414486] using wordTrace_append hprefix tailTrace_3414486
  have hstable : (prefixWord ++ tailWord_3414486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414486).length < 2 ^ (prefixWord ++ tailWord_3414486).sum := by decide
  have hdescent : baseEnd_3414486 < baseStart_3414486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414545 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_3414545 : Nat := 118140960795 + 3414545 * 2 ^ 59
def prefixEnd_3414545 : Nat := 4983230072969 + 3 ^ 40 * 3414545 * 2
def baseEnd_3414545 : Nat := 1753302801406448310684299

theorem tailTrace_3414545 : CollatzResearch.WordTrace tailWord_3414545 prefixEnd_3414545 1753302801406448310684299 := by
  unfold tailWord_3414545
  simp only [CollatzResearch.WordTrace]
  refine ⟨124538687414694097703541089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83025791609796065135694059 124538687414694097703541089)
  ·
    refine ⟨93404015561020573277655817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124538687414694097703541089 93404015561020573277655817)
    ·
      refine ⟨70053011670765429958241863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93404015561020573277655817 70053011670765429958241863)
      ·
        refine ⟨105079517506148144937362795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70053011670765429958241863 105079517506148144937362795)
        ·
          refine ⟨157619276259222217406044193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105079517506148144937362795 157619276259222217406044193)
          ·
            refine ⟨118214457194416663054533145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157619276259222217406044193 118214457194416663054533145)
            ·
              refine ⟨88660842895812497290899859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118214457194416663054533145 88660842895812497290899859)
              ·
                refine ⟨132991264343718745936349789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88660842895812497290899859 132991264343718745936349789)
                ·
                  refine ⟨49871724128894529726131171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132991264343718745936349789 49871724128894529726131171)
                  ·
                    refine ⟨74807586193341794589196757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49871724128894529726131171 74807586193341794589196757)
                    ·
                      refine ⟨1753302801406448310684299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74807586193341794589196757 1753302801406448310684299)
                      ·
                        rfl

theorem cell23_3414545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_3414545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414545 prefixEnd_3414545 := by exact prefixLift 3414545
  have htrace : WordTrace (prefixWord ++ tailWord_3414545) baseStart_3414545 baseEnd_3414545 := by
    simpa [prefixWord, tailWord_3414545, baseEnd_3414545] using wordTrace_append hprefix tailTrace_3414545
  have hstable : (prefixWord ++ tailWord_3414545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414545).length < 2 ^ (prefixWord ++ tailWord_3414545).sum := by decide
  have hdescent : baseEnd_3414545 < baseStart_3414545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414552 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 1, 7]
def baseStart_3414552 : Nat := 118140960795 + 3414552 * 2 ^ 59
def prefixEnd_3414552 : Nat := 4983230072969 + 3 ^ 40 * 3414552 * 2
def baseEnd_3414552 : Nat := 584435465257009927765589

theorem tailTrace_3414552 : CollatzResearch.WordTrace tailWord_3414552 prefixEnd_3414552 584435465257009927765589 := by
  unfold tailWord_3414552
  simp only [CollatzResearch.WordTrace]
  refine ⟨62269471362834368949522955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83025961817112491932697273 62269471362834368949522955)
  ·
    refine ⟨93404207044251553424284433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62269471362834368949522955 93404207044251553424284433)
    ·
      refine ⟨70053155283188665068213325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93404207044251553424284433 70053155283188665068213325)
      ·
        refine ⟨26269933231195749400579997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70053155283188665068213325 26269933231195749400579997)
        ·
          refine ⟨9851224961698406025217499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26269933231195749400579997 9851224961698406025217499)
          ·
            refine ⟨14776837442547609037826249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9851224961698406025217499 14776837442547609037826249)
            ·
              refine ⟨11082628081910706778369687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14776837442547609037826249 11082628081910706778369687)
              ·
                refine ⟨16623942122866060167554531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11082628081910706778369687 16623942122866060167554531)
                ·
                  refine ⟨24935913184299090251331797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16623942122866060167554531 24935913184299090251331797)
                  ·
                    refine ⟨584435465257009927765589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24935913184299090251331797 584435465257009927765589)
                    ·
                      rfl

theorem cell23_3414552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_3414552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414552 prefixEnd_3414552 := by exact prefixLift 3414552
  have htrace : WordTrace (prefixWord ++ tailWord_3414552) baseStart_3414552 baseEnd_3414552 := by
    simpa [prefixWord, tailWord_3414552, baseEnd_3414552] using wordTrace_append hprefix tailTrace_3414552
  have hstable : (prefixWord ++ tailWord_3414552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414552).length < 2 ^ (prefixWord ++ tailWord_3414552).sum := by decide
  have hdescent : baseEnd_3414552 < baseStart_3414552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414556 : List Nat := [2, 2, 3, 1, 2, 4, 1, 3, 5]
def baseStart_3414556 : Nat := 118140960795 + 3414556 * 2 ^ 59
def prefixEnd_3414556 : Nat := 4983230072969 + 3 ^ 40 * 3414556 * 2
def baseEnd_3414556 : Nat := 194812049965960863071861

theorem tailTrace_3414556 : CollatzResearch.WordTrace tailWord_3414556 prefixEnd_3414556 194812049965960863071861 := by
  unfold tailWord_3414556
  simp only [CollatzResearch.WordTrace]
  refine ⟨62269544308827123291095761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83026059078436164388127681 62269544308827123291095761)
  ·
    refine ⟨46702158231620342468321821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62269544308827123291095761 46702158231620342468321821)
    ·
      refine ⟨17513309336857628425620683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46702158231620342468321821 17513309336857628425620683)
      ·
        refine ⟨26269964005286442638431025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17513309336857628425620683 26269964005286442638431025)
        ·
          refine ⟨19702473003964831978823269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26269964005286442638431025 19702473003964831978823269)
          ·
            refine ⟨3694213688243405996029363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19702473003964831978823269 3694213688243405996029363)
            ·
              refine ⟨5541320532365108994044045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694213688243405996029363 5541320532365108994044045)
              ·
                refine ⟨2077995199636915872766517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5541320532365108994044045 2077995199636915872766517)
                ·
                  refine ⟨194812049965960863071861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2077995199636915872766517 194812049965960863071861)
                  ·
                    rfl

theorem cell23_3414556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_3414556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414556 prefixEnd_3414556 := by exact prefixLift 3414556
  have htrace : WordTrace (prefixWord ++ tailWord_3414556) baseStart_3414556 baseEnd_3414556 := by
    simpa [prefixWord, tailWord_3414556, baseEnd_3414556] using wordTrace_append hprefix tailTrace_3414556
  have hstable : (prefixWord ++ tailWord_3414556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414556).length < 2 ^ (prefixWord ++ tailWord_3414556).sum := by decide
  have hdescent : baseEnd_3414556 < baseStart_3414556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414562 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_3414562 : Nat := 118140960795 + 3414562 * 2 ^ 59
def prefixEnd_3414562 : Nat := 4983230072969 + 3 ^ 40 * 3414562 * 2
def baseEnd_3414562 : Nat := 1753311530577574744171721

theorem tailTrace_3414562 : CollatzResearch.WordTrace tailWord_3414562 prefixEnd_3414562 1753311530577574744171721 := by
  unfold tailWord_3414562
  simp only [CollatzResearch.WordTrace]
  refine ⟨31134826863908127401727485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83026204970421673071273293 31134826863908127401727485)
  ·
    refine ⟨11675560073965547775647807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31134826863908127401727485 11675560073965547775647807)
    ·
      refine ⟨17513340110948321663471711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11675560073965547775647807 17513340110948321663471711)
      ·
        refine ⟨26270010166422482495207567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17513340110948321663471711 26270010166422482495207567)
        ·
          refine ⟨39405015249633723742811351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26270010166422482495207567 39405015249633723742811351)
          ·
            refine ⟨59107522874450585614217027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39405015249633723742811351 59107522874450585614217027)
            ·
              refine ⟨88661284311675878421325541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59107522874450585614217027 88661284311675878421325541)
              ·
                refine ⟨16623990808439227203998539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88661284311675878421325541 16623990808439227203998539)
                ·
                  refine ⟨24935986212658840805997809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16623990808439227203998539 24935986212658840805997809)
                  ·
                    refine ⟨18701989659494130604498357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24935986212658840805997809 18701989659494130604498357)
                    ·
                      refine ⟨1753311530577574744171721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18701989659494130604498357 1753311530577574744171721)
                      ·
                        rfl

theorem cell23_3414562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_3414562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414562 prefixEnd_3414562 := by exact prefixLift 3414562
  have htrace : WordTrace (prefixWord ++ tailWord_3414562) baseStart_3414562 baseEnd_3414562 := by
    simpa [prefixWord, tailWord_3414562, baseEnd_3414562] using wordTrace_append hprefix tailTrace_3414562
  have hstable : (prefixWord ++ tailWord_3414562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414562).length < 2 ^ (prefixWord ++ tailWord_3414562).sum := by decide
  have hdescent : baseEnd_3414562 < baseStart_3414562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414592 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 3]
def baseStart_3414592 : Nat := 118140960795 + 3414592 * 2 ^ 59
def prefixEnd_3414592 : Nat := 4983230072969 + 3 ^ 40 * 3414592 * 2
def baseEnd_3414592 : Nat := 1753326934997209626796583

theorem tailTrace_3414592 : CollatzResearch.WordTrace tailWord_3414592 prefixEnd_3414592 1753326934997209626796583 := by
  unfold tailWord_3414592
  simp only [CollatzResearch.WordTrace]
  refine ⟨62270200822761912365251015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83026934430349216487001353 62270200822761912365251015)
  ·
    refine ⟨93405301234142868547876523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62270200822761912365251015 93405301234142868547876523)
    ·
      refine ⟨140107951851214302821814785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93405301234142868547876523 140107951851214302821814785)
      ·
        refine ⟨105080963888410727116361089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140107951851214302821814785 105080963888410727116361089)
        ·
          refine ⟨78810722916308045337270817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105080963888410727116361089 78810722916308045337270817)
          ·
            refine ⟨59108042187231034002953113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78810722916308045337270817 59108042187231034002953113)
            ·
              refine ⟨44331031640423275502214835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59108042187231034002953113 44331031640423275502214835)
              ·
                refine ⟨66496547460634913253322253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44331031640423275502214835 66496547460634913253322253)
                ·
                  refine ⟨24936205297738092469995845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66496547460634913253322253 24936205297738092469995845)
                  ·
                    refine ⟨4675538493325892338124221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24936205297738092469995845 4675538493325892338124221)
                    ·
                      refine ⟨1753326934997209626796583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4675538493325892338124221 1753326934997209626796583)
                      ·
                        rfl

theorem cell23_3414592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_3414592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414592 prefixEnd_3414592 := by exact prefixLift 3414592
  have htrace : WordTrace (prefixWord ++ tailWord_3414592) baseStart_3414592 baseEnd_3414592 := by
    simpa [prefixWord, tailWord_3414592, baseEnd_3414592] using wordTrace_append hprefix tailTrace_3414592
  have hstable : (prefixWord ++ tailWord_3414592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414592).length < 2 ^ (prefixWord ++ tailWord_3414592).sum := by decide
  have hdescent : baseEnd_3414592 < baseStart_3414592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414609 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 2, 2, 3]
def baseStart_3414609 : Nat := 118140960795 + 3414609 * 2 ^ 59
def prefixEnd_3414609 : Nat := 4983230072969 + 3 ^ 40 * 3414609 * 2
def baseEnd_3414609 : Nat := 1753335664168336060284005

theorem tailTrace_3414609 : CollatzResearch.WordTrace tailWord_3414609 prefixEnd_3414609 1753335664168336060284005 := by
  unfold tailWord_3414609
  simp only [CollatzResearch.WordTrace]
  refine ⟨124541021686462236633870881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83027347790974824422580587 124541021686462236633870881)
  ·
    refine ⟨93405766264846677475403161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124541021686462236633870881 93405766264846677475403161)
    ·
      refine ⟨70054324698635008106552371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93405766264846677475403161 70054324698635008106552371)
      ·
        refine ⟨105081487047952512159828557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70054324698635008106552371 105081487047952512159828557)
        ·
          refine ⟨39405557642982192059935709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105081487047952512159828557 39405557642982192059935709)
          ·
            refine ⟨14777084116118322022475891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39405557642982192059935709 14777084116118322022475891)
            ·
              refine ⟨22165626174177483033713837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14777084116118322022475891 22165626174177483033713837)
              ·
                refine ⟨8312109815316556137642689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22165626174177483033713837 8312109815316556137642689)
                ·
                  refine ⟨6234082361487417103232017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8312109815316556137642689 6234082361487417103232017)
                  ·
                    refine ⟨4675561771115562827424013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6234082361487417103232017 4675561771115562827424013)
                    ·
                      refine ⟨1753335664168336060284005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4675561771115562827424013 1753335664168336060284005)
                      ·
                        rfl

theorem cell23_3414609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_3414609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414609 prefixEnd_3414609 := by exact prefixLift 3414609
  have htrace : WordTrace (prefixWord ++ tailWord_3414609) baseStart_3414609 baseEnd_3414609 := by
    simpa [prefixWord, tailWord_3414609, baseEnd_3414609] using wordTrace_append hprefix tailTrace_3414609
  have hstable : (prefixWord ++ tailWord_3414609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414609).length < 2 ^ (prefixWord ++ tailWord_3414609).sum := by decide
  have hdescent : baseEnd_3414609 < baseStart_3414609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414656 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 3, 1, 3]
def baseStart_3414656 : Nat := 118140960795 + 3414656 * 2 ^ 59
def prefixEnd_3414656 : Nat := 4983230072969 + 3 ^ 40 * 3414656 * 2
def baseEnd_3414656 : Nat := 1753359797759097376396289

theorem tailTrace_3414656 : CollatzResearch.WordTrace tailWord_3414656 prefixEnd_3414656 1753359797759097376396289 := by
  unfold tailWord_3414656
  simp only [CollatzResearch.WordTrace]
  refine ⟨62271367958645981830415911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83028490611527975773887881 62271367958645981830415911)
  ·
    refine ⟨93407051937968972745623867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62271367958645981830415911 93407051937968972745623867)
    ·
      refine ⟨140110577906953459118435801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93407051937968972745623867 140110577906953459118435801)
      ·
        refine ⟨105082933430215094338826851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140110577906953459118435801 105082933430215094338826851)
        ·
          refine ⟨157624400145322641508240277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105082933430215094338826851 157624400145322641508240277)
          ·
            refine ⟨7388643756811998820698763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157624400145322641508240277 7388643756811998820698763)
            ·
              refine ⟨11082965635217998231048145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388643756811998820698763 11082965635217998231048145)
              ·
                refine ⟨8312224226413498673286109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11082965635217998231048145 8312224226413498673286109)
                ·
                  refine ⟨3117084084905062002482291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8312224226413498673286109 3117084084905062002482291)
                  ·
                    refine ⟨4675626127357593003723437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3117084084905062002482291 4675626127357593003723437)
                    ·
                      refine ⟨1753359797759097376396289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4675626127357593003723437 1753359797759097376396289)
                      ·
                        rfl

theorem cell23_3414656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_3414656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414656 prefixEnd_3414656 := by exact prefixLift 3414656
  have htrace : WordTrace (prefixWord ++ tailWord_3414656) baseStart_3414656 baseEnd_3414656 := by
    simpa [prefixWord, tailWord_3414656, baseEnd_3414656] using wordTrace_append hprefix tailTrace_3414656
  have hstable : (prefixWord ++ tailWord_3414656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414656).length < 2 ^ (prefixWord ++ tailWord_3414656).sum := by decide
  have hdescent : baseEnd_3414656 < baseStart_3414656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414710 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_3414710 : Nat := 118140960795 + 3414710 * 2 ^ 59
def prefixEnd_3414710 : Nat := 4983230072969 + 3 ^ 40 * 3414710 * 2
def baseEnd_3414710 : Nat := 584462508571480055040347

theorem tailTrace_3414710 : CollatzResearch.WordTrace tailWord_3414710 prefixEnd_3414710 584462508571480055040347 := by
  unfold tailWord_3414710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7784044091193520680206099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83029803639397553922198389 7784044091193520680206099)
  ·
    refine ⟨11676066136790281020309149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7784044091193520680206099 11676066136790281020309149)
    ·
      refine ⟨4378524801296355382615931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11676066136790281020309149 4378524801296355382615931)
      ·
        refine ⟨6567787201944533073923897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4378524801296355382615931 6567787201944533073923897)
        ·
          refine ⟨4925840401458399805442923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6567787201944533073923897 4925840401458399805442923)
          ·
            refine ⟨7388760602187599708164385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925840401458399805442923 7388760602187599708164385)
            ·
              refine ⟨5541570451640699781123289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7388760602187599708164385 5541570451640699781123289)
              ·
                refine ⟨4156177838730524835842467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5541570451640699781123289 4156177838730524835842467)
                ·
                  refine ⟨6234266758095787253763701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156177838730524835842467 6234266758095787253763701)
                  ·
                    refine ⟨584462508571480055040347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6234266758095787253763701 584462508571480055040347)
                    ·
                      rfl

theorem cell23_3414710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_3414710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414710 prefixEnd_3414710 := by exact prefixLift 3414710
  have htrace : WordTrace (prefixWord ++ tailWord_3414710) baseStart_3414710 baseEnd_3414710 := by
    simpa [prefixWord, tailWord_3414710, baseEnd_3414710] using wordTrace_append hprefix tailTrace_3414710
  have hstable : (prefixWord ++ tailWord_3414710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414710).length < 2 ^ (prefixWord ++ tailWord_3414710).sum := by decide
  have hdescent : baseEnd_3414710 < baseStart_3414710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414719 : List Nat := [1, 1, 2, 2, 2, 4, 4, 7]
def baseStart_3414719 : Nat := 118140960795 + 3414719 * 2 ^ 59
def prefixEnd_3414719 : Nat := 4983230072969 + 3 ^ 40 * 3414719 * 2
def baseEnd_3414719 : Nat := 64940449890382615922537

theorem tailTrace_3414719 : CollatzResearch.WordTrace tailWord_3414719 prefixEnd_3414719 64940449890382615922537 := by
  unfold tailWord_3414719
  simp only [CollatzResearch.WordTrace]
  refine ⟨124545033716063725420375211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83030022477375816946916807 124545033716063725420375211)
  ·
    refine ⟨186817550574095588130562817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124545033716063725420375211 186817550574095588130562817)
    ·
      refine ⟨140113162930571691097922113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186817550574095588130562817 140113162930571691097922113)
      ·
        refine ⟨105084872197928768323441585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140113162930571691097922113 105084872197928768323441585)
        ·
          refine ⟨78813654148446576242581189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105084872197928768323441585 78813654148446576242581189)
          ·
            refine ⟨14777560152833733045483973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78813654148446576242581189 14777560152833733045483973)
            ·
              refine ⟨2770792528656324946028245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14777560152833733045483973 2770792528656324946028245)
              ·
                refine ⟨64940449890382615922537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2770792528656324946028245 64940449890382615922537)
                ·
                  rfl

theorem cell23_3414719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 7].length) (baseStart_3414719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414719 prefixEnd_3414719 := by exact prefixLift 3414719
  have htrace : WordTrace (prefixWord ++ tailWord_3414719) baseStart_3414719 baseEnd_3414719 := by
    simpa [prefixWord, tailWord_3414719, baseEnd_3414719] using wordTrace_append hprefix tailTrace_3414719
  have hstable : (prefixWord ++ tailWord_3414719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414719).length < 2 ^ (prefixWord ++ tailWord_3414719).sum := by decide
  have hdescent : baseEnd_3414719 < baseStart_3414719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414746 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3]
def baseStart_3414746 : Nat := 118140960795 + 3414746 * 2 ^ 59
def prefixEnd_3414746 : Nat := 4983230072969 + 3 ^ 40 * 3414746 * 2
def baseEnd_3414746 : Nat := 1753406011018002024270875

theorem tailTrace_3414746 : CollatzResearch.WordTrace tailWord_3414746 prefixEnd_3414746 1753406011018002024270875 := by
  unfold tailWord_3414746
  simp only [CollatzResearch.WordTrace]
  refine ⟨31136504621741477257902023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83030678991310606021072061 31136504621741477257902023)
  ·
    refine ⟨46704756932612215886853035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31136504621741477257902023 46704756932612215886853035)
    ·
      refine ⟨70057135398918323830279553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46704756932612215886853035 70057135398918323830279553)
      ·
        refine ⟨52542851549188742872709665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70057135398918323830279553 52542851549188742872709665)
        ·
          refine ⟨39407138661891557154532249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52542851549188742872709665 39407138661891557154532249)
          ·
            refine ⟨29555353996418667865899187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39407138661891557154532249 29555353996418667865899187)
            ·
              refine ⟨44333030994628001798848781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29555353996418667865899187 44333030994628001798848781)
              ·
                refine ⟨16624886622985500674568293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44333030994628001798848781 16624886622985500674568293)
                ·
                  refine ⟨3117166241809781376481555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16624886622985500674568293 3117166241809781376481555)
                  ·
                    refine ⟨4675749362714672064722333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3117166241809781376481555 4675749362714672064722333)
                    ·
                      refine ⟨1753406011018002024270875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4675749362714672064722333 1753406011018002024270875)
                      ·
                        rfl

theorem cell23_3414746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_3414746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414746 prefixEnd_3414746 := by exact prefixLift 3414746
  have htrace : WordTrace (prefixWord ++ tailWord_3414746) baseStart_3414746 baseEnd_3414746 := by
    simpa [prefixWord, tailWord_3414746, baseEnd_3414746] using wordTrace_append hprefix tailTrace_3414746
  have hstable : (prefixWord ++ tailWord_3414746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414746).length < 2 ^ (prefixWord ++ tailWord_3414746).sum := by decide
  have hdescent : baseEnd_3414746 < baseStart_3414746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414789 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 4, 4, 3]
def baseStart_3414789 : Nat := 118140960795 + 3414789 * 2 ^ 59
def prefixEnd_3414789 : Nat := 4983230072969 + 3 ^ 40 * 3414789 * 2
def baseEnd_3414789 : Nat := 1753428090686145356033177

theorem tailTrace_3414789 : CollatzResearch.WordTrace tailWord_3414789 prefixEnd_3414789 1753428090686145356033177 := by
  unfold tailWord_3414789
  simp only [CollatzResearch.WordTrace]
  refine ⟨124547586825810127375423421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83031724550540084916948947 124547586825810127375423421)
  ·
    refine ⟨46705345059678797765783783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124547586825810127375423421 46705345059678797765783783)
    ·
      refine ⟨70058017589518196648675675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46705345059678797765783783 70058017589518196648675675)
      ·
        refine ⟨105087026384277294973013513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70058017589518196648675675 105087026384277294973013513)
        ·
          refine ⟨78815269788207971229760135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105087026384277294973013513 78815269788207971229760135)
          ·
            refine ⟨118222904682311956844640203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78815269788207971229760135 118222904682311956844640203)
            ·
              refine ⟨177334357023467935266960305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118222904682311956844640203 177334357023467935266960305)
              ·
                refine ⟨133000767767600951450220229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177334357023467935266960305 133000767767600951450220229)
                ·
                  refine ⟨24937643956425178396916293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133000767767600951450220229 24937643956425178396916293)
                  ·
                    refine ⟨4675808241829720949421805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24937643956425178396916293 4675808241829720949421805)
                    ·
                      refine ⟨1753428090686145356033177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4675808241829720949421805 1753428090686145356033177)
                      ·
                        rfl

theorem cell23_3414789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_3414789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414789 prefixEnd_3414789 := by exact prefixLift 3414789
  have htrace : WordTrace (prefixWord ++ tailWord_3414789) baseStart_3414789 baseEnd_3414789 := by
    simpa [prefixWord, tailWord_3414789, baseEnd_3414789] using wordTrace_append hprefix tailTrace_3414789
  have hstable : (prefixWord ++ tailWord_3414789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414789).length < 2 ^ (prefixWord ++ tailWord_3414789).sum := by decide
  have hdescent : baseEnd_3414789 < baseStart_3414789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414799 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 4]
def baseStart_3414799 : Nat := 118140960795 + 3414799 * 2 ^ 59
def prefixEnd_3414799 : Nat := 4983230072969 + 3 ^ 40 * 3414799 * 2
def baseEnd_3414799 : Nat := 1753433225492690316908131

theorem tailTrace_3414799 : CollatzResearch.WordTrace tailWord_3414799 prefixEnd_3414799 1753433225492690316908131 := by
  unfold tailWord_3414799
  simp only [CollatzResearch.WordTrace]
  refine ⟨124547951555773899083287451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83031967703849266055524967 124547951555773899083287451)
  ·
    refine ⟨186821927333660848624931177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124547951555773899083287451 186821927333660848624931177)
    ·
      refine ⟨140116445500245636468698383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186821927333660848624931177 140116445500245636468698383)
      ·
        refine ⟨210174668250368454703047575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140116445500245636468698383 210174668250368454703047575)
        ·
          refine ⟨315262002375552682054571363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210174668250368454703047575 315262002375552682054571363)
          ·
            refine ⟨472893003563329023081857045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315262002375552682054571363 472893003563329023081857045)
            ·
              refine ⟨22166859542031047956962049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 472893003563329023081857045 22166859542031047956962049)
              ·
                refine ⟨16625144656523285967721537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22166859542031047956962049 16625144656523285967721537)
                ·
                  refine ⟨12468858492392464475791153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16625144656523285967721537 12468858492392464475791153)
                  ·
                    refine ⟨9351643869294348356843365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12468858492392464475791153 9351643869294348356843365)
                    ·
                      refine ⟨1753433225492690316908131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9351643869294348356843365 1753433225492690316908131)
                      ·
                        rfl

theorem cell23_3414799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_3414799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414799 prefixEnd_3414799 := by exact prefixLift 3414799
  have htrace : WordTrace (prefixWord ++ tailWord_3414799) baseStart_3414799 baseEnd_3414799 := by
    simpa [prefixWord, tailWord_3414799, baseEnd_3414799] using wordTrace_append hprefix tailTrace_3414799
  have hstable : (prefixWord ++ tailWord_3414799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414799).length < 2 ^ (prefixWord ++ tailWord_3414799).sum := by decide
  have hdescent : baseEnd_3414799 < baseStart_3414799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414813 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_3414813 : Nat := 118140960795 + 3414813 * 2 ^ 59
def prefixEnd_3414813 : Nat := 4983230072969 + 3 ^ 40 * 3414813 * 2
def baseEnd_3414813 : Nat := 584480138073951087377689

theorem tailTrace_3414813 : CollatzResearch.WordTrace tailWord_3414813 prefixEnd_3414813 584480138073951087377689 := by
  unfold tailWord_3414813
  simp only [CollatzResearch.WordTrace]
  refine ⟨124548462177723179474297093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83032308118482119649531395 124548462177723179474297093)
  ·
    refine ⟨23352836658323096151430705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124548462177723179474297093 23352836658323096151430705)
    ·
      refine ⟨17514627493742322113573029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23352836658323096151430705 17514627493742322113573029)
      ·
        refine ⟨3283992655076685396294943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17514627493742322113573029 3283992655076685396294943)
        ·
          refine ⟨4925988982615028094442415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283992655076685396294943 4925988982615028094442415)
          ·
            refine ⟨7388983473922542141663623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925988982615028094442415 7388983473922542141663623)
            ·
              refine ⟨11083475210883813212495435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388983473922542141663623 11083475210883813212495435)
              ·
                refine ⟨16625212816325719818743153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11083475210883813212495435 16625212816325719818743153)
                ·
                  refine ⟨12468909612244289864057365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16625212816325719818743153 12468909612244289864057365)
                  ·
                    refine ⟨584480138073951087377689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12468909612244289864057365 584480138073951087377689)
                    ·
                      rfl

theorem cell23_3414813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_3414813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414813 prefixEnd_3414813 := by exact prefixLift 3414813
  have htrace : WordTrace (prefixWord ++ tailWord_3414813) baseStart_3414813 baseEnd_3414813 := by
    simpa [prefixWord, tailWord_3414813, baseEnd_3414813] using wordTrace_append hprefix tailTrace_3414813
  have hstable : (prefixWord ++ tailWord_3414813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414813).length < 2 ^ (prefixWord ++ tailWord_3414813).sum := by decide
  have hdescent : baseEnd_3414813 < baseStart_3414813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414816 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 4]
def baseStart_3414816 : Nat := 118140960795 + 3414816 * 2 ^ 59
def prefixEnd_3414816 : Nat := 4983230072969 + 3 ^ 40 * 3414816 * 2
def baseEnd_3414816 : Nat := 1753441954663816750395553

theorem tailTrace_3414816 : CollatzResearch.WordTrace tailWord_3414816 prefixEnd_3414816 1753441954663816750395553 := by
  unfold tailWord_3414816
  simp only [CollatzResearch.WordTrace]
  refine ⟨62274285798356155493328151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83032381064474873991104201 62274285798356155493328151)
  ·
    refine ⟨93411428697534233239992227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62274285798356155493328151 93411428697534233239992227)
    ·
      refine ⟨140117143046301349859988341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93411428697534233239992227 140117143046301349859988341)
      ·
        refine ⟨13135982160590751549373907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140117143046301349859988341 13135982160590751549373907)
        ·
          refine ⟨19703973240886127324060861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13135982160590751549373907 19703973240886127324060861)
          ·
            refine ⟨7388989965332297746522823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19703973240886127324060861 7388989965332297746522823)
            ·
              refine ⟨11083484947998446619784235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388989965332297746522823 11083484947998446619784235)
              ·
                refine ⟨16625227421997669929676353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11083484947998446619784235 16625227421997669929676353)
                ·
                  refine ⟨12468920566498252447257265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16625227421997669929676353 12468920566498252447257265)
                  ·
                    refine ⟨9351690424873689335442949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12468920566498252447257265 9351690424873689335442949)
                    ·
                      refine ⟨1753441954663816750395553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9351690424873689335442949 1753441954663816750395553)
                      ·
                        rfl

theorem cell23_3414816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_3414816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414816 prefixEnd_3414816 := by exact prefixLift 3414816
  have htrace : WordTrace (prefixWord ++ tailWord_3414816) baseStart_3414816 baseEnd_3414816 := by
    simpa [prefixWord, tailWord_3414816, baseEnd_3414816] using wordTrace_append hprefix tailTrace_3414816
  have hstable : (prefixWord ++ tailWord_3414816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414816).length < 2 ^ (prefixWord ++ tailWord_3414816).sum := by decide
  have hdescent : baseEnd_3414816 < baseStart_3414816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414820 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 1, 4, 2]
def baseStart_3414820 : Nat := 118140960795 + 3414820 * 2 ^ 59
def prefixEnd_3414820 : Nat := 4983230072969 + 3 ^ 40 * 3414820 * 2
def baseEnd_3414820 : Nat := 1753444008586434734745535

theorem tailTrace_3414820 : CollatzResearch.WordTrace tailWord_3414820 prefixEnd_3414820 1753444008586434734745535 := by
  unfold tailWord_3414820
  simp only [CollatzResearch.WordTrace]
  refine ⟨62274358744348909834900957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83032478325798546446534609 62274358744348909834900957)
  ·
    refine ⟨23352884529130841188087859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62274358744348909834900957 23352884529130841188087859)
    ·
      refine ⟨35029326793696261782131789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23352884529130841188087859 35029326793696261782131789)
      ·
        refine ⟨13135997547636098168299421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35029326793696261782131789 13135997547636098168299421)
        ·
          refine ⟨4925999080363536813112283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13135997547636098168299421 4925999080363536813112283)
          ·
            refine ⟨7388998620545305219668425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925999080363536813112283 7388998620545305219668425)
            ·
              refine ⟨5541748965408978914751319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7388998620545305219668425 5541748965408978914751319)
              ·
                refine ⟨8312623448113468372126979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5541748965408978914751319 8312623448113468372126979)
                ·
                  refine ⟨12468935172170202558190469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8312623448113468372126979 12468935172170202558190469)
                  ·
                    refine ⟨2337925344781912979660713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12468935172170202558190469 2337925344781912979660713)
                    ·
                      refine ⟨1753444008586434734745535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2337925344781912979660713 1753444008586434734745535)
                      ·
                        rfl

theorem cell23_3414820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_3414820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414820 prefixEnd_3414820 := by exact prefixLift 3414820
  have htrace : WordTrace (prefixWord ++ tailWord_3414820) baseStart_3414820 baseEnd_3414820 := by
    simpa [prefixWord, tailWord_3414820, baseEnd_3414820] using wordTrace_append hprefix tailTrace_3414820
  have hstable : (prefixWord ++ tailWord_3414820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414820).length < 2 ^ (prefixWord ++ tailWord_3414820).sum := by decide
  have hdescent : baseEnd_3414820 < baseStart_3414820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414839 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 1, 7]
def baseStart_3414839 : Nat := 118140960795 + 3414839 * 2 ^ 59
def prefixEnd_3414839 : Nat := 4983230072969 + 3 ^ 40 * 3414839 * 2
def baseEnd_3414839 : Nat := 584484588239623386802649

theorem tailTrace_3414839 : CollatzResearch.WordTrace tailWord_3414839 prefixEnd_3414839 584484588239623386802649 := by
  unfold tailWord_3414839
  simp only [CollatzResearch.WordTrace]
  refine ⟨124549410475628985914743571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83032940317085990609829047 124549410475628985914743571)
  ·
    refine ⟨186824115713443478872115357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124549410475628985914743571 186824115713443478872115357)
    ·
      refine ⟨70059043392541304577043259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186824115713443478872115357 70059043392541304577043259)
      ·
        refine ⟨105088565088811956865564889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70059043392541304577043259 105088565088811956865564889)
        ·
          refine ⟨78816423816608967649173667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105088565088811956865564889 78816423816608967649173667)
          ·
            refine ⟨118224635724913451473760501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78816423816608967649173667 118224635724913451473760501)
            ·
              refine ⟨11083559599210636075665047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118224635724913451473760501 11083559599210636075665047)
              ·
                refine ⟨16625339398815954113497571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11083559599210636075665047 16625339398815954113497571)
                ·
                  refine ⟨24938009098223931170246357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16625339398815954113497571 24938009098223931170246357)
                  ·
                    refine ⟨584484588239623386802649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24938009098223931170246357 584484588239623386802649)
                    ·
                      rfl

theorem cell23_3414839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_3414839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414839 prefixEnd_3414839 := by exact prefixLift 3414839
  have htrace : WordTrace (prefixWord ++ tailWord_3414839) baseStart_3414839 baseEnd_3414839 := by
    simpa [prefixWord, tailWord_3414839, baseEnd_3414839] using wordTrace_append hprefix tailTrace_3414839
  have hstable : (prefixWord ++ tailWord_3414839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414839).length < 2 ^ (prefixWord ++ tailWord_3414839).sum := by decide
  have hdescent : baseEnd_3414839 < baseStart_3414839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414854 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_3414854 : Nat := 118140960795 + 3414854 * 2 ^ 59
def prefixEnd_3414854 : Nat := 4983230072969 + 3 ^ 40 * 3414854 * 2
def baseEnd_3414854 : Nat := 1753461466928687601720379

theorem tailTrace_3414854 : CollatzResearch.WordTrace tailWord_3414854 prefixEnd_3414854 1753461466928687601720379 := by
  unfold tailWord_3414854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3892186174080457608641863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83033305047049762317693077 3892186174080457608641863)
  ·
    refine ⟨5838279261120686412962795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3892186174080457608641863 5838279261120686412962795)
    ·
      refine ⟨8757418891681029619444193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5838279261120686412962795 8757418891681029619444193)
      ·
        refine ⟨6568064168760772214583145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8757418891681029619444193 6568064168760772214583145)
        ·
          refine ⟨4926048126570579160937359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6568064168760772214583145 4926048126570579160937359)
          ·
            refine ⟨7389072189855868741406039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926048126570579160937359 7389072189855868741406039)
            ·
              refine ⟨11083608284783803112109059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7389072189855868741406039 11083608284783803112109059)
              ·
                refine ⟨16625412427175704668163589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11083608284783803112109059 16625412427175704668163589)
                ·
                  refine ⟨3117264830095444625280673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16625412427175704668163589 3117264830095444625280673)
                  ·
                    refine ⟨2337948622571583468960505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3117264830095444625280673 2337948622571583468960505)
                    ·
                      refine ⟨1753461466928687601720379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2337948622571583468960505 1753461466928687601720379)
                      ·
                        rfl

theorem cell23_3414854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_3414854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414854 prefixEnd_3414854 := by exact prefixLift 3414854
  have htrace : WordTrace (prefixWord ++ tailWord_3414854) baseStart_3414854 baseEnd_3414854 := by
    simpa [prefixWord, tailWord_3414854, baseEnd_3414854] using wordTrace_append hprefix tailTrace_3414854
  have hstable : (prefixWord ++ tailWord_3414854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414854).length < 2 ^ (prefixWord ++ tailWord_3414854).sum := by decide
  have hdescent : baseEnd_3414854 < baseStart_3414854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414896 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 3]
def baseStart_3414896 : Nat := 118140960795 + 3414896 * 2 ^ 59
def prefixEnd_3414896 : Nat := 4983230072969 + 3 ^ 40 * 3414896 * 2
def baseEnd_3414896 : Nat := 1753483033116176437395185

theorem tailTrace_3414896 : CollatzResearch.WordTrace tailWord_3414896 prefixEnd_3414896 1753483033116176437395185 := by
  unfold tailWord_3414896
  simp only [CollatzResearch.WordTrace]
  refine ⟨62275744718211242324784271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83034326290948323099712361 62275744718211242324784271)
  ·
    refine ⟨93413617077316863487176407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62275744718211242324784271 93413617077316863487176407)
    ·
      refine ⟨140120425615975295230764611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93413617077316863487176407 140120425615975295230764611)
      ·
        refine ⟨210180638423962942846146917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140120425615975295230764611 210180638423962942846146917)
        ·
          refine ⟨39408869704493051783652547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210180638423962942846146917 39408869704493051783652547)
          ·
            refine ⟨59113304556739577675478821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39408869704493051783652547 59113304556739577675478821)
            ·
              refine ⟨11083744604388670814152279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59113304556739577675478821 11083744604388670814152279)
              ·
                refine ⟨16625616906583006221228419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11083744604388670814152279 16625616906583006221228419)
                ·
                  refine ⟨24938425359874509331842629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16625616906583006221228419 24938425359874509331842629)
                  ·
                    refine ⟨4675954754976470499720493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24938425359874509331842629 4675954754976470499720493)
                    ·
                      refine ⟨1753483033116176437395185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4675954754976470499720493 1753483033116176437395185)
                      ·
                        rfl

theorem cell23_3414896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 3].length) (baseStart_3414896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414896 prefixEnd_3414896 := by exact prefixLift 3414896
  have htrace : WordTrace (prefixWord ++ tailWord_3414896) baseStart_3414896 baseEnd_3414896 := by
    simpa [prefixWord, tailWord_3414896, baseEnd_3414896] using wordTrace_append hprefix tailTrace_3414896
  have hstable : (prefixWord ++ tailWord_3414896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414896).length < 2 ^ (prefixWord ++ tailWord_3414896).sum := by decide
  have hdescent : baseEnd_3414896 < baseStart_3414896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414899 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 8]
def baseStart_3414899 : Nat := 118140960795 + 3414899 * 2 ^ 59
def prefixEnd_3414899 : Nat := 4983230072969 + 3 ^ 40 * 3414899 * 2
def baseEnd_3414899 : Nat := 194831619284237769517519

theorem tailTrace_3414899 : CollatzResearch.WordTrace tailWord_3414899 prefixEnd_3414899 194831619284237769517519 := by
  unfold tailWord_3414899
  simp only [CollatzResearch.WordTrace]
  refine ⟨124551598855411616161927751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83034399236941077441285167 124551598855411616161927751)
  ·
    refine ⟨186827398283117424242891627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124551598855411616161927751 186827398283117424242891627)
    ·
      refine ⟨280241097424676136364337441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186827398283117424242891627 280241097424676136364337441)
      ·
        refine ⟨210180823068507102273253081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280241097424676136364337441 210180823068507102273253081)
        ·
          refine ⟨157635617301380326704939811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210180823068507102273253081 157635617301380326704939811)
          ·
            refine ⟨236453425952070490057409717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157635617301380326704939811 236453425952070490057409717)
            ·
              refine ⟨22167508683006608442882161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236453425952070490057409717 22167508683006608442882161)
              ·
                refine ⟨16625631512254956332161621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22167508683006608442882161 16625631512254956332161621)
                ·
                  refine ⟨194831619284237769517519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16625631512254956332161621 194831619284237769517519)
                  ·
                    rfl

theorem cell23_3414899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 8].length) (baseStart_3414899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414899 prefixEnd_3414899 := by exact prefixLift 3414899
  have htrace : WordTrace (prefixWord ++ tailWord_3414899) baseStart_3414899 baseEnd_3414899 := by
    simpa [prefixWord, tailWord_3414899, baseEnd_3414899] using wordTrace_append hprefix tailTrace_3414899
  have hstable : (prefixWord ++ tailWord_3414899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414899).length < 2 ^ (prefixWord ++ tailWord_3414899).sum := by decide
  have hdescent : baseEnd_3414899 < baseStart_3414899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414916 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 6]
def baseStart_3414916 : Nat := 118140960795 + 3414916 * 2 ^ 59
def prefixEnd_3414916 : Nat := 4983230072969 + 3 ^ 40 * 3414916 * 2
def baseEnd_3414916 : Nat := 194832589192140706571677

theorem tailTrace_3414916 : CollatzResearch.WordTrace tailWord_3414916 prefixEnd_3414916 194832589192140706571677 := by
  unfold tailWord_3414916
  simp only [CollatzResearch.WordTrace]
  refine ⟨62276109448175014032648301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83034812597566685376864401 62276109448175014032648301)
  ·
    refine ⟨23353541043065630262243113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62276109448175014032648301 23353541043065630262243113)
    ·
      refine ⟨17515155782299222696682335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23353541043065630262243113 17515155782299222696682335)
      ·
        refine ⟨26272733673448834045023503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17515155782299222696682335 26272733673448834045023503)
        ·
          refine ⟨39409100510173251067535255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26272733673448834045023503 39409100510173251067535255)
          ·
            refine ⟨59113650765259876601302883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39409100510173251067535255 59113650765259876601302883)
            ·
              refine ⟨88670476147889814901954325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59113650765259876601302883 88670476147889814901954325)
              ·
                refine ⟨4156428569432335073529109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88670476147889814901954325 4156428569432335073529109)
                ·
                  refine ⟨194832589192140706571677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4156428569432335073529109 194832589192140706571677)
                  ·
                    rfl

theorem cell23_3414916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_3414916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414916 prefixEnd_3414916 := by exact prefixLift 3414916
  have htrace : WordTrace (prefixWord ++ tailWord_3414916) baseStart_3414916 baseEnd_3414916 := by
    simpa [prefixWord, tailWord_3414916, baseEnd_3414916] using wordTrace_append hprefix tailTrace_3414916
  have hstable : (prefixWord ++ tailWord_3414916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414916).length < 2 ^ (prefixWord ++ tailWord_3414916).sum := by decide
  have hdescent : baseEnd_3414916 < baseStart_3414916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414920 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 3, 4]
def baseStart_3414920 : Nat := 118140960795 + 3414920 * 2 ^ 59
def prefixEnd_3414920 : Nat := 4983230072969 + 3 ^ 40 * 3414920 * 2
def baseEnd_3414920 : Nat := 584498452217294781165025

theorem tailTrace_3414920 : CollatzResearch.WordTrace tailWord_3414920 prefixEnd_3414920 584498452217294781165025 := by
  unfold tailWord_3414920
  simp only [CollatzResearch.WordTrace]
  refine ⟨62276182394167768374221107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83034909858890357832294809 62276182394167768374221107)
  ·
    refine ⟨93414273591251652561331661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62276182394167768374221107 93414273591251652561331661)
    ·
      refine ⟨35030352596719369710499373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93414273591251652561331661 35030352596719369710499373)
      ·
        refine ⟨13136382223769763641437265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35030352596719369710499373 13136382223769763641437265)
        ·
          refine ⟨9852286667827322731077949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13136382223769763641437265 9852286667827322731077949)
          ·
            refine ⟨3694607500435246024154231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9852286667827322731077949 3694607500435246024154231)
            ·
              refine ⟨5541911250652869036231347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694607500435246024154231 5541911250652869036231347)
              ·
                refine ⟨8312866875979303554347021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5541911250652869036231347 8312866875979303554347021)
                ·
                  refine ⟨3117325078492238832880133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8312866875979303554347021 3117325078492238832880133)
                  ·
                    refine ⟨584498452217294781165025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3117325078492238832880133 584498452217294781165025)
                    ·
                      rfl

theorem cell23_3414920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_3414920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414920 prefixEnd_3414920 := by exact prefixLift 3414920
  have htrace : WordTrace (prefixWord ++ tailWord_3414920) baseStart_3414920 baseEnd_3414920 := by
    simpa [prefixWord, tailWord_3414920, baseEnd_3414920] using wordTrace_append hprefix tailTrace_3414920
  have hstable : (prefixWord ++ tailWord_3414920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414920).length < 2 ^ (prefixWord ++ tailWord_3414920).sum := by decide
  have hdescent : baseEnd_3414920 < baseStart_3414920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414929 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 2, 9]
def baseStart_3414929 : Nat := 118140960795 + 3414929 * 2 ^ 59
def prefixEnd_3414929 : Nat := 4983230072969 + 3 ^ 40 * 3414929 * 2
def baseEnd_3414929 : Nat := 584499992659258269427511

theorem tailTrace_3414929 : CollatzResearch.WordTrace tailWord_3414929 prefixEnd_3414929 584499992659258269427511 := by
  unfold tailWord_3414929
  simp only [CollatzResearch.WordTrace]
  refine ⟨124552693045302931285519841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83035128696868620857013227 124552693045302931285519841)
  ·
    refine ⟨93414519783977198464139881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124552693045302931285519841 93414519783977198464139881)
    ·
      refine ⟨70060889837982898848104911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93414519783977198464139881 70060889837982898848104911)
      ·
        refine ⟨105091334756974348272157367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70060889837982898848104911 105091334756974348272157367)
        ·
          refine ⟨157637002135461522408236051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105091334756974348272157367 157637002135461522408236051)
          ·
            refine ⟨236455503203192283612354077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157637002135461522408236051 236455503203192283612354077)
            ·
              refine ⟨88670813701197106354632779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236455503203192283612354077 88670813701197106354632779)
              ·
                refine ⟨133006220551795659531949169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88670813701197106354632779 133006220551795659531949169)
                ·
                  refine ⟨99754665413846744648961877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133006220551795659531949169 99754665413846744648961877)
                  ·
                    refine ⟨584499992659258269427511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 99754665413846744648961877 584499992659258269427511)
                    ·
                      rfl

theorem cell23_3414929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_3414929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414929 prefixEnd_3414929 := by exact prefixLift 3414929
  have htrace : WordTrace (prefixWord ++ tailWord_3414929) baseStart_3414929 baseEnd_3414929 := by
    simpa [prefixWord, tailWord_3414929, baseEnd_3414929] using wordTrace_append hprefix tailTrace_3414929
  have hstable : (prefixWord ++ tailWord_3414929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414929).length < 2 ^ (prefixWord ++ tailWord_3414929).sum := by decide
  have hdescent : baseEnd_3414929 < baseStart_3414929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414933 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 6]
def baseStart_3414933 : Nat := 118140960795 + 3414933 * 2 ^ 59
def prefixEnd_3414933 : Nat := 4983230072969 + 3 ^ 40 * 3414933 * 2
def baseEnd_3414933 : Nat := 194833559100043643625835

theorem tailTrace_3414933 : CollatzResearch.WordTrace tailWord_3414933 prefixEnd_3414933 194833559100043643625835 := by
  unfold tailWord_3414933
  simp only [CollatzResearch.WordTrace]
  refine ⟨124552838937288439968665453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83035225958192293312443635 124552838937288439968665453)
  ·
    refine ⟨46707314601483164988249545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124552838937288439968665453 46707314601483164988249545)
    ·
      refine ⟨35030485951112373741187159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46707314601483164988249545 35030485951112373741187159)
      ·
        refine ⟨52545728926668560611780739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35030485951112373741187159 52545728926668560611780739)
        ·
          refine ⟨78818593390002840917671109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52545728926668560611780739 78818593390002840917671109)
          ·
            refine ⟨14778486260625532672063333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78818593390002840917671109 14778486260625532672063333)
            ·
              refine ⟨2770966173867287376011875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14778486260625532672063333 2770966173867287376011875)
              ·
                refine ⟨4156449260800931064017813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770966173867287376011875 4156449260800931064017813)
                ·
                  refine ⟨194833559100043643625835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4156449260800931064017813 194833559100043643625835)
                  ·
                    rfl

theorem cell23_3414933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 6].length) (baseStart_3414933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414933 prefixEnd_3414933 := by exact prefixLift 3414933
  have htrace : WordTrace (prefixWord ++ tailWord_3414933) baseStart_3414933 baseEnd_3414933 := by
    simpa [prefixWord, tailWord_3414933, baseEnd_3414933] using wordTrace_append hprefix tailTrace_3414933
  have hstable : (prefixWord ++ tailWord_3414933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414933).length < 2 ^ (prefixWord ++ tailWord_3414933).sum := by decide
  have hdescent : baseEnd_3414933 < baseStart_3414933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414986 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_3414986 : Nat := 118140960795 + 3414986 * 2 ^ 59
def prefixEnd_3414986 : Nat := 4983230072969 + 3 ^ 40 * 3414986 * 2
def baseEnd_3414986 : Nat := 1753529246375081085269771

theorem tailTrace_3414986 : CollatzResearch.WordTrace tailWord_3414986 prefixEnd_3414986 1753529246375081085269771 := by
  unfold tailWord_3414986
  simp only [CollatzResearch.WordTrace]
  refine ⟨31138693001524107505086203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83036514670730953346896541 31138693001524107505086203)
  ·
    refine ⟨46708039502286161257629305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31138693001524107505086203 46708039502286161257629305)
    ·
      refine ⟨35031029626714620943221979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46708039502286161257629305 35031029626714620943221979)
      ·
        refine ⟨52546544440071931414832969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35031029626714620943221979 52546544440071931414832969)
        ·
          refine ⟨39409908330053948561124727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52546544440071931414832969 39409908330053948561124727)
          ·
            refine ⟨59114862495080922841687091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39409908330053948561124727 59114862495080922841687091)
            ·
              refine ⟨88672293742621384262530637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59114862495080922841687091 88672293742621384262530637)
              ·
                refine ⟨33252110153483019098448989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88672293742621384262530637 33252110153483019098448989)
                ·
                  refine ⟨12469541307556132161918371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33252110153483019098448989 12469541307556132161918371)
                  ·
                    refine ⟨18704311961334198242877557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12469541307556132161918371 18704311961334198242877557)
                    ·
                      refine ⟨1753529246375081085269771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18704311961334198242877557 1753529246375081085269771)
                      ·
                        rfl

theorem cell23_3414986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_3414986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414986 prefixEnd_3414986 := by exact prefixLift 3414986
  have htrace : WordTrace (prefixWord ++ tailWord_3414986) baseStart_3414986 baseEnd_3414986 := by
    simpa [prefixWord, tailWord_3414986, baseEnd_3414986] using wordTrace_append hprefix tailTrace_3414986
  have hstable : (prefixWord ++ tailWord_3414986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414986).length < 2 ^ (prefixWord ++ tailWord_3414986).sum := by decide
  have hdescent : baseEnd_3414986 < baseStart_3414986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414993 : List Nat := [1, 2, 2, 1, 2, 1, 3, 5, 2, 4]
def baseStart_3414993 : Nat := 118140960795 + 3414993 * 2 ^ 59
def prefixEnd_3414993 : Nat := 4983230072969 + 3 ^ 40 * 3414993 * 2
def baseEnd_3414993 : Nat := 584510946913220852627413

theorem tailTrace_3414993 : CollatzResearch.WordTrace tailWord_3414993 prefixEnd_3414993 584510946913220852627413 := by
  unfold tailWord_3414993
  simp only [CollatzResearch.WordTrace]
  refine ⟨124555027317071070215849633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83036684878047380143899755 124555027317071070215849633)
  ·
    refine ⟨93416270487803302661887225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124555027317071070215849633 93416270487803302661887225)
    ·
      refine ⟨70062202865852476996415419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93416270487803302661887225 70062202865852476996415419)
      ·
        refine ⟨105093304298778715494623129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70062202865852476996415419 105093304298778715494623129)
        ·
          refine ⟨78819978224084036620967347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105093304298778715494623129 78819978224084036620967347)
          ·
            refine ⟨118229967336126054931451021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78819978224084036620967347 118229967336126054931451021)
            ·
              refine ⟨44336237751047270599294133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118229967336126054931451021 44336237751047270599294133)
              ·
                refine ⟨4156522289160681618683825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44336237751047270599294133 4156522289160681618683825)
                ·
                  refine ⟨3117391716870511214012869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4156522289160681618683825 3117391716870511214012869)
                  ·
                    refine ⟨584510946913220852627413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3117391716870511214012869 584510946913220852627413)
                    ·
                      rfl

theorem cell23_3414993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_3414993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3414993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3414993 prefixEnd_3414993 := by exact prefixLift 3414993
  have htrace : WordTrace (prefixWord ++ tailWord_3414993) baseStart_3414993 baseEnd_3414993 := by
    simpa [prefixWord, tailWord_3414993, baseEnd_3414993] using wordTrace_append hprefix tailTrace_3414993
  have hstable : (prefixWord ++ tailWord_3414993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414993).length < 2 ^ (prefixWord ++ tailWord_3414993).sum := by decide
  have hdescent : baseEnd_3414993 < baseStart_3414993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415000 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 5, 2, 2]
def baseStart_3415000 : Nat := 118140960795 + 3415000 * 2 ^ 59
def prefixEnd_3415000 : Nat := 4983230072969 + 3 ^ 40 * 3415000 * 2
def baseEnd_3415000 : Nat := 1753536435104244030494707

theorem tailTrace_3415000 : CollatzResearch.WordTrace tailWord_3415000 prefixEnd_3415000 1753536435104244030494707 := by
  unfold tailWord_3415000
  simp only [CollatzResearch.WordTrace]
  refine ⟨62277641314022855205677227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83036855085363806940902969 62277641314022855205677227)
  ·
    refine ⟨93416461971034282808515841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62277641314022855205677227 93416461971034282808515841)
    ·
      refine ⟨70062346478275712106386881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93416461971034282808515841 70062346478275712106386881)
      ·
        refine ⟨52546759858706784079790161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70062346478275712106386881 52546759858706784079790161)
        ·
          refine ⟨39410069894030088059842621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52546759858706784079790161 39410069894030088059842621)
          ·
            refine ⟨14778776210261283022440983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39410069894030088059842621 14778776210261283022440983)
            ·
              refine ⟨22168164315391924533661475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14778776210261283022440983 22168164315391924533661475)
              ·
                refine ⟨33252246473087886800492213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22168164315391924533661475 33252246473087886800492213)
                ·
                  refine ⟨3117398106851989387546145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33252246473087886800492213 3117398106851989387546145)
                  ·
                    refine ⟨2338048580138992040659609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3117398106851989387546145 2338048580138992040659609)
                    ·
                      refine ⟨1753536435104244030494707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2338048580138992040659609 1753536435104244030494707)
                      ·
                        rfl

theorem cell23_3415000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_3415000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415000 prefixEnd_3415000 := by exact prefixLift 3415000
  have htrace : WordTrace (prefixWord ++ tailWord_3415000) baseStart_3415000 baseEnd_3415000 := by
    simpa [prefixWord, tailWord_3415000, baseEnd_3415000] using wordTrace_append hprefix tailTrace_3415000
  have hstable : (prefixWord ++ tailWord_3415000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415000).length < 2 ^ (prefixWord ++ tailWord_3415000).sum := by decide
  have hdescent : baseEnd_3415000 < baseStart_3415000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415010 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3415010 : Nat := 118140960795 + 3415010 * 2 ^ 59
def prefixEnd_3415010 : Nat := 4983230072969 + 3 ^ 40 * 3415010 * 2
def baseEnd_3415010 : Nat := 584513856636929663789887

theorem tailTrace_3415010 : CollatzResearch.WordTrace tailWord_3415010 prefixEnd_3415010 584513856636929663789887 := by
  unfold tailWord_3415010
  simp only [CollatzResearch.WordTrace]
  refine ⟨31138911839502370529804621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83037098238672988079478989 31138911839502370529804621)
  ·
    refine ⟨11677091939813388948676733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31138911839502370529804621 11677091939813388948676733)
    ·
      refine ⟨4378909477430020855753775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11677091939813388948676733 4378909477430020855753775)
      ·
        refine ⟨6568364216145031283630663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4378909477430020855753775 6568364216145031283630663)
        ·
          refine ⟨9852546324217546925445995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6568364216145031283630663 9852546324217546925445995)
          ·
            refine ⟨14778819486326320388168993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9852546324217546925445995 14778819486326320388168993)
            ·
              refine ⟨11084114614744740291126745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14778819486326320388168993 11084114614744740291126745)
              ·
                refine ⟨8313085961058555218345059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11084114614744740291126745 8313085961058555218345059)
                ·
                  refine ⟨12469628941587832827517589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313085961058555218345059 12469628941587832827517589)
                  ·
                    refine ⟨584513856636929663789887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12469628941587832827517589 584513856636929663789887)
                    ·
                      rfl

theorem cell23_3415010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3415010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415010 prefixEnd_3415010 := by exact prefixLift 3415010
  have htrace : WordTrace (prefixWord ++ tailWord_3415010) baseStart_3415010 baseEnd_3415010 := by
    simpa [prefixWord, tailWord_3415010, baseEnd_3415010] using wordTrace_append hprefix tailTrace_3415010
  have hstable : (prefixWord ++ tailWord_3415010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415010).length < 2 ^ (prefixWord ++ tailWord_3415010).sum := by decide
  have hdescent : baseEnd_3415010 < baseStart_3415010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415028 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3415028 : Nat := 118140960795 + 3415028 * 2 ^ 59
def prefixEnd_3415028 : Nat := 4983230072969 + 3 ^ 40 * 3415028 * 2
def baseEnd_3415028 : Nat := 1753550812562569920944579

theorem tailTrace_3415028 : CollatzResearch.WordTrace tailWord_3415028 prefixEnd_3415028 1753550812562569920944579 := by
  unfold tailWord_3415028
  simp only [CollatzResearch.WordTrace]
  refine ⟨62278151935972135596686869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83037535914629514128915825 62278151935972135596686869)
  ·
    refine ⟨2919288371998693856094697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62278151935972135596686869 2919288371998693856094697)
    ·
      refine ⟨2189466278999020392071023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2919288371998693856094697 2189466278999020392071023)
      ·
        refine ⟨3284199418498530588106535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189466278999020392071023 3284199418498530588106535)
        ·
          refine ⟨4926299127747795882159803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284199418498530588106535 4926299127747795882159803)
          ·
            refine ⟨7389448691621693823239705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926299127747795882159803 7389448691621693823239705)
            ·
              refine ⟨5542086518716270367429779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7389448691621693823239705 5542086518716270367429779)
              ·
                refine ⟨8313129778074405551144669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5542086518716270367429779 8313129778074405551144669)
                ·
                  refine ⟨3117423666777902081679251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8313129778074405551144669 3117423666777902081679251)
                  ·
                    refine ⟨4676135500166853122518877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3117423666777902081679251 4676135500166853122518877)
                    ·
                      refine ⟨1753550812562569920944579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4676135500166853122518877 1753550812562569920944579)
                      ·
                        rfl

theorem cell23_3415028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3415028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415028 prefixEnd_3415028 := by exact prefixLift 3415028
  have htrace : WordTrace (prefixWord ++ tailWord_3415028) baseStart_3415028 baseEnd_3415028 := by
    simpa [prefixWord, tailWord_3415028, baseEnd_3415028] using wordTrace_append hprefix tailTrace_3415028
  have hstable : (prefixWord ++ tailWord_3415028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415028).length < 2 ^ (prefixWord ++ tailWord_3415028).sum := by decide
  have hdescent : baseEnd_3415028 < baseStart_3415028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415050 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_3415050 : Nat := 118140960795 + 3415050 * 2 ^ 59
def prefixEnd_3415050 : Nat := 4983230072969 + 3 ^ 40 * 3415050 * 2
def baseEnd_3415050 : Nat := 1753562109136968834869477

theorem tailTrace_3415050 : CollatzResearch.WordTrace tailWord_3415050 prefixEnd_3415050 1753562109136968834869477 := by
  unfold tailWord_3415050
  simp only [CollatzResearch.WordTrace]
  refine ⟨31139276569466142237668651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83038070851909712633783069 31139276569466142237668651)
  ·
    refine ⟨46708914854199213356502977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31139276569466142237668651 46708914854199213356502977)
    ·
      refine ⟨35031686140649410017377233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46708914854199213356502977 35031686140649410017377233)
      ·
        refine ⟨26273764605487057513032925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35031686140649410017377233 26273764605487057513032925)
        ·
          refine ⟨9852661727057646567387347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26273764605487057513032925 9852661727057646567387347)
          ·
            refine ⟨14778992590586469851081021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9852661727057646567387347 14778992590586469851081021)
            ·
              refine ⟨5542122221469926194155383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14778992590586469851081021 5542122221469926194155383)
              ·
                refine ⟨8313183332204889291233075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5542122221469926194155383 8313183332204889291233075)
                ·
                  refine ⟨12469774998307333936849613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313183332204889291233075 12469774998307333936849613)
                  ·
                    refine ⟨4676165624365250226318605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12469774998307333936849613 4676165624365250226318605)
                    ·
                      refine ⟨1753562109136968834869477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4676165624365250226318605 1753562109136968834869477)
                      ·
                        rfl

theorem cell23_3415050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_3415050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415050 prefixEnd_3415050 := by exact prefixLift 3415050
  have htrace : WordTrace (prefixWord ++ tailWord_3415050) baseStart_3415050 baseEnd_3415050 := by
    simpa [prefixWord, tailWord_3415050, baseEnd_3415050] using wordTrace_append hprefix tailTrace_3415050
  have hstable : (prefixWord ++ tailWord_3415050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415050).length < 2 ^ (prefixWord ++ tailWord_3415050).sum := by decide
  have hdescent : baseEnd_3415050 < baseStart_3415050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415063 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_3415063 : Nat := 118140960795 + 3415063 * 2 ^ 59
def prefixEnd_3415063 : Nat := 4983230072969 + 3 ^ 40 * 3415063 * 2
def baseEnd_3415063 : Nat := 1753568784385477284006917

theorem tailTrace_3415063 : CollatzResearch.WordTrace tailWord_3415063 prefixEnd_3415063 1753568784385477284006917 := by
  unfold tailWord_3415063
  simp only [CollatzResearch.WordTrace]
  refine ⟨124557580426817472170897843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83038386951211648113931895 124557580426817472170897843)
  ·
    refine ⟨186836370640226208256346765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124557580426817472170897843 186836370640226208256346765)
    ·
      refine ⟨70063638990084828096130037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186836370640226208256346765 70063638990084828096130037)
      ·
        refine ⟨6568466155320452634012191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70063638990084828096130037 6568466155320452634012191)
        ·
          refine ⟨9852699232980678951018287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6568466155320452634012191 9852699232980678951018287)
          ·
            refine ⟨14779048849471018426527431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9852699232980678951018287 14779048849471018426527431)
            ·
              refine ⟨22168573274206527639791147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14779048849471018426527431 22168573274206527639791147)
              ·
                refine ⟨33252859911309791459686721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22168573274206527639791147 33252859911309791459686721)
                ·
                  refine ⟨24939644933482343594765041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33252859911309791459686721 24939644933482343594765041)
                  ·
                    refine ⟨18704733700111757696073781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24939644933482343594765041 18704733700111757696073781)
                    ·
                      refine ⟨1753568784385477284006917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18704733700111757696073781 1753568784385477284006917)
                      ·
                        rfl

theorem cell23_3415063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_3415063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415063 prefixEnd_3415063 := by exact prefixLift 3415063
  have htrace : WordTrace (prefixWord ++ tailWord_3415063) baseStart_3415063 baseEnd_3415063 := by
    simpa [prefixWord, tailWord_3415063, baseEnd_3415063] using wordTrace_append hprefix tailTrace_3415063
  have hstable : (prefixWord ++ tailWord_3415063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415063).length < 2 ^ (prefixWord ++ tailWord_3415063).sum := by decide
  have hdescent : baseEnd_3415063 < baseStart_3415063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415068 : List Nat := [2, 2, 3, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_3415068 : Nat := 118140960795 + 3415068 * 2 ^ 59
def prefixEnd_3415068 : Nat := 4983230072969 + 3 ^ 40 * 3415068 * 2
def baseEnd_3415068 : Nat := 1753571351788749764444395

theorem tailTrace_3415068 : CollatzResearch.WordTrace tailWord_3415068 prefixEnd_3415068 1753571351788749764444395 := by
  unfold tailWord_3415068
  simp only [CollatzResearch.WordTrace]
  refine ⟨62278881395899679012414929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83038508527866238683219905 62278881395899679012414929)
  ·
    refine ⟨46709161046924759259311197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62278881395899679012414929 46709161046924759259311197)
    ·
      refine ⟨17515935392596784722241699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46709161046924759259311197 17515935392596784722241699)
      ·
        refine ⟨26273903088895177083362549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17515935392596784722241699 26273903088895177083362549)
        ·
          refine ⟨2463178414583922851565239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26273903088895177083362549 2463178414583922851565239)
          ·
            refine ⟨3694767621875884277347859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463178414583922851565239 3694767621875884277347859)
            ·
              refine ⟨5542151432813826416021789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694767621875884277347859 5542151432813826416021789)
              ·
                refine ⟨2078306787305184906008171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5542151432813826416021789 2078306787305184906008171)
                ·
                  refine ⟨3117460180957777359012257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078306787305184906008171 3117460180957777359012257)
                  ·
                    refine ⟨2338095135718333019259193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3117460180957777359012257 2338095135718333019259193)
                    ·
                      refine ⟨1753571351788749764444395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2338095135718333019259193 1753571351788749764444395)
                      ·
                        rfl

theorem cell23_3415068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_3415068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415068 prefixEnd_3415068 := by exact prefixLift 3415068
  have htrace : WordTrace (prefixWord ++ tailWord_3415068) baseStart_3415068 baseEnd_3415068 := by
    simpa [prefixWord, tailWord_3415068, baseEnd_3415068] using wordTrace_append hprefix tailTrace_3415068
  have hstable : (prefixWord ++ tailWord_3415068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415068).length < 2 ^ (prefixWord ++ tailWord_3415068).sum := by decide
  have hdescent : baseEnd_3415068 < baseStart_3415068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415093 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_3415093 : Nat := 118140960795 + 3415093 * 2 ^ 59
def prefixEnd_3415093 : Nat := 4983230072969 + 3 ^ 40 * 3415093 * 2
def baseEnd_3415093 : Nat := 1753584188805112166631779

theorem tailTrace_3415093 : CollatzResearch.WordTrace tailWord_3415093 prefixEnd_3415093 1753584188805112166631779 := by
  unfold tailWord_3415093
  simp only [CollatzResearch.WordTrace]
  refine ⟨124558674616708787294489933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83039116411139191529659955 124558674616708787294489933)
  ·
    refine ⟨46709502981265795235433725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124558674616708787294489933 46709502981265795235433725)
    ·
      refine ⟨17516063617974673213287647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46709502981265795235433725 17516063617974673213287647)
      ·
        refine ⟨26274095426962009819931471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17516063617974673213287647 26274095426962009819931471)
        ·
          refine ⟨39411143140443014729897207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26274095426962009819931471 39411143140443014729897207)
          ·
            refine ⟨59116714710664522094845811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39411143140443014729897207 59116714710664522094845811)
            ·
              refine ⟨88675072065996783142268717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59116714710664522094845811 88675072065996783142268717)
              ·
                refine ⟨33253152024748793678350769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88675072065996783142268717 33253152024748793678350769)
                ·
                  refine ⟨24939864018561595258763077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33253152024748793678350769 24939864018561595258763077)
                  ·
                    refine ⟨4676224503480299111018077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24939864018561595258763077 4676224503480299111018077)
                    ·
                      refine ⟨1753584188805112166631779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4676224503480299111018077 1753584188805112166631779)
                      ·
                        rfl

theorem cell23_3415093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_3415093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415093 prefixEnd_3415093 := by exact prefixLift 3415093
  have htrace : WordTrace (prefixWord ++ tailWord_3415093) baseStart_3415093 baseEnd_3415093 := by
    simpa [prefixWord, tailWord_3415093, baseEnd_3415093] using wordTrace_append hprefix tailTrace_3415093
  have hstable : (prefixWord ++ tailWord_3415093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415093).length < 2 ^ (prefixWord ++ tailWord_3415093).sum := by decide
  have hdescent : baseEnd_3415093 < baseStart_3415093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415107 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 2, 2, 2]
def baseStart_3415107 : Nat := 118140960795 + 3415107 * 2 ^ 59
def prefixEnd_3415107 : Nat := 4983230072969 + 3 ^ 40 * 3415107 * 2
def baseEnd_3415107 : Nat := 1753591377534275111856715

theorem tailTrace_3415107 : CollatzResearch.WordTrace tailWord_3415107 prefixEnd_3415107 1753591377534275111856715 := by
  unfold tailWord_3415107
  simp only [CollatzResearch.WordTrace]
  refine ⟨124559185238658067685499575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83039456825772045123666383 124559185238658067685499575)
  ·
    refine ⟨186838777857987101528249363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124559185238658067685499575 186838777857987101528249363)
    ·
      refine ⟨280258166786980652292374045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186838777857987101528249363 280258166786980652292374045)
      ·
        refine ⟨105096812545117744609640267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280258166786980652292374045 105096812545117744609640267)
        ·
          refine ⟨157645218817676616914460401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105096812545117744609640267 157645218817676616914460401)
          ·
            refine ⟨118233914113257462685845301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157645218817676616914460401 118233914113257462685845301)
            ·
              refine ⟨11084429448117887126797997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118233914113257462685845301 11084429448117887126797997)
              ·
                refine ⟨4156661043044207672549249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11084429448117887126797997 4156661043044207672549249)
                ·
                  refine ⟨3117495782283155754411937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4156661043044207672549249 3117495782283155754411937)
                  ·
                    refine ⟨2338121836712366815808953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3117495782283155754411937 2338121836712366815808953)
                    ·
                      refine ⟨1753591377534275111856715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2338121836712366815808953 1753591377534275111856715)
                      ·
                        rfl

theorem cell23_3415107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 2, 2].length) (baseStart_3415107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415107 prefixEnd_3415107 := by exact prefixLift 3415107
  have htrace : WordTrace (prefixWord ++ tailWord_3415107) baseStart_3415107 baseEnd_3415107 := by
    simpa [prefixWord, tailWord_3415107, baseEnd_3415107] using wordTrace_append hprefix tailTrace_3415107
  have hstable : (prefixWord ++ tailWord_3415107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415107).length < 2 ^ (prefixWord ++ tailWord_3415107).sum := by decide
  have hdescent : baseEnd_3415107 < baseStart_3415107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415163 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 4]
def baseStart_3415163 : Nat := 118140960795 + 3415163 * 2 ^ 59
def prefixEnd_3415163 : Nat := 4983230072969 + 3 ^ 40 * 3415163 * 2
def baseEnd_3415163 : Nat := 1753620132450926892756457

theorem tailTrace_3415163 : CollatzResearch.WordTrace tailWord_3415163 prefixEnd_3415163 1753620132450926892756457 := by
  unfold tailWord_3415163
  simp only [CollatzResearch.WordTrace]
  refine ⟨124561227726455189249538143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83040818484303459499692095 124561227726455189249538143)
  ·
    refine ⟨186841841589682783874307215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124561227726455189249538143 186841841589682783874307215)
    ·
      refine ⟨280262762384524175811460823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186841841589682783874307215 280262762384524175811460823)
      ·
        refine ⟨420394143576786263717191235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280262762384524175811460823 420394143576786263717191235)
        ·
          refine ⟨630591215365179395575786853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420394143576786263717191235 630591215365179395575786853)
          ·
            refine ⟨118235852880971136670460035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 630591215365179395575786853 118235852880971136670460035)
            ·
              refine ⟨177353779321456705005690053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118235852880971136670460035 177353779321456705005690053)
              ·
                refine ⟨33253833622773132188566885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177353779321456705005690053 33253833622773132188566885)
                ·
                  refine ⟨6235093804269962285356291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33253833622773132188566885 6235093804269962285356291)
                  ·
                    refine ⟨9352640706404943428034437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6235093804269962285356291 9352640706404943428034437)
                    ·
                      refine ⟨1753620132450926892756457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9352640706404943428034437 1753620132450926892756457)
                      ·
                        rfl

theorem cell23_3415163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 4].length) (baseStart_3415163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415163 prefixEnd_3415163 := by exact prefixLift 3415163
  have htrace : WordTrace (prefixWord ++ tailWord_3415163) baseStart_3415163 baseEnd_3415163 := by
    simpa [prefixWord, tailWord_3415163, baseEnd_3415163] using wordTrace_append hprefix tailTrace_3415163
  have hstable : (prefixWord ++ tailWord_3415163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415163).length < 2 ^ (prefixWord ++ tailWord_3415163).sum := by decide
  have hdescent : baseEnd_3415163 < baseStart_3415163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415200 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 3]
def baseStart_3415200 : Nat := 118140960795 + 3415200 * 2 ^ 59
def prefixEnd_3415200 : Nat := 4983230072969 + 3 ^ 40 * 3415200 * 2
def baseEnd_3415200 : Nat := 1753639131235143247993787

theorem tailTrace_3415200 : CollatzResearch.WordTrace tailWord_3415200 prefixEnd_3415200 1753639131235143247993787 := by
  unfold tailWord_3415200
  simp only [CollatzResearch.WordTrace]
  refine ⟨62281288613660572284317527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83041718151547429712423369 62281288613660572284317527)
  ·
    refine ⟨93421932920490858426476291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62281288613660572284317527 93421932920490858426476291)
    ·
      refine ⟨140132899380736287639714437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93421932920490858426476291 140132899380736287639714437)
      ·
        refine ⟨26274918633888053932446457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140132899380736287639714437 26274918633888053932446457)
        ·
          refine ⟨19706188975416040449334843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26274918633888053932446457 19706188975416040449334843)
          ·
            refine ⟨29559283463124060674002265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19706188975416040449334843 29559283463124060674002265)
            ·
              refine ⟨22169462597343045505501699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29559283463124060674002265 22169462597343045505501699)
              ·
                refine ⟨33254193896014568258252549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22169462597343045505501699 33254193896014568258252549)
                ·
                  refine ⟨6235161355502731548422353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33254193896014568258252549 6235161355502731548422353)
                  ·
                    refine ⟨4676371016627048661316765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6235161355502731548422353 4676371016627048661316765)
                    ·
                      refine ⟨1753639131235143247993787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4676371016627048661316765 1753639131235143247993787)
                      ·
                        rfl

theorem cell23_3415200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_3415200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415200 prefixEnd_3415200 := by exact prefixLift 3415200
  have htrace : WordTrace (prefixWord ++ tailWord_3415200) baseStart_3415200 baseEnd_3415200 := by
    simpa [prefixWord, tailWord_3415200, baseEnd_3415200] using wordTrace_append hprefix tailTrace_3415200
  have hstable : (prefixWord ++ tailWord_3415200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415200).length < 2 ^ (prefixWord ++ tailWord_3415200).sum := by decide
  have hdescent : baseEnd_3415200 < baseStart_3415200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415207 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 3, 4]
def baseStart_3415207 : Nat := 118140960795 + 3415207 * 2 ^ 59
def prefixEnd_3415207 : Nat := 4983230072969 + 3 ^ 40 * 3415207 * 2
def baseEnd_3415207 : Nat := 584547575199908240202085

theorem tailTrace_3415207 : CollatzResearch.WordTrace tailWord_3415207 prefixEnd_3415207 584547575199908240202085 := by
  unfold tailWord_3415207
  simp only [CollatzResearch.WordTrace]
  refine ⟨124562832538295784764139875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83041888358863856509426583 124562832538295784764139875)
  ·
    refine ⟨186844248807443677146209813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124562832538295784764139875 186844248807443677146209813)
    ·
      refine ⟨8758324162848922366228585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 186844248807443677146209813 8758324162848922366228585)
      ·
        refine ⟨6568743122136691774671439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8758324162848922366228585 6568743122136691774671439)
        ·
          refine ⟨9853114683205037662007159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6568743122136691774671439 9853114683205037662007159)
          ·
            refine ⟨14779672024807556493010739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9853114683205037662007159 14779672024807556493010739)
            ·
              refine ⟨22169508037211334739516109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14779672024807556493010739 22169508037211334739516109)
              ·
                refine ⟨8313565513954250527318541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22169508037211334739516109 8313565513954250527318541)
                ·
                  refine ⟨3117587067732843947744453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8313565513954250527318541 3117587067732843947744453)
                  ·
                    refine ⟨584547575199908240202085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3117587067732843947744453 584547575199908240202085)
                    ·
                      rfl

theorem cell23_3415207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_3415207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415207 prefixEnd_3415207 := by exact prefixLift 3415207
  have htrace : WordTrace (prefixWord ++ tailWord_3415207) baseStart_3415207 baseEnd_3415207 := by
    simpa [prefixWord, tailWord_3415207, baseEnd_3415207] using wordTrace_append hprefix tailTrace_3415207
  have hstable : (prefixWord ++ tailWord_3415207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415207).length < 2 ^ (prefixWord ++ tailWord_3415207).sum := by decide
  have hdescent : baseEnd_3415207 < baseStart_3415207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415223 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_3415223 : Nat := 118140960795 + 3415223 * 2 ^ 59
def prefixEnd_3415223 : Nat := 4983230072969 + 3 ^ 40 * 3415223 * 2
def baseEnd_3415223 : Nat := 1753650941290196658006181

theorem tailTrace_3415223 : CollatzResearch.WordTrace tailWord_3415223 prefixEnd_3415223 1753650941290196658006181 := by
  unfold tailWord_3415223
  simp only [CollatzResearch.WordTrace]
  refine ⟨124563416106237819496722323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83042277404158546331148215 124563416106237819496722323)
  ·
    refine ⟨186845124159356729245083485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124563416106237819496722323 186845124159356729245083485)
    ·
      refine ⟨70066921559758773466906307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186845124159356729245083485 70066921559758773466906307)
      ·
        refine ⟨105100382339638160200359461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70066921559758773466906307 105100382339638160200359461)
        ·
          refine ⟨19706321688682155037567399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105100382339638160200359461 19706321688682155037567399)
          ·
            refine ⟨29559482533023232556351099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19706321688682155037567399 29559482533023232556351099)
            ·
              refine ⟨44339223799534848834526649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29559482533023232556351099 44339223799534848834526649)
              ·
                refine ⟨33254417849651136625894987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44339223799534848834526649 33254417849651136625894987)
                ·
                  refine ⟨49881626774476704938842481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33254417849651136625894987 49881626774476704938842481)
                  ·
                    refine ⟨37411220080857528704131861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49881626774476704938842481 37411220080857528704131861)
                    ·
                      refine ⟨1753650941290196658006181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37411220080857528704131861 1753650941290196658006181)
                      ·
                        rfl

theorem cell23_3415223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_3415223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415223 prefixEnd_3415223 := by exact prefixLift 3415223
  have htrace : WordTrace (prefixWord ++ tailWord_3415223) baseStart_3415223 baseEnd_3415223 := by
    simpa [prefixWord, tailWord_3415223, baseEnd_3415223] using wordTrace_append hprefix tailTrace_3415223
  have hstable : (prefixWord ++ tailWord_3415223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415223).length < 2 ^ (prefixWord ++ tailWord_3415223).sum := by decide
  have hdescent : baseEnd_3415223 < baseStart_3415223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415264 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 3, 1, 3]
def baseStart_3415264 : Nat := 118140960795 + 3415264 * 2 ^ 59
def prefixEnd_3415264 : Nat := 4983230072969 + 3 ^ 40 * 3415264 * 2
def baseEnd_3415264 : Nat := 1753671993997030997593493

theorem tailTrace_3415264 : CollatzResearch.WordTrace tailWord_3415264 prefixEnd_3415264 1753671993997030997593493 := by
  unfold tailWord_3415264
  simp only [CollatzResearch.WordTrace]
  refine ⟨62282455749544641749482423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83043274332726188999309897 62282455749544641749482423)
  ·
    refine ⟨93423683624316962624223635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62282455749544641749482423 93423683624316962624223635)
    ·
      refine ⟨140135525436475443936335453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93423683624316962624223635 140135525436475443936335453)
      ·
        refine ⟨52550822038678291476125795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140135525436475443936335453 52550822038678291476125795)
        ·
          refine ⟨78826233058017437214188693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52550822038678291476125795 78826233058017437214188693)
          ·
            refine ⟨3694979674594567369415095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78826233058017437214188693 3694979674594567369415095)
            ·
              refine ⟨5542469511891851054122643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694979674594567369415095 5542469511891851054122643)
              ·
                refine ⟨8313704267837776581183965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5542469511891851054122643 8313704267837776581183965)
                ·
                  refine ⟨3117639100439166217943987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8313704267837776581183965 3117639100439166217943987)
                  ·
                    refine ⟨4676458650658749326915981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3117639100439166217943987 4676458650658749326915981)
                    ·
                      refine ⟨1753671993997030997593493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4676458650658749326915981 1753671993997030997593493)
                      ·
                        rfl

theorem cell23_3415264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_3415264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415264 prefixEnd_3415264 := by exact prefixLift 3415264
  have htrace : WordTrace (prefixWord ++ tailWord_3415264) baseStart_3415264 baseEnd_3415264 := by
    simpa [prefixWord, tailWord_3415264, baseEnd_3415264] using wordTrace_append hprefix tailTrace_3415264
  have hstable : (prefixWord ++ tailWord_3415264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415264).length < 2 ^ (prefixWord ++ tailWord_3415264).sum := by decide
  have hdescent : baseEnd_3415264 < baseStart_3415264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415271 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 6]
def baseStart_3415271 : Nat := 118140960795 + 3415271 * 2 ^ 59
def prefixEnd_3415271 : Nat := 4983230072969 + 3 ^ 40 * 3415271 * 2
def baseEnd_3415271 : Nat := 194852843151290274467329

theorem tailTrace_3415271 : CollatzResearch.WordTrace tailWord_3415271 prefixEnd_3415271 194852843151290274467329 := by
  unfold tailWord_3415271
  simp only [CollatzResearch.WordTrace]
  refine ⟨124565166810063923694469667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83043444540042615796313111 124565166810063923694469667)
  ·
    refine ⟨186847750215095885541704501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124565166810063923694469667 186847750215095885541704501)
    ·
      refine ⟨17516976582665239269534797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186847750215095885541704501 17516976582665239269534797)
      ·
        refine ⟨6568866218499464726075549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17516976582665239269534797 6568866218499464726075549)
        ·
          refine ⟨2463324831937299272278331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6568866218499464726075549 2463324831937299272278331)
          ·
            refine ⟨3694987247905948908417497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463324831937299272278331 3694987247905948908417497)
            ·
              refine ⟨2771240435929461681313123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3694987247905948908417497 2771240435929461681313123)
              ·
                refine ⟨4156860653894192521969685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771240435929461681313123 4156860653894192521969685)
                ·
                  refine ⟨194852843151290274467329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4156860653894192521969685 194852843151290274467329)
                  ·
                    rfl

theorem cell23_3415271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 6].length) (baseStart_3415271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415271 prefixEnd_3415271 := by exact prefixLift 3415271
  have htrace : WordTrace (prefixWord ++ tailWord_3415271) baseStart_3415271 baseEnd_3415271 := by
    simpa [prefixWord, tailWord_3415271, baseEnd_3415271] using wordTrace_append hprefix tailTrace_3415271
  have hstable : (prefixWord ++ tailWord_3415271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415271).length < 2 ^ (prefixWord ++ tailWord_3415271).sum := by decide
  have hdescent : baseEnd_3415271 < baseStart_3415271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415307 : List Nat := [1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 5]
def baseStart_3415307 : Nat := 118140960795 + 3415307 * 2 ^ 59
def prefixEnd_3415307 : Nat := 4983230072969 + 3 ^ 40 * 3415307 * 2
def baseEnd_3415307 : Nat := 1753694073665174329355795

theorem tailTrace_3415307 : CollatzResearch.WordTrace tailWord_3415307 prefixEnd_3415307 1753694073665174329355795 := by
  unfold tailWord_3415307
  simp only [CollatzResearch.WordTrace]
  refine ⟨124566479837933501842780175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83044319891955667895186783 124566479837933501842780175)
  ·
    refine ⟨186849719756900252764170263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124566479837933501842780175 186849719756900252764170263)
    ·
      refine ⟨280274579635350379146255395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186849719756900252764170263 280274579635350379146255395)
      ·
        refine ⟨420411869453025568719383093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280274579635350379146255395 420411869453025568719383093)
        ·
          refine ⟨39413612761221147067442165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 420411869453025568719383093 39413612761221147067442165)
          ·
            refine ⟨3695026196364482537572703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39413612761221147067442165 3695026196364482537572703)
            ·
              refine ⟨5542539294546723806359055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695026196364482537572703 5542539294546723806359055)
              ·
                refine ⟨8313808941820085709538583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5542539294546723806359055 8313808941820085709538583)
                ·
                  refine ⟨12470713412730128564307875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313808941820085709538583 12470713412730128564307875)
                  ·
                    refine ⟨18706070119095192846461813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12470713412730128564307875 18706070119095192846461813)
                    ·
                      refine ⟨1753694073665174329355795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18706070119095192846461813 1753694073665174329355795)
                      ·
                        rfl

theorem cell23_3415307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 5].length) (baseStart_3415307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415307 prefixEnd_3415307 := by exact prefixLift 3415307
  have htrace : WordTrace (prefixWord ++ tailWord_3415307) baseStart_3415307 baseEnd_3415307 := by
    simpa [prefixWord, tailWord_3415307, baseEnd_3415307] using wordTrace_append hprefix tailTrace_3415307
  have hstable : (prefixWord ++ tailWord_3415307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415307).length < 2 ^ (prefixWord ++ tailWord_3415307).sum := by decide
  have hdescent : baseEnd_3415307 < baseStart_3415307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415327 : List Nat := [1, 1, 2, 4, 4, 2, 1, 8]
def baseStart_3415327 : Nat := 118140960795 + 3415327 * 2 ^ 59
def prefixEnd_3415327 : Nat := 4983230072969 + 3 ^ 40 * 3415327 * 2
def baseEnd_3415327 : Nat := 64952012714009787077989

theorem tailTrace_3415327 : CollatzResearch.WordTrace tailWord_3415327 prefixEnd_3415327 64952012714009787077989 := by
  unfold tailWord_3415327
  simp only [CollatzResearch.WordTrace]
  refine ⟨124567209297861045258508235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83044806198574030172338823 124567209297861045258508235)
  ·
    refine ⟨186850813946791567887762353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124567209297861045258508235 186850813946791567887762353)
    ·
      refine ⟨140138110460093675915821765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186850813946791567887762353 140138110460093675915821765)
      ·
        refine ⟨26275895711267564234216581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140138110460093675915821765 26275895711267564234216581)
        ·
          refine ⟨4926730445862668293915609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26275895711267564234216581 4926730445862668293915609)
          ·
            refine ⟨3695047834397001220436707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4926730445862668293915609 3695047834397001220436707)
            ·
              refine ⟨5542571751595501830655061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695047834397001220436707 5542571751595501830655061)
              ·
                refine ⟨64952012714009787077989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5542571751595501830655061 64952012714009787077989)
                ·
                  rfl

theorem cell23_3415327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 8].length) (baseStart_3415327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415327 prefixEnd_3415327 := by exact prefixLift 3415327
  have htrace : WordTrace (prefixWord ++ tailWord_3415327) baseStart_3415327 baseEnd_3415327 := by
    simpa [prefixWord, tailWord_3415327, baseEnd_3415327] using wordTrace_append hprefix tailTrace_3415327
  have hstable : (prefixWord ++ tailWord_3415327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415327).length < 2 ^ (prefixWord ++ tailWord_3415327).sum := by decide
  have hdescent : baseEnd_3415327 < baseStart_3415327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415382 : List Nat := [5, 2, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3415382 : Nat := 118140960795 + 3415382 * 2 ^ 59
def prefixEnd_3415382 : Nat := 4983230072969 + 3 ^ 40 * 3415382 * 2
def baseEnd_3415382 : Nat := 584577528238087178639317

theorem tailTrace_3415382 : CollatzResearch.WordTrace tailWord_3415382 prefixEnd_3415382 584577528238087178639317 := by
  unfold tailWord_3415382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7785575957041361853235025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83046143541774526434506933 7785575957041361853235025)
  ·
    refine ⟨5839181967781021389926269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7785575957041361853235025 5839181967781021389926269)
    ·
      refine ⟨2189693237917883021222351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5839181967781021389926269 2189693237917883021222351)
      ·
        refine ⟨3284539856876824531833527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189693237917883021222351 3284539856876824531833527)
        ·
          refine ⟨4926809785315236797750291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284539856876824531833527 4926809785315236797750291)
          ·
            refine ⟨7390214677972855196625437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926809785315236797750291 7390214677972855196625437)
            ·
              refine ⟨2771330504239820698734539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7390214677972855196625437 2771330504239820698734539)
              ·
                refine ⟨4156995756359731048101809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771330504239820698734539 4156995756359731048101809)
                ·
                  refine ⟨3117746817269798286076357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4156995756359731048101809 3117746817269798286076357)
                  ·
                    refine ⟨584577528238087178639317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3117746817269798286076357 584577528238087178639317)
                    ·
                      rfl

theorem cell23_3415382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3415382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415382 prefixEnd_3415382 := by exact prefixLift 3415382
  have htrace : WordTrace (prefixWord ++ tailWord_3415382) baseStart_3415382 baseEnd_3415382 := by
    simpa [prefixWord, tailWord_3415382, baseEnd_3415382] using wordTrace_append hprefix tailTrace_3415382
  have hstable : (prefixWord ++ tailWord_3415382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415382).length < 2 ^ (prefixWord ++ tailWord_3415382).sum := by decide
  have hdescent : baseEnd_3415382 < baseStart_3415382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415521 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_3415521 : Nat := 118140960795 + 3415521 * 2 ^ 59
def prefixEnd_3415521 : Nat := 4983230072969 + 3 ^ 40 * 3415521 * 2
def baseEnd_3415521 : Nat := 1753803958525236492079811

theorem tailTrace_3415521 : CollatzResearch.WordTrace tailWord_3415521 prefixEnd_3415521 1753803958525236492079811 := by
  unfold tailWord_3415521
  simp only [CollatzResearch.WordTrace]
  refine ⟨124574285059158216391070417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83049523372772144260713611 124574285059158216391070417)
  ·
    refine ⟨93430713794368662293302813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124574285059158216391070417 93430713794368662293302813)
    ·
      refine ⟨35036517672888248359988555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93430713794368662293302813 35036517672888248359988555)
      ·
        refine ⟨52554776509332372539982833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35036517672888248359988555 52554776509332372539982833)
        ·
          refine ⟨39416082381999279404987125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52554776509332372539982833 39416082381999279404987125)
          ·
            refine ⟨3695257723312432444217543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39416082381999279404987125 3695257723312432444217543)
            ·
              refine ⟨5542886584968648666326315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695257723312432444217543 5542886584968648666326315)
              ·
                refine ⟨8314329877452972999489473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5542886584968648666326315 8314329877452972999489473)
                ·
                  refine ⟨6235747408089729749617105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8314329877452972999489473 6235747408089729749617105)
                  ·
                    refine ⟨4676810556067297312212829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6235747408089729749617105 4676810556067297312212829)
                    ·
                      refine ⟨1753803958525236492079811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4676810556067297312212829 1753803958525236492079811)
                      ·
                        rfl

theorem cell23_3415521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_3415521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415521 prefixEnd_3415521 := by exact prefixLift 3415521
  have htrace : WordTrace (prefixWord ++ tailWord_3415521) baseStart_3415521 baseEnd_3415521 := by
    simpa [prefixWord, tailWord_3415521, baseEnd_3415521] using wordTrace_append hprefix tailTrace_3415521
  have hstable : (prefixWord ++ tailWord_3415521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415521).length < 2 ^ (prefixWord ++ tailWord_3415521).sum := by decide
  have hdescent : baseEnd_3415521 < baseStart_3415521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415541 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 6]
def baseStart_3415541 : Nat := 118140960795 + 3415541 * 2 ^ 59
def prefixEnd_3415541 : Nat := 4983230072969 + 3 ^ 40 * 3415541 * 2
def baseEnd_3415541 : Nat := 194868247570925157092191

theorem tailTrace_3415541 : CollatzResearch.WordTrace tailWord_3415541 prefixEnd_3415541 194868247570925157092191 := by
  unfold tailWord_3415541
  simp only [CollatzResearch.WordTrace]
  refine ⟨124575014519085759806798477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83050009679390506537865651 124575014519085759806798477)
  ·
    refine ⟨46715630444657159927549429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124575014519085759806798477 46715630444657159927549429)
    ·
      refine ⟨4379590354186608743207759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46715630444657159927549429 4379590354186608743207759)
      ·
        refine ⟨6569385531279913114811639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4379590354186608743207759 6569385531279913114811639)
        ·
          refine ⟨9854078296919869672217459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6569385531279913114811639 9854078296919869672217459)
          ·
            refine ⟨14781117445379804508326189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9854078296919869672217459 14781117445379804508326189)
            ·
              refine ⟨5542919042017426690622321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14781117445379804508326189 5542919042017426690622321)
              ·
                refine ⟨4157189281513070017966741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5542919042017426690622321 4157189281513070017966741)
                ·
                  refine ⟨194868247570925157092191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4157189281513070017966741 194868247570925157092191)
                  ·
                    rfl

theorem cell23_3415541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_3415541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415541 prefixEnd_3415541 := by exact prefixLift 3415541
  have htrace : WordTrace (prefixWord ++ tailWord_3415541) baseStart_3415541 baseEnd_3415541 := by
    simpa [prefixWord, tailWord_3415541, baseEnd_3415541] using wordTrace_append hprefix tailTrace_3415541
  have hstable : (prefixWord ++ tailWord_3415541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415541).length < 2 ^ (prefixWord ++ tailWord_3415541).sum := by decide
  have hdescent : baseEnd_3415541 < baseStart_3415541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415585 : List Nat := [1, 2, 3, 2, 2, 4, 1, 3, 1, 1, 3]
def baseStart_3415585 : Nat := 118140960795 + 3415585 * 2 ^ 59
def prefixEnd_3415585 : Nat := 4983230072969 + 3 ^ 40 * 3415585 * 2
def baseEnd_3415585 : Nat := 1753836821287124241679517

theorem tailTrace_3415585 : CollatzResearch.WordTrace tailWord_3415585 prefixEnd_3415585 1753836821287124241679517 := by
  unfold tailWord_3415585
  simp only [CollatzResearch.WordTrace]
  refine ⟨124576619330926355321400209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83051079553950903547600139 124576619330926355321400209)
  ·
    refine ⟨93432464498194766491050157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124576619330926355321400209 93432464498194766491050157)
    ·
      refine ⟨35037174186823037434143809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93432464498194766491050157 35037174186823037434143809)
      ·
        refine ⟨26277880640117278075607857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35037174186823037434143809 26277880640117278075607857)
        ·
          refine ⟨19708410480087958556705893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26277880640117278075607857 19708410480087958556705893)
          ·
            refine ⟨3695326965016492229382355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19708410480087958556705893 3695326965016492229382355)
            ·
              refine ⟨5542990447524738344073533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695326965016492229382355 5542990447524738344073533)
              ·
                refine ⟨2078621417821776879027575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5542990447524738344073533 2078621417821776879027575)
                ·
                  refine ⟨3117932126732665318541363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078621417821776879027575 3117932126732665318541363)
                  ·
                    refine ⟨4676898190098997977812045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3117932126732665318541363 4676898190098997977812045)
                    ·
                      refine ⟨1753836821287124241679517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4676898190098997977812045 1753836821287124241679517)
                      ·
                        rfl

theorem cell23_3415585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_3415585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415585 prefixEnd_3415585 := by exact prefixLift 3415585
  have htrace : WordTrace (prefixWord ++ tailWord_3415585) baseStart_3415585 baseEnd_3415585 := by
    simpa [prefixWord, tailWord_3415585, baseEnd_3415585] using wordTrace_append hprefix tailTrace_3415585
  have hstable : (prefixWord ++ tailWord_3415585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415585).length < 2 ^ (prefixWord ++ tailWord_3415585).sum := by decide
  have hdescent : baseEnd_3415585 < baseStart_3415585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415608 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 3, 2, 2]
def baseStart_3415608 : Nat := 118140960795 + 3415608 * 2 ^ 59
def prefixEnd_3415608 : Nat := 4983230072969 + 3 ^ 40 * 3415608 * 2
def baseEnd_3415608 : Nat := 1753848631342177651691911

theorem tailTrace_3415608 : CollatzResearch.WordTrace tailWord_3415608 prefixEnd_3415608 1753848631342177651691911 := by
  unfold tailWord_3415608
  simp only [CollatzResearch.WordTrace]
  refine ⟨62288729104921515124743739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83051638806562020166324985 62288729104921515124743739)
  ·
    refine ⟨93433093657382272687115609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62288729104921515124743739 93433093657382272687115609)
    ·
      refine ⟨70074820243036704515336707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93433093657382272687115609 70074820243036704515336707)
      ·
        refine ⟨105112230364555056773005061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70074820243036704515336707 105112230364555056773005061)
        ·
          refine ⟨19708543193354073144938449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105112230364555056773005061 19708543193354073144938449)
          ·
            refine ⟨14781407395015554858703837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19708543193354073144938449 14781407395015554858703837)
            ·
              refine ⟨5543027773130833072013939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14781407395015554858703837 5543027773130833072013939)
              ·
                refine ⟨8314541659696249608020909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5543027773130833072013939 8314541659696249608020909)
                ·
                  refine ⟨3117953122386093603007841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8314541659696249608020909 3117953122386093603007841)
                  ·
                    refine ⟨2338464841789570202255881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3117953122386093603007841 2338464841789570202255881)
                    ·
                      refine ⟨1753848631342177651691911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2338464841789570202255881 1753848631342177651691911)
                      ·
                        rfl

theorem cell23_3415608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 3, 2, 2].length) (baseStart_3415608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415608 prefixEnd_3415608 := by exact prefixLift 3415608
  have htrace : WordTrace (prefixWord ++ tailWord_3415608) baseStart_3415608 baseEnd_3415608 := by
    simpa [prefixWord, tailWord_3415608, baseEnd_3415608] using wordTrace_append hprefix tailTrace_3415608
  have hstable : (prefixWord ++ tailWord_3415608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415608).length < 2 ^ (prefixWord ++ tailWord_3415608).sum := by decide
  have hdescent : baseEnd_3415608 < baseStart_3415608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415622 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_3415622 : Nat := 118140960795 + 3415622 * 2 ^ 59
def prefixEnd_3415622 : Nat := 4983230072969 + 3 ^ 40 * 3415622 * 2
def baseEnd_3415622 : Nat := 584618606690446865638949

theorem tailTrace_3415622 : CollatzResearch.WordTrace tailWord_3415622 prefixEnd_3415622 584618606690446865638949 := by
  unfold tailWord_3415622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3893061525993509707515535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83051979221194873760331413 3893061525993509707515535)
  ·
    refine ⟨5839592288990264561273303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3893061525993509707515535 5839592288990264561273303)
    ·
      refine ⟨8759388433485396841909955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5839592288990264561273303 8759388433485396841909955)
      ·
        refine ⟨13139082650228095262864933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8759388433485396841909955 13139082650228095262864933)
        ·
          refine ⟨2463577996917767861787175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13139082650228095262864933 2463577996917767861787175)
          ·
            refine ⟨3695366995376651792680763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463577996917767861787175 3695366995376651792680763)
            ·
              refine ⟨5543050493064977689021145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695366995376651792680763 5543050493064977689021145)
              ·
                refine ⟨4157287869798733266765859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5543050493064977689021145 4157287869798733266765859)
                ·
                  refine ⟨6235931804698099900148789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4157287869798733266765859 6235931804698099900148789)
                  ·
                    refine ⟨584618606690446865638949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6235931804698099900148789 584618606690446865638949)
                    ·
                      rfl

theorem cell23_3415622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_3415622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415622 prefixEnd_3415622 := by exact prefixLift 3415622
  have htrace : WordTrace (prefixWord ++ tailWord_3415622) baseStart_3415622 baseEnd_3415622 := by
    simpa [prefixWord, tailWord_3415622, baseEnd_3415622] using wordTrace_append hprefix tailTrace_3415622
  have hstable : (prefixWord ++ tailWord_3415622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415622).length < 2 ^ (prefixWord ++ tailWord_3415622).sum := by decide
  have hdescent : baseEnd_3415622 < baseStart_3415622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415628 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 1, 2, 3]
def baseStart_3415628 : Nat := 118140960795 + 3415628 * 2 ^ 59
def prefixEnd_3415628 : Nat := 4983230072969 + 3 ^ 40 * 3415628 * 2
def baseEnd_3415628 : Nat := 1753858900955267573441819

theorem tailTrace_3415628 : CollatzResearch.WordTrace tailWord_3415628 prefixEnd_3415628 1753858900955267573441819 := by
  unfold tailWord_3415628
  simp only [CollatzResearch.WordTrace]
  refine ⟨62289093834885286832607769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83052125113180382443477025 62289093834885286832607769)
  ·
    refine ⟨46716820376163965124455827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62289093834885286832607769 46716820376163965124455827)
    ·
      refine ⟨70075230564245947686683741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46716820376163965124455827 70075230564245947686683741)
      ·
        refine ⟨26278211461592230382506403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70075230564245947686683741 26278211461592230382506403)
        ·
          refine ⟨39417317192388345573759605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26278211461592230382506403 39417317192388345573759605)
          ·
            refine ⟨3695373486786407397539963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39417317192388345573759605 3695373486786407397539963)
            ·
              refine ⟨5543060230179611096309945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695373486786407397539963 5543060230179611096309945)
              ·
                refine ⟨4157295172634708322232459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5543060230179611096309945 4157295172634708322232459)
                ·
                  refine ⟨6235942758952062483348689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4157295172634708322232459 6235942758952062483348689)
                  ·
                    refine ⟨4676957069214046862511517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6235942758952062483348689 4676957069214046862511517)
                    ·
                      refine ⟨1753858900955267573441819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4676957069214046862511517 1753858900955267573441819)
                      ·
                        rfl

theorem cell23_3415628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_3415628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415628 prefixEnd_3415628 := by exact prefixLift 3415628
  have htrace : WordTrace (prefixWord ++ tailWord_3415628) baseStart_3415628 baseEnd_3415628 := by
    simpa [prefixWord, tailWord_3415628, baseEnd_3415628] using wordTrace_append hprefix tailTrace_3415628
  have hstable : (prefixWord ++ tailWord_3415628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415628).length < 2 ^ (prefixWord ++ tailWord_3415628).sum := by decide
  have hdescent : baseEnd_3415628 < baseStart_3415628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415645 : List Nat := [1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_3415645 : Nat := 118140960795 + 3415645 * 2 ^ 59
def prefixEnd_3415645 : Nat := 4983230072969 + 3 ^ 40 * 3415645 * 2
def baseEnd_3415645 : Nat := 1753867630126394006929241

theorem tailTrace_3415645 : CollatzResearch.WordTrace tailWord_3415645 prefixEnd_3415645 1753867630126394006929241 := by
  unfold tailWord_3415645
  simp only [CollatzResearch.WordTrace]
  refine ⟨124578807710708985568584389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83052538473805990379056259 124578807710708985568584389)
  ·
    refine ⟨23358526445757934794109573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124578807710708985568584389 23358526445757934794109573)
    ·
      refine ⟨4379723708579612773895545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23358526445757934794109573 4379723708579612773895545)
      ·
        refine ⟨3284792781434709580421659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4379723708579612773895545 3284792781434709580421659)
        ·
          refine ⟨4927189172152064370632489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284792781434709580421659 4927189172152064370632489)
          ·
            refine ⟨3695391879114048277974367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4927189172152064370632489 3695391879114048277974367)
            ·
              refine ⟨5543087818671072416961551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695391879114048277974367 5543087818671072416961551)
              ·
                refine ⟨8314631728006608625442327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5543087818671072416961551 8314631728006608625442327)
                ·
                  refine ⟨12471947592009912938163491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8314631728006608625442327 12471947592009912938163491)
                  ·
                    refine ⟨18707921388014869407245237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12471947592009912938163491 18707921388014869407245237)
                    ·
                      refine ⟨1753867630126394006929241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18707921388014869407245237 1753867630126394006929241)
                      ·
                        rfl

theorem cell23_3415645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_3415645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415645 prefixEnd_3415645 := by exact prefixLift 3415645
  have htrace : WordTrace (prefixWord ++ tailWord_3415645) baseStart_3415645 baseEnd_3415645 := by
    simpa [prefixWord, tailWord_3415645, baseEnd_3415645] using wordTrace_append hprefix tailTrace_3415645
  have hstable : (prefixWord ++ tailWord_3415645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415645).length < 2 ^ (prefixWord ++ tailWord_3415645).sum := by decide
  have hdescent : baseEnd_3415645 < baseStart_3415645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415658 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_3415658 : Nat := 118140960795 + 3415658 * 2 ^ 59
def prefixEnd_3415658 : Nat := 4983230072969 + 3 ^ 40 * 3415658 * 2
def baseEnd_3415658 : Nat := 1753874305374902456066681

theorem tailTrace_3415658 : CollatzResearch.WordTrace tailWord_3415658 prefixEnd_3415658 1753874305374902456066681 := by
  unfold tailWord_3415658
  simp only [CollatzResearch.WordTrace]
  refine ⟨31144820464915472197201907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83052854573107925859205085 31144820464915472197201907)
  ·
    refine ⟨46717230697373208295802861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31144820464915472197201907 46717230697373208295802861)
    ·
      refine ⟨17518961511514953110926073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46717230697373208295802861 17518961511514953110926073)
      ·
        refine ⟨13139221133636214833194555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17518961511514953110926073 13139221133636214833194555)
        ·
          refine ⟨19708831700454322249791833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13139221133636214833194555 19708831700454322249791833)
          ·
            refine ⟨14781623775340741687343875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19708831700454322249791833 14781623775340741687343875)
            ·
              refine ⟨22172435663011112531015813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14781623775340741687343875 22172435663011112531015813)
              ·
                refine ⟨4157331686814583599565465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22172435663011112531015813 4157331686814583599565465)
                ·
                  refine ⟨3117998765110937699674099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4157331686814583599565465 3117998765110937699674099)
                  ·
                    refine ⟨4676998147666406549511149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3117998765110937699674099 4676998147666406549511149)
                    ·
                      refine ⟨1753874305374902456066681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4676998147666406549511149 1753874305374902456066681)
                      ·
                        rfl

theorem cell23_3415658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_3415658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415658 prefixEnd_3415658 := by exact prefixLift 3415658
  have htrace : WordTrace (prefixWord ++ tailWord_3415658) baseStart_3415658 baseEnd_3415658 := by
    simpa [prefixWord, tailWord_3415658, baseEnd_3415658] using wordTrace_append hprefix tailTrace_3415658
  have hstable : (prefixWord ++ tailWord_3415658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415658).length < 2 ^ (prefixWord ++ tailWord_3415658).sum := by decide
  have hdescent : baseEnd_3415658 < baseStart_3415658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415664 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 4]
def baseStart_3415664 : Nat := 118140960795 + 3415664 * 2 ^ 59
def prefixEnd_3415664 : Nat := 4983230072969 + 3 ^ 40 * 3415664 * 2
def baseEnd_3415664 : Nat := 1753877386258829432591653

theorem tailTrace_3415664 : CollatzResearch.WordTrace tailWord_3415664 prefixEnd_3415664 1753877386258829432591653 := by
  unfold tailWord_3415664
  simp only [CollatzResearch.WordTrace]
  refine ⟨62289750348820075906763023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83053000465093434542350697 62289750348820075906763023)
  ·
    refine ⟨93434625523230113860144535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62289750348820075906763023 93434625523230113860144535)
    ·
      refine ⟨140151938284845170790216803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93434625523230113860144535 140151938284845170790216803)
      ·
        refine ⟨210227907427267756185325205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140151938284845170790216803 210227907427267756185325205)
        ·
          refine ⟨9854433160653176071187119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 210227907427267756185325205 9854433160653176071187119)
          ·
            refine ⟨14781649740979764106780679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9854433160653176071187119 14781649740979764106780679)
            ·
              refine ⟨22172474611469646160171019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14781649740979764106780679 22172474611469646160171019)
              ·
                refine ⟨33258711917204469240256529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22172474611469646160171019 33258711917204469240256529)
                ·
                  refine ⟨24944033937903351930192397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33258711917204469240256529 24944033937903351930192397)
                  ·
                    refine ⟨9354012726713756973822149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24944033937903351930192397 9354012726713756973822149)
                    ·
                      refine ⟨1753877386258829432591653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9354012726713756973822149 1753877386258829432591653)
                      ·
                        rfl

theorem cell23_3415664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_3415664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415664 prefixEnd_3415664 := by exact prefixLift 3415664
  have htrace : WordTrace (prefixWord ++ tailWord_3415664) baseStart_3415664 baseEnd_3415664 := by
    simpa [prefixWord, tailWord_3415664, baseEnd_3415664] using wordTrace_append hprefix tailTrace_3415664
  have hstable : (prefixWord ++ tailWord_3415664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415664).length < 2 ^ (prefixWord ++ tailWord_3415664).sum := by decide
  have hdescent : baseEnd_3415664 < baseStart_3415664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415772 : List Nat := [2, 2, 5, 1, 2, 1, 3, 2, 5]
def baseStart_3415772 : Nat := 118140960795 + 3415772 * 2 ^ 59
def prefixEnd_3415772 : Nat := 4983230072969 + 3 ^ 40 * 3415772 * 2
def baseEnd_3415772 : Nat := 194881426907723890004573

theorem tailTrace_3415772 : CollatzResearch.WordTrace tailWord_3415772 prefixEnd_3415772 194881426907723890004573 := by
  unfold tailWord_3415772
  simp only [CollatzResearch.WordTrace]
  refine ⟨62291719890624443129228785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83055626520832590838971713 62291719890624443129228785)
  ·
    refine ⟨46718789917968332346921589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62291719890624443129228785 46718789917968332346921589)
    ·
      refine ⟨4379886554809531157523899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46718789917968332346921589 4379886554809531157523899)
      ·
        refine ⟨6569829832214296736285849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4379886554809531157523899 6569829832214296736285849)
        ·
          refine ⟨4927372374160722552214387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6569829832214296736285849 4927372374160722552214387)
          ·
            refine ⟨7391058561241083828321581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4927372374160722552214387 7391058561241083828321581)
            ·
              refine ⟨2771646960465406435620593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7391058561241083828321581 2771646960465406435620593)
              ·
                refine ⟨2078735220349054826715445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2771646960465406435620593 2078735220349054826715445)
                ·
                  refine ⟨194881426907723890004573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2078735220349054826715445 194881426907723890004573)
                  ·
                    rfl

theorem cell23_3415772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_3415772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415772 prefixEnd_3415772 := by exact prefixLift 3415772
  have htrace : WordTrace (prefixWord ++ tailWord_3415772) baseStart_3415772 baseEnd_3415772 := by
    simpa [prefixWord, tailWord_3415772, baseEnd_3415772] using wordTrace_append hprefix tailTrace_3415772
  have hstable : (prefixWord ++ tailWord_3415772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415772).length < 2 ^ (prefixWord ++ tailWord_3415772).sum := by decide
  have hdescent : baseEnd_3415772 < baseStart_3415772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415791 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 3]
def baseStart_3415791 : Nat := 118140960795 + 3415791 * 2 ^ 59
def prefixEnd_3415791 : Nat := 4983230072969 + 3 ^ 40 * 3415791 * 2
def baseEnd_3415791 : Nat := 1753942598301950435703569

theorem tailTrace_3415791 : CollatzResearch.WordTrace tailWord_3415791 prefixEnd_3415791 1753942598301950435703569 := by
  unfold tailWord_3415791
  simp only [CollatzResearch.WordTrace]
  refine ⟨124584132768180052503399227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83056088512120035002266151 124584132768180052503399227)
  ·
    refine ⟨186876199152270078755098841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124584132768180052503399227 186876199152270078755098841)
    ·
      refine ⟨140157149364202559066324131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186876199152270078755098841 140157149364202559066324131)
      ·
        refine ⟨210235724046303838599486197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140157149364202559066324131 210235724046303838599486197)
        ·
          refine ⟨19709599129340984868701831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210235724046303838599486197 19709599129340984868701831)
          ·
            refine ⟨29564398694011477303052747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19709599129340984868701831 29564398694011477303052747)
            ·
              refine ⟨44346598041017215954579121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29564398694011477303052747 44346598041017215954579121)
              ·
                refine ⟨33259948530762911965934341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44346598041017215954579121 33259948530762911965934341)
                ·
                  refine ⟨6236240349518045993612689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33259948530762911965934341 6236240349518045993612689)
                  ·
                    refine ⟨4677180262138534495209517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6236240349518045993612689 4677180262138534495209517)
                    ·
                      refine ⟨1753942598301950435703569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4677180262138534495209517 1753942598301950435703569)
                      ·
                        rfl

theorem cell23_3415791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 2, 3].length) (baseStart_3415791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415791 prefixEnd_3415791 := by exact prefixLift 3415791
  have htrace : WordTrace (prefixWord ++ tailWord_3415791) baseStart_3415791 baseEnd_3415791 := by
    simpa [prefixWord, tailWord_3415791, baseEnd_3415791] using wordTrace_append hprefix tailTrace_3415791
  have hstable : (prefixWord ++ tailWord_3415791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415791).length < 2 ^ (prefixWord ++ tailWord_3415791).sum := by decide
  have hdescent : baseEnd_3415791 < baseStart_3415791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415841 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 3, 5]
def baseStart_3415841 : Nat := 118140960795 + 3415841 * 2 ^ 59
def prefixEnd_3415841 : Nat := 4983230072969 + 3 ^ 40 * 3415841 * 2
def baseEnd_3415841 : Nat := 584656090778225080026113

theorem tailTrace_3415841 : CollatzResearch.WordTrace tailWord_3415841 prefixEnd_3415841 584656090778225080026113 := by
  unfold tailWord_3415841
  simp only [CollatzResearch.WordTrace]
  refine ⟨124585956417998911042719377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83057304278665940695146251 124585956417998911042719377)
  ·
    refine ⟨93439467313499183282039533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124585956417998911042719377 93439467313499183282039533)
    ·
      refine ⟨35039800242562193730764825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93439467313499183282039533 35039800242562193730764825)
      ·
        refine ⟨26279850181921645298073619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35039800242562193730764825 26279850181921645298073619)
        ·
          refine ⟨39419775272882467947110429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26279850181921645298073619 39419775272882467947110429)
          ·
            refine ⟨14782415727330925480166411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39419775272882467947110429 14782415727330925480166411)
            ·
              refine ⟨22173623590996388220249617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14782415727330925480166411 22173623590996388220249617)
              ·
                refine ⟨16630217693247291165187213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22173623590996388220249617 16630217693247291165187213)
                ·
                  refine ⟨6236331634967734186945205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16630217693247291165187213 6236331634967734186945205)
                  ·
                    refine ⟨584656090778225080026113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6236331634967734186945205 584656090778225080026113)
                    ·
                      rfl

theorem cell23_3415841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_3415841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415841 prefixEnd_3415841 := by exact prefixLift 3415841
  have htrace : WordTrace (prefixWord ++ tailWord_3415841) baseStart_3415841 baseEnd_3415841 := by
    simpa [prefixWord, tailWord_3415841, baseEnd_3415841] using wordTrace_append hprefix tailTrace_3415841
  have hstable : (prefixWord ++ tailWord_3415841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415841).length < 2 ^ (prefixWord ++ tailWord_3415841).sum := by decide
  have hdescent : baseEnd_3415841 < baseStart_3415841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415875 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 1, 5]
def baseStart_3415875 : Nat := 118140960795 + 3415875 * 2 ^ 59
def prefixEnd_3415875 : Nat := 4983230072969 + 3 ^ 40 * 3415875 * 2
def baseEnd_3415875 : Nat := 584661910225642702351061

theorem tailTrace_3415875 : CollatzResearch.WordTrace tailWord_3415875 prefixEnd_3415875 584661910225642702351061 := by
  unfold tailWord_3415875
  simp only [CollatzResearch.WordTrace]
  refine ⟨124587196499875734849457079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83058130999917156566304719 124587196499875734849457079)
  ·
    refine ⟨186880794749813602274185619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124587196499875734849457079 186880794749813602274185619)
    ·
      refine ⟨280321192124720403411278429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186880794749813602274185619 280321192124720403411278429)
      ·
        refine ⟨105120447046770151279229411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280321192124720403411278429 105120447046770151279229411)
        ·
          refine ⟨157680670570155226918844117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105120447046770151279229411 157680670570155226918844117)
          ·
            refine ⟨3695640716488013130910409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 157680670570155226918844117 3695640716488013130910409)
            ·
              refine ⟨2771730537366009848182807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3695640716488013130910409 2771730537366009848182807)
              ·
                refine ⟨4157595806049014772274211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771730537366009848182807 4157595806049014772274211)
                ·
                  refine ⟨6236393709073522158411317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4157595806049014772274211 6236393709073522158411317)
                  ·
                    refine ⟨584661910225642702351061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6236393709073522158411317 584661910225642702351061)
                    ·
                      rfl

theorem cell23_3415875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 1, 5].length) (baseStart_3415875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415875 prefixEnd_3415875 := by exact prefixLift 3415875
  have htrace : WordTrace (prefixWord ++ tailWord_3415875) baseStart_3415875 baseEnd_3415875 := by
    simpa [prefixWord, tailWord_3415875, baseEnd_3415875] using wordTrace_append hprefix tailTrace_3415875
  have hstable : (prefixWord ++ tailWord_3415875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415875).length < 2 ^ (prefixWord ++ tailWord_3415875).sum := by decide
  have hdescent : baseEnd_3415875 < baseStart_3415875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415881 : List Nat := [1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 5]
def baseStart_3415881 : Nat := 118140960795 + 3415881 * 2 ^ 59
def prefixEnd_3415881 : Nat := 4983230072969 + 3 ^ 40 * 3415881 * 2
def baseEnd_3415881 : Nat := 1753988811560855083578155

theorem tailTrace_3415881 : CollatzResearch.WordTrace tailWord_3415881 prefixEnd_3415881 1753988811560855083578155 := by
  unfold tailWord_3415881
  simp only [CollatzResearch.WordTrace]
  refine ⟨124587415337853997874175497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83058276891902665249450331 124587415337853997874175497)
  ·
    refine ⟨93440561503390498405631623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124587415337853997874175497 93440561503390498405631623)
    ·
      refine ⟨140160842255085747608447435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93440561503390498405631623 140160842255085747608447435)
      ·
        refine ⟨210241263382628621412671153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140160842255085747608447435 210241263382628621412671153)
        ·
          refine ⟨157680947536971466059503365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210241263382628621412671153 157680947536971466059503365)
          ·
            refine ⟨29565177663182149886156881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157680947536971466059503365 29565177663182149886156881)
            ·
              refine ⟨22173883247386612414617661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29565177663182149886156881 22173883247386612414617661)
              ·
                refine ⟨8315206217769979655481623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22173883247386612414617661 8315206217769979655481623)
                ·
                  refine ⟨12472809326654969483222435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8315206217769979655481623 12472809326654969483222435)
                  ·
                    refine ⟨18709213989982454224833653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12472809326654969483222435 18709213989982454224833653)
                    ·
                      refine ⟨1753988811560855083578155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18709213989982454224833653 1753988811560855083578155)
                      ·
                        rfl

theorem cell23_3415881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_3415881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415881 prefixEnd_3415881 := by exact prefixLift 3415881
  have htrace : WordTrace (prefixWord ++ tailWord_3415881) baseStart_3415881 baseEnd_3415881 := by
    simpa [prefixWord, tailWord_3415881, baseEnd_3415881] using wordTrace_append hprefix tailTrace_3415881
  have hstable : (prefixWord ++ tailWord_3415881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415881).length < 2 ^ (prefixWord ++ tailWord_3415881).sum := by decide
  have hdescent : baseEnd_3415881 < baseStart_3415881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415905 : List Nat := [1, 2, 3, 1, 1, 1, 7, 1, 2, 4]
def baseStart_3415905 : Nat := 118140960795 + 3415905 * 2 ^ 59
def prefixEnd_3415905 : Nat := 4983230072969 + 3 ^ 40 * 3415905 * 2
def baseEnd_3415905 : Nat := 584667045032187663226015

theorem tailTrace_3415905 : CollatzResearch.WordTrace tailWord_3415905 prefixEnd_3415905 584667045032187663226015 := by
  unfold tailWord_3415905
  simp only [CollatzResearch.WordTrace]
  refine ⟨124588290689767049973049169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83058860459844699982032779 124588290689767049973049169)
  ·
    refine ⟨93441218017325287479786877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124588290689767049973049169 93441218017325287479786877)
    ·
      refine ⟨35040456756496982804920079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93441218017325287479786877 35040456756496982804920079)
      ·
        refine ⟨52560685134745474207380119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35040456756496982804920079 52560685134745474207380119)
        ·
          refine ⟨78841027702118211311070179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52560685134745474207380119 78841027702118211311070179)
          ·
            refine ⟨118261541553177316966605269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78841027702118211311070179 118261541553177316966605269)
            ·
              refine ⟨2771754880152593366404811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 118261541553177316966605269 2771754880152593366404811)
              ·
                refine ⟨4157632320228890049607217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771754880152593366404811 4157632320228890049607217)
                ·
                  refine ⟨3118224240171667537205413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4157632320228890049607217 3118224240171667537205413)
                  ·
                    refine ⟨584667045032187663226015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3118224240171667537205413 584667045032187663226015)
                    ·
                      rfl

theorem cell23_3415905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_3415905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415905 prefixEnd_3415905 := by exact prefixLift 3415905
  have htrace : WordTrace (prefixWord ++ tailWord_3415905) baseStart_3415905 baseEnd_3415905 := by
    simpa [prefixWord, tailWord_3415905, baseEnd_3415905] using wordTrace_append hprefix tailTrace_3415905
  have hstable : (prefixWord ++ tailWord_3415905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415905).length < 2 ^ (prefixWord ++ tailWord_3415905).sum := by decide
  have hdescent : baseEnd_3415905 < baseStart_3415905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415908 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_3415908 : Nat := 118140960795 + 3415908 * 2 ^ 59
def prefixEnd_3415908 : Nat := 4983230072969 + 3 ^ 40 * 3415908 * 2
def baseEnd_3415908 : Nat := 1754002675538526477940531

theorem tailTrace_3415908 : CollatzResearch.WordTrace tailWord_3415908 prefixEnd_3415908 1754002675538526477940531 := by
  unfold tailWord_3415908
  simp only [CollatzResearch.WordTrace]
  refine ⟨62294200054378090742704189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83058933405837454323605585 62294200054378090742704189)
  ·
    refine ⟨23360325020391784028514071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62294200054378090742704189 23360325020391784028514071)
    ·
      refine ⟨35040487530587676042771107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23360325020391784028514071 35040487530587676042771107)
      ·
        refine ⟨52560731295881514064156661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35040487530587676042771107 52560731295881514064156661)
        ·
          refine ⟨4927568558988891943514687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52560731295881514064156661 4927568558988891943514687)
          ·
            refine ⟨7391352838483337915272031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4927568558988891943514687 7391352838483337915272031)
            ·
              refine ⟨11087029257725006872908047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7391352838483337915272031 11087029257725006872908047)
              ·
                refine ⟨16630543886587510309362071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11087029257725006872908047 16630543886587510309362071)
                ·
                  refine ⟨24945815829881265464043107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16630543886587510309362071 24945815829881265464043107)
                  ·
                    refine ⟨37418723744821898196064661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24945815829881265464043107 37418723744821898196064661)
                    ·
                      refine ⟨1754002675538526477940531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37418723744821898196064661 1754002675538526477940531)
                      ·
                        rfl

theorem cell23_3415908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_3415908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415908 prefixEnd_3415908 := by exact prefixLift 3415908
  have htrace : WordTrace (prefixWord ++ tailWord_3415908) baseStart_3415908 baseEnd_3415908 := by
    simpa [prefixWord, tailWord_3415908, baseEnd_3415908] using wordTrace_append hprefix tailTrace_3415908
  have hstable : (prefixWord ++ tailWord_3415908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415908).length < 2 ^ (prefixWord ++ tailWord_3415908).sum := by decide
  have hdescent : baseEnd_3415908 < baseStart_3415908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415918 : List Nat := [4, 1, 2, 3, 1, 2, 1, 9]
def baseStart_3415918 : Nat := 118140960795 + 3415918 * 2 ^ 59
def prefixEnd_3415918 : Nat := 4983230072969 + 3 ^ 40 * 3415918 * 2
def baseEnd_3415918 : Nat := 64963252235002645882055

theorem tailTrace_3415918 : CollatzResearch.WordTrace tailWord_3415918 prefixEnd_3415918 64963252235002645882055 := by
  unfold tailWord_3415918
  simp only [CollatzResearch.WordTrace]
  refine ⟨15573595604839994149159051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83059176559146635462181605 15573595604839994149159051)
  ·
    refine ⟨23360393407259991223738577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15573595604839994149159051 23360393407259991223738577)
    ·
      refine ⟨17520295055444993417803933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23360393407259991223738577 17520295055444993417803933)
      ·
        refine ⟨6570110645791872531676475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17520295055444993417803933 6570110645791872531676475)
        ·
          refine ⟨9855165968687808797514713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6570110645791872531676475 9855165968687808797514713)
          ·
            refine ⟨7391374476515856598136035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9855165968687808797514713 7391374476515856598136035)
            ·
              refine ⟨11087061714773784897204053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7391374476515856598136035 11087061714773784897204053)
              ·
                refine ⟨64963252235002645882055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11087061714773784897204053 64963252235002645882055)
                ·
                  rfl

theorem cell23_3415918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_3415918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415918 prefixEnd_3415918 := by exact prefixLift 3415918
  have htrace : WordTrace (prefixWord ++ tailWord_3415918) baseStart_3415918 baseEnd_3415918 := by
    simpa [prefixWord, tailWord_3415918, baseEnd_3415918] using wordTrace_append hprefix tailTrace_3415918
  have hstable : (prefixWord ++ tailWord_3415918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415918).length < 2 ^ (prefixWord ++ tailWord_3415918).sum := by decide
  have hdescent : baseEnd_3415918 < baseStart_3415918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415941 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_3415941 : Nat := 118140960795 + 3415941 * 2 ^ 59
def prefixEnd_3415941 : Nat := 4983230072969 + 3 ^ 40 * 3415941 * 2
def baseEnd_3415941 : Nat := 1754019620400124848827879

theorem tailTrace_3415941 : CollatzResearch.WordTrace tailWord_3415941 prefixEnd_3415941 1754019620400124848827879 := by
  unfold tailWord_3415941
  simp only [CollatzResearch.WordTrace]
  refine ⟨124589603717636628121359677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83059735811757752080906451 124589603717636628121359677)
  ·
    refine ⟨46721101394113735545509879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124589603717636628121359677 46721101394113735545509879)
    ·
      refine ⟨70081652091170603318264819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46721101394113735545509879 70081652091170603318264819)
      ·
        refine ⟨105122478136755904977397229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70081652091170603318264819 105122478136755904977397229)
        ·
          refine ⟨39420929301283464366523961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105122478136755904977397229 39420929301283464366523961)
          ·
            refine ⟨29565696975962598274892971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39420929301283464366523961 29565696975962598274892971)
            ·
              refine ⟨44348545463943897412339457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29565696975962598274892971 44348545463943897412339457)
              ·
                refine ⟨33261409097957923059254593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44348545463943897412339457 33261409097957923059254593)
                ·
                  refine ⟨24946056823468442294440945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33261409097957923059254593 24946056823468442294440945)
                  ·
                    refine ⟨18709542617601331720830709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24946056823468442294440945 18709542617601331720830709)
                    ·
                      refine ⟨1754019620400124848827879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18709542617601331720830709 1754019620400124848827879)
                      ·
                        rfl

theorem cell23_3415941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_3415941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415941 prefixEnd_3415941 := by exact prefixLift 3415941
  have htrace : WordTrace (prefixWord ++ tailWord_3415941) baseStart_3415941 baseEnd_3415941 := by
    simpa [prefixWord, tailWord_3415941, baseEnd_3415941] using wordTrace_append hprefix tailTrace_3415941
  have hstable : (prefixWord ++ tailWord_3415941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415941).length < 2 ^ (prefixWord ++ tailWord_3415941).sum := by decide
  have hdescent : baseEnd_3415941 < baseStart_3415941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415945 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 2, 1, 3]
def baseStart_3415945 : Nat := 118140960795 + 3415945 * 2 ^ 59
def prefixEnd_3415945 : Nat := 4983230072969 + 3 ^ 40 * 3415945 * 2
def baseEnd_3415945 : Nat := 1754021674322742833177861

theorem tailTrace_3415945 : CollatzResearch.WordTrace tailWord_3415945 prefixEnd_3415945 1754021674322742833177861 := by
  unfold tailWord_3415945
  simp only [CollatzResearch.WordTrace]
  refine ⟨124589749609622136804505289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83059833073081424536336859 124589749609622136804505289)
  ·
    refine ⟨93442312207216602603378967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124589749609622136804505289 93442312207216602603378967)
    ·
      refine ⟨140163468310824903905068451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93442312207216602603378967 140163468310824903905068451)
      ·
        refine ⟨210245202466237355857602677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140163468310824903905068451 210245202466237355857602677)
        ·
          refine ⟨19710487731209752111650251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210245202466237355857602677 19710487731209752111650251)
          ·
            refine ⟨29565731596814628167475377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19710487731209752111650251 29565731596814628167475377)
            ·
              refine ⟨22174298697610971125606533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29565731596814628167475377 22174298697610971125606533)
              ·
                refine ⟨4157681005802057086051225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22174298697610971125606533 4157681005802057086051225)
                ·
                  refine ⟨3118260754351542814538419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4157681005802057086051225 3118260754351542814538419)
                  ·
                    refine ⟨4677391131527314221807629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3118260754351542814538419 4677391131527314221807629)
                    ·
                      refine ⟨1754021674322742833177861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4677391131527314221807629 1754021674322742833177861)
                      ·
                        rfl

theorem cell23_3415945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 1, 3].length) (baseStart_3415945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415945 prefixEnd_3415945 := by exact prefixLift 3415945
  have htrace : WordTrace (prefixWord ++ tailWord_3415945) baseStart_3415945 baseEnd_3415945 := by
    simpa [prefixWord, tailWord_3415945, baseEnd_3415945] using wordTrace_append hprefix tailTrace_3415945
  have hstable : (prefixWord ++ tailWord_3415945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415945).length < 2 ^ (prefixWord ++ tailWord_3415945).sum := by decide
  have hdescent : baseEnd_3415945 < baseStart_3415945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415946 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2]
def baseStart_3415946 : Nat := 118140960795 + 3415946 * 2 ^ 59
def prefixEnd_3415946 : Nat := 4983230072969 + 3 ^ 40 * 3415946 * 2
def baseEnd_3415946 : Nat := 1754022187803397329265357

theorem tailTrace_3415946 : CollatzResearch.WordTrace tailWord_3415946 prefixEnd_3415946 1754022187803397329265357 := by
  unfold tailWord_3415946
  simp only [CollatzResearch.WordTrace]
  refine ⟨31147446520654628493822923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83059857388412342650194461 31147446520654628493822923)
  ·
    refine ⟨46721169780981942740734385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31147446520654628493822923 46721169780981942740734385)
    ·
      refine ⟨35040877335736457055550789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46721169780981942740734385 35040877335736457055550789)
      ·
        refine ⟨6570164500450585697915773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35040877335736457055550789 6570164500450585697915773)
        ·
          refine ⟨2463811687668969636718415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6570164500450585697915773 2463811687668969636718415)
          ·
            refine ⟨3695717531503454455077623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2463811687668969636718415 3695717531503454455077623)
            ·
              refine ⟨5543576297255181682616435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695717531503454455077623 5543576297255181682616435)
              ·
                refine ⟨8315364445882772523924653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5543576297255181682616435 8315364445882772523924653)
                ·
                  refine ⟨3118261667206039696471745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8315364445882772523924653 3118261667206039696471745)
                  ·
                    refine ⟨2338696250404529772353809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3118261667206039696471745 2338696250404529772353809)
                    ·
                      refine ⟨1754022187803397329265357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2338696250404529772353809 1754022187803397329265357)
                      ·
                        rfl

theorem cell23_3415946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_3415946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415946 prefixEnd_3415946 := by exact prefixLift 3415946
  have htrace : WordTrace (prefixWord ++ tailWord_3415946) baseStart_3415946 baseEnd_3415946 := by
    simpa [prefixWord, tailWord_3415946, baseEnd_3415946] using wordTrace_append hprefix tailTrace_3415946
  have hstable : (prefixWord ++ tailWord_3415946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415946).length < 2 ^ (prefixWord ++ tailWord_3415946).sum := by decide
  have hdescent : baseEnd_3415946 < baseStart_3415946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415961 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 2, 6]
def baseStart_3415961 : Nat := 118140960795 + 3415961 * 2 ^ 59
def prefixEnd_3415961 : Nat := 4983230072969 + 3 ^ 40 * 3415961 * 2
def baseEnd_3415961 : Nat := 584676630004404923525929

theorem tailTrace_3415961 : CollatzResearch.WordTrace tailWord_3415961 prefixEnd_3415961 584676630004404923525929 := by
  unfold tailWord_3415961
  simp only [CollatzResearch.WordTrace]
  refine ⟨124590333177564171537087737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83060222118376114358058491 124590333177564171537087737)
  ·
    refine ⟨93442749883173128652815803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124590333177564171537087737 93442749883173128652815803)
    ·
      refine ⟨140164124824759692979223705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93442749883173128652815803 140164124824759692979223705)
      ·
        refine ⟨105123093618569769734417779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140164124824759692979223705 105123093618569769734417779)
        ·
          refine ⟨157684640427854654601626669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105123093618569769734417779 157684640427854654601626669)
          ·
            refine ⟨59131740160445495475610001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157684640427854654601626669 59131740160445495475610001)
            ·
              refine ⟨44348805120334121606707501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59131740160445495475610001 44348805120334121606707501)
              ·
                refine ⟨16630801920125295602515313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44348805120334121606707501 16630801920125295602515313)
                ·
                  refine ⟨12473101440093971701886485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16630801920125295602515313 12473101440093971701886485)
                  ·
                    refine ⟨584676630004404923525929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12473101440093971701886485 584676630004404923525929)
                    ·
                      rfl

theorem cell23_3415961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_3415961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415961 prefixEnd_3415961 := by exact prefixLift 3415961
  have htrace : WordTrace (prefixWord ++ tailWord_3415961) baseStart_3415961 baseEnd_3415961 := by
    simpa [prefixWord, tailWord_3415961, baseEnd_3415961] using wordTrace_append hprefix tailTrace_3415961
  have hstable : (prefixWord ++ tailWord_3415961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415961).length < 2 ^ (prefixWord ++ tailWord_3415961).sum := by decide
  have hdescent : baseEnd_3415961 < baseStart_3415961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415962 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3415962 : Nat := 118140960795 + 3415962 * 2 ^ 59
def prefixEnd_3415962 : Nat := 4983230072969 + 3 ^ 40 * 3415962 * 2
def baseEnd_3415962 : Nat := 1754030403493869266665283

theorem tailTrace_3415962 : CollatzResearch.WordTrace tailWord_3415962 prefixEnd_3415962 1754030403493869266665283 := by
  unfold tailWord_3415962
  simp only [CollatzResearch.WordTrace]
  refine ⟨31147592412640137176968535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83060246433707032471916093 31147592412640137176968535)
  ·
    refine ⟨46721388618960205765452803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31147592412640137176968535 46721388618960205765452803)
    ·
      refine ⟨70082082928440308648179205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46721388618960205765452803 70082082928440308648179205)
      ·
        refine ⟨13140390549082557871533601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70082082928440308648179205 13140390549082557871533601)
        ·
          refine ⟨9855292911811918403650201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13140390549082557871533601 9855292911811918403650201)
          ·
            refine ⟨7391469683858938802737651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9855292911811918403650201 7391469683858938802737651)
            ·
              refine ⟨11087204525788408204106477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7391469683858938802737651 11087204525788408204106477)
              ·
                refine ⟨4157701697170653076539929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11087204525788408204106477 4157701697170653076539929)
                ·
                  refine ⟨3118276272877989807404947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4157701697170653076539929 3118276272877989807404947)
                  ·
                    refine ⟨4677414409316984711107421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3118276272877989807404947 4677414409316984711107421)
                    ·
                      refine ⟨1754030403493869266665283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4677414409316984711107421 1754030403493869266665283)
                      ·
                        rfl

theorem cell23_3415962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3415962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415962 prefixEnd_3415962 := by exact prefixLift 3415962
  have htrace : WordTrace (prefixWord ++ tailWord_3415962) baseStart_3415962 baseEnd_3415962 := by
    simpa [prefixWord, tailWord_3415962, baseEnd_3415962] using wordTrace_append hprefix tailTrace_3415962
  have hstable : (prefixWord ++ tailWord_3415962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415962).length < 2 ^ (prefixWord ++ tailWord_3415962).sum := by decide
  have hdescent : baseEnd_3415962 < baseStart_3415962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415966 : List Nat := [4, 3, 1, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_3415966 : Nat := 118140960795 + 3415966 * 2 ^ 59
def prefixEnd_3415966 : Nat := 4983230072969 + 3 ^ 40 * 3415966 * 2
def baseEnd_3415966 : Nat := 1754032457416487251015265

theorem tailTrace_3415966 : CollatzResearch.WordTrace tailWord_3415966 prefixEnd_3415966 1754032457416487251015265 := by
  unfold tailWord_3415966
  simp only [CollatzResearch.WordTrace]
  refine ⟨15573814442818257173877469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83060343695030704927346501 15573814442818257173877469)
  ·
    refine ⟨5840180416056846440204051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15573814442818257173877469 5840180416056846440204051)
    ·
      refine ⟨8760270624085269660306077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5840180416056846440204051 8760270624085269660306077)
      ·
        refine ⟨3285101484031976122614779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8760270624085269660306077 3285101484031976122614779)
        ·
          refine ⟨4927652226047964183922169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3285101484031976122614779 4927652226047964183922169)
          ·
            refine ⟨3695739169535973137941627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4927652226047964183922169 3695739169535973137941627)
            ·
              refine ⟨5543608754303959706912441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695739169535973137941627 5543608754303959706912441)
              ·
                refine ⟨4157706565727969780184331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5543608754303959706912441 4157706565727969780184331)
                ·
                  refine ⟨6236559848591954670276497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4157706565727969780184331 6236559848591954670276497)
                  ·
                    refine ⟨4677419886443966002707373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6236559848591954670276497 4677419886443966002707373)
                    ·
                      refine ⟨1754032457416487251015265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4677419886443966002707373 1754032457416487251015265)
                      ·
                        rfl

theorem cell23_3415966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_3415966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415966 prefixEnd_3415966 := by exact prefixLift 3415966
  have htrace : WordTrace (prefixWord ++ tailWord_3415966) baseStart_3415966 baseEnd_3415966 := by
    simpa [prefixWord, tailWord_3415966, baseEnd_3415966] using wordTrace_append hprefix tailTrace_3415966
  have hstable : (prefixWord ++ tailWord_3415966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415966).length < 2 ^ (prefixWord ++ tailWord_3415966).sum := by decide
  have hdescent : baseEnd_3415966 < baseStart_3415966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415972 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 1, 3, 2]
def baseStart_3415972 : Nat := 118140960795 + 3415972 * 2 ^ 59
def prefixEnd_3415972 : Nat := 4983230072969 + 3 ^ 40 * 3415972 * 2
def baseEnd_3415972 : Nat := 1754035538300414227540237

theorem tailTrace_3415972 : CollatzResearch.WordTrace tailWord_3415972 prefixEnd_3415972 1754035538300414227540237 := by
  unfold tailWord_3415972
  simp only [CollatzResearch.WordTrace]
  refine ⟨62295367190262160207869085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83060489587016213610492113 62295367190262160207869085)
  ·
    refine ⟨23360762696348310077950907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62295367190262160207869085 23360762696348310077950907)
    ·
      refine ⟨35041144044522465116926361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23360762696348310077950907 35041144044522465116926361)
      ·
        refine ⟨26280858033391848837694771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35041144044522465116926361 26280858033391848837694771)
        ·
          refine ⟨39421287050087773256542157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26280858033391848837694771 39421287050087773256542157)
          ·
            refine ⟨14782982643782914971203309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39421287050087773256542157 14782982643782914971203309)
            ·
              refine ⟨5543618491418593114201241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14782982643782914971203309 5543618491418593114201241)
              ·
                refine ⟨4157713868563944835650931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5543618491418593114201241 4157713868563944835650931)
                ·
                  refine ⟨6236570802845917253476397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4157713868563944835650931 6236570802845917253476397)
                  ·
                    refine ⟨2338714051067218970053649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6236570802845917253476397 2338714051067218970053649)
                    ·
                      refine ⟨1754035538300414227540237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2338714051067218970053649 1754035538300414227540237)
                      ·
                        rfl

theorem cell23_3415972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_3415972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415972 prefixEnd_3415972 := by exact prefixLift 3415972
  have htrace : WordTrace (prefixWord ++ tailWord_3415972) baseStart_3415972 baseEnd_3415972 := by
    simpa [prefixWord, tailWord_3415972, baseEnd_3415972] using wordTrace_append hprefix tailTrace_3415972
  have hstable : (prefixWord ++ tailWord_3415972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415972).length < 2 ^ (prefixWord ++ tailWord_3415972).sum := by decide
  have hdescent : baseEnd_3415972 < baseStart_3415972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415985 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 3, 4, 2]
def baseStart_3415985 : Nat := 118140960795 + 3415985 * 2 ^ 59
def prefixEnd_3415985 : Nat := 4983230072969 + 3 ^ 40 * 3415985 * 2
def baseEnd_3415985 : Nat := 1754042213548922676677677

theorem tailTrace_3415985 : CollatzResearch.WordTrace tailWord_3415985 prefixEnd_3415985 1754042213548922676677677 := by
  unfold tailWord_3415985
  simp only [CollatzResearch.WordTrace]
  refine ⟨124591208529477223635961409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83060805686318149090640939 124591208529477223635961409)
  ·
    refine ⟨93443406397107917726971057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124591208529477223635961409 93443406397107917726971057)
    ·
      refine ⟨70082554797830938295228293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93443406397107917726971057 70082554797830938295228293)
      ·
        refine ⟨13140479024593300930355305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70082554797830938295228293 13140479024593300930355305)
        ·
          refine ⟨9855359268444975697766479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13140479024593300930355305 9855359268444975697766479)
          ·
            refine ⟨14783038902667463546649719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9855359268444975697766479 14783038902667463546649719)
            ·
              refine ⟨22174558354001195319974579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783038902667463546649719 22174558354001195319974579)
              ·
                refine ⟨33261837531001792979961869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22174558354001195319974579 33261837531001792979961869)
                ·
                  refine ⟨12473189074125672367485701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33261837531001792979961869 12473189074125672367485701)
                  ·
                    refine ⟨2338722951398563568903569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12473189074125672367485701 2338722951398563568903569)
                    ·
                      refine ⟨1754042213548922676677677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2338722951398563568903569 1754042213548922676677677)
                      ·
                        rfl

theorem cell23_3415985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_3415985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415985 prefixEnd_3415985 := by exact prefixLift 3415985
  have htrace : WordTrace (prefixWord ++ tailWord_3415985) baseStart_3415985 baseEnd_3415985 := by
    simpa [prefixWord, tailWord_3415985, baseEnd_3415985] using wordTrace_append hprefix tailTrace_3415985
  have hstable : (prefixWord ++ tailWord_3415985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415985).length < 2 ^ (prefixWord ++ tailWord_3415985).sum := by decide
  have hdescent : baseEnd_3415985 < baseStart_3415985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415989 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_3415989 : Nat := 118140960795 + 3415989 * 2 ^ 59
def prefixEnd_3415989 : Nat := 4983230072969 + 3 ^ 40 * 3415989 * 2
def baseEnd_3415989 : Nat := 1754044267471540661027659

theorem tailTrace_3415989 : CollatzResearch.WordTrace tailWord_3415989 prefixEnd_3415989 1754044267471540661027659 := by
  unfold tailWord_3415989
  simp only [CollatzResearch.WordTrace]
  refine ⟨124591354421462732319107021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83060902947641821546071347 124591354421462732319107021)
  ·
    refine ⟨46721757908048524619665133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124591354421462732319107021 46721757908048524619665133)
    ·
      refine ⟨17520659215518196732374425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46721757908048524619665133 17520659215518196732374425)
      ·
        refine ⟨13140494411638647549280819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17520659215518196732374425 13140494411638647549280819)
        ·
          refine ⟨19710741617457971323921229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13140494411638647549280819 19710741617457971323921229)
          ·
            refine ⟨7391528106546739246470461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19710741617457971323921229 7391528106546739246470461)
            ·
              refine ⟨2771823039955027217426423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7391528106546739246470461 2771823039955027217426423)
              ·
                refine ⟨4157734559932540826139635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771823039955027217426423 4157734559932540826139635)
                ·
                  refine ⟨6236601839898811239209453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4157734559932540826139635 6236601839898811239209453)
                  ·
                    refine ⟨2338725689962054214703545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6236601839898811239209453 2338725689962054214703545)
                    ·
                      refine ⟨1754044267471540661027659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2338725689962054214703545 1754044267471540661027659)
                      ·
                        rfl

theorem cell23_3415989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_3415989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3415989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3415989 prefixEnd_3415989 := by exact prefixLift 3415989
  have htrace : WordTrace (prefixWord ++ tailWord_3415989) baseStart_3415989 baseEnd_3415989 := by
    simpa [prefixWord, tailWord_3415989, baseEnd_3415989] using wordTrace_append hprefix tailTrace_3415989
  have hstable : (prefixWord ++ tailWord_3415989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415989).length < 2 ^ (prefixWord ++ tailWord_3415989).sum := by decide
  have hdescent : baseEnd_3415989 < baseStart_3415989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416051 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 1, 10]
def baseStart_3416051 : Nat := 118140960795 + 3416051 * 2 ^ 59
def prefixEnd_3416051 : Nat := 4983230072969 + 3 ^ 40 * 3416051 * 2
def baseEnd_3416051 : Nat := 584692034424039806150791

theorem tailTrace_3416051 : CollatzResearch.WordTrace tailWord_3416051 prefixEnd_3416051 584692034424039806150791 := by
  unfold tailWord_3416051
  simp only [CollatzResearch.WordTrace]
  refine ⟨124593615747238116907864007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83062410498158744605242671 124593615747238116907864007)
  ·
    refine ⟨186890423620857175361796011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124593615747238116907864007 186890423620857175361796011)
    ·
      refine ⟨280335635431285763042694017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186890423620857175361796011 280335635431285763042694017)
      ·
        refine ⟨210251726573464322282020513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280335635431285763042694017 210251726573464322282020513)
        ·
          refine ⟨157688794930098241711515385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210251726573464322282020513 157688794930098241711515385)
          ·
            refine ⟨118266596197573681283636539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157688794930098241711515385 118266596197573681283636539)
            ·
              refine ⟨177399894296360521925454809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118266596197573681283636539 177399894296360521925454809)
              ·
                refine ⟨133049920722270391444091107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177399894296360521925454809 133049920722270391444091107)
                ·
                  refine ⟨199574881083405587166136661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133049920722270391444091107 199574881083405587166136661)
                  ·
                    refine ⟨584692034424039806150791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 199574881083405587166136661 584692034424039806150791)
                    ·
                      rfl

theorem cell23_3416051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 10].length) (baseStart_3416051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416051 prefixEnd_3416051 := by exact prefixLift 3416051
  have htrace : WordTrace (prefixWord ++ tailWord_3416051) baseStart_3416051 baseEnd_3416051 := by
    simpa [prefixWord, tailWord_3416051, baseEnd_3416051] using wordTrace_append hprefix tailTrace_3416051
  have hstable : (prefixWord ++ tailWord_3416051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416051).length < 2 ^ (prefixWord ++ tailWord_3416051).sum := by decide
  have hdescent : baseEnd_3416051 < baseStart_3416051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416070 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_3416070 : Nat := 118140960795 + 3416070 * 2 ^ 59
def prefixEnd_3416070 : Nat := 4983230072969 + 3 ^ 40 * 3416070 * 2
def baseEnd_3416070 : Nat := 1754085859404554844114787

theorem tailTrace_3416070 : CollatzResearch.WordTrace tailWord_3416070 prefixEnd_3416070 1754085859404554844114787 := by
  unfold tailWord_3416070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3893572147942790098525177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83062872489446188768537109 3893572147942790098525177)
  ·
    refine ⟨2920179110957092573893883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3893572147942790098525177 2920179110957092573893883)
    ·
      refine ⟨4380268666435638860840825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2920179110957092573893883 4380268666435638860840825)
      ·
        refine ⟨3285201499826729145630619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4380268666435638860840825 3285201499826729145630619)
        ·
          refine ⟨4927802249740093718445929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3285201499826729145630619 4927802249740093718445929)
          ·
            refine ⟨3695851687305070288834447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4927802249740093718445929 3695851687305070288834447)
            ·
              refine ⟨5543777530957605433251671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3695851687305070288834447 5543777530957605433251671)
              ·
                refine ⟨8315666296436408149877507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5543777530957605433251671 8315666296436408149877507)
                ·
                  refine ⟨12473499444654612224816261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8315666296436408149877507 12473499444654612224816261)
                  ·
                    refine ⟨2338781145872739792153049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12473499444654612224816261 2338781145872739792153049)
                    ·
                      refine ⟨1754085859404554844114787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2338781145872739792153049 1754085859404554844114787)
                      ·
                        rfl

theorem cell23_3416070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_3416070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416070 prefixEnd_3416070 := by exact prefixLift 3416070
  have htrace : WordTrace (prefixWord ++ tailWord_3416070) baseStart_3416070 baseEnd_3416070 := by
    simpa [prefixWord, tailWord_3416070, baseEnd_3416070] using wordTrace_append hprefix tailTrace_3416070
  have hstable : (prefixWord ++ tailWord_3416070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416070).length < 2 ^ (prefixWord ++ tailWord_3416070).sum := by decide
  have hdescent : baseEnd_3416070 < baseStart_3416070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416075 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 2, 4, 2]
def baseStart_3416075 : Nat := 118140960795 + 3416075 * 2 ^ 59
def prefixEnd_3416075 : Nat := 4983230072969 + 3 ^ 40 * 3416075 * 2
def baseEnd_3416075 : Nat := 1754088426807827324552263

theorem tailTrace_3416075 : CollatzResearch.WordTrace tailWord_3416075 prefixEnd_3416075 1754088426807827324552263 := by
  unfold tailWord_3416075
  simp only [CollatzResearch.WordTrace]
  refine ⟨124594491099151169006737679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83062994066100779337825119 124594491099151169006737679)
  ·
    refine ⟨186891736648726753510106519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124594491099151169006737679 186891736648726753510106519)
    ·
      refine ⟨280337604973090130265159779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186891736648726753510106519 280337604973090130265159779)
      ·
        refine ⟨420506407459635195397739669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280337604973090130265159779 420506407459635195397739669)
        ·
          refine ⟨19711237849670399784269047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 420506407459635195397739669 19711237849670399784269047)
          ·
            refine ⟨29566856774505599676403571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19711237849670399784269047 29566856774505599676403571)
            ·
              refine ⟨44350285161758399514605357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29566856774505599676403571 44350285161758399514605357)
              ·
                refine ⟨16631356935659399817977009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44350285161758399514605357 16631356935659399817977009)
                ·
                  refine ⟨12473517701744549863482757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16631356935659399817977009 12473517701744549863482757)
                  ·
                    refine ⟨2338784569077103099403017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12473517701744549863482757 2338784569077103099403017)
                    ·
                      refine ⟨1754088426807827324552263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2338784569077103099403017 1754088426807827324552263)
                      ·
                        rfl

theorem cell23_3416075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 4, 2].length) (baseStart_3416075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416075 prefixEnd_3416075 := by exact prefixLift 3416075
  have htrace : WordTrace (prefixWord ++ tailWord_3416075) baseStart_3416075 baseEnd_3416075 := by
    simpa [prefixWord, tailWord_3416075, baseEnd_3416075] using wordTrace_append hprefix tailTrace_3416075
  have hstable : (prefixWord ++ tailWord_3416075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416075).length < 2 ^ (prefixWord ++ tailWord_3416075).sum := by decide
  have hdescent : baseEnd_3416075 < baseStart_3416075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416088 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3416088 : Nat := 118140960795 + 3416088 * 2 ^ 59
def prefixEnd_3416088 : Nat := 4983230072969 + 3 ^ 40 * 3416088 * 2
def baseEnd_3416088 : Nat := 1754095102056335773689703

theorem tailTrace_3416088 : CollatzResearch.WordTrace tailWord_3416088 prefixEnd_3416088 1754095102056335773689703 := by
  unfold tailWord_3416088
  simp only [CollatzResearch.WordTrace]
  refine ⟨62297482624052036113480459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83063310165402714817973945 62297482624052036113480459)
  ·
    refine ⟨93446223936078054170220689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62297482624052036113480459 93446223936078054170220689)
    ·
      refine ⟨70084667952058540627665517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93446223936078054170220689 70084667952058540627665517)
      ·
        refine ⟨26281750482021952735374569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70084667952058540627665517 26281750482021952735374569)
        ·
          refine ⟨19711312861516464551530927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26281750482021952735374569 19711312861516464551530927)
          ·
            refine ⟨29566969292274696827296391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19711312861516464551530927 29566969292274696827296391)
            ·
              refine ⟨44350453938412045240944587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29566969292274696827296391 44350453938412045240944587)
              ·
                refine ⟨66525680907618067861416881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44350453938412045240944587 66525680907618067861416881)
                ·
                  refine ⟨49894260680713550896062661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66525680907618067861416881 49894260680713550896062661)
                  ·
                    refine ⟨9355173877633790793011749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49894260680713550896062661 9355173877633790793011749)
                    ·
                      refine ⟨1754095102056335773689703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9355173877633790793011749 1754095102056335773689703)
                      ·
                        rfl

theorem cell23_3416088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3416088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416088 prefixEnd_3416088 := by exact prefixLift 3416088
  have htrace : WordTrace (prefixWord ++ tailWord_3416088) baseStart_3416088 baseEnd_3416088 := by
    simpa [prefixWord, tailWord_3416088, baseEnd_3416088] using wordTrace_append hprefix tailTrace_3416088
  have hstable : (prefixWord ++ tailWord_3416088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416088).length < 2 ^ (prefixWord ++ tailWord_3416088).sum := by decide
  have hdescent : baseEnd_3416088 < baseStart_3416088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416095 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 3]
def baseStart_3416095 : Nat := 118140960795 + 3416095 * 2 ^ 59
def prefixEnd_3416095 : Nat := 4983230072969 + 3 ^ 40 * 3416095 * 2
def baseEnd_3416095 : Nat := 1754098696420917246302171

theorem tailTrace_3416095 : CollatzResearch.WordTrace tailWord_3416095 prefixEnd_3416095 1754098696420917246302171 := by
  unfold tailWord_3416095
  simp only [CollatzResearch.WordTrace]
  refine ⟨124595220559078712422465739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83063480372719141614977159 124595220559078712422465739)
  ·
    refine ⟨186892830838618068633698609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124595220559078712422465739 186892830838618068633698609)
    ·
      refine ⟨140169623128963551475273957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186892830838618068633698609 140169623128963551475273957)
      ·
        refine ⟨26281804336680665901613867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140169623128963551475273957 26281804336680665901613867)
        ·
          refine ⟨39422706505020998852420801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26281804336680665901613867 39422706505020998852420801)
          ·
            refine ⟨29567029878765749139315601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39422706505020998852420801 29567029878765749139315601)
            ·
              refine ⟨22175272409074311854486701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29567029878765749139315601 22175272409074311854486701)
              ·
                refine ⟨8315727153402866945432513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22175272409074311854486701 8315727153402866945432513)
                ·
                  refine ⟨6236795365052150209074385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8315727153402866945432513 6236795365052150209074385)
                  ·
                    refine ⟨4677596523789112656805789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6236795365052150209074385 4677596523789112656805789)
                    ·
                      refine ⟨1754098696420917246302171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4677596523789112656805789 1754098696420917246302171)
                      ·
                        rfl

theorem cell23_3416095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_3416095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416095 prefixEnd_3416095 := by exact prefixLift 3416095
  have htrace : WordTrace (prefixWord ++ tailWord_3416095) baseStart_3416095 baseEnd_3416095 := by
    simpa [prefixWord, tailWord_3416095, baseEnd_3416095] using wordTrace_append hprefix tailTrace_3416095
  have hstable : (prefixWord ++ tailWord_3416095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416095).length < 2 ^ (prefixWord ++ tailWord_3416095).sum := by decide
  have hdescent : baseEnd_3416095 < baseStart_3416095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416098 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 10]
def baseStart_3416098 : Nat := 118140960795 + 3416098 * 2 ^ 59
def prefixEnd_3416098 : Nat := 4983230072969 + 3 ^ 40 * 3416098 * 2
def baseEnd_3416098 : Nat := 194900026318097859396073

theorem tailTrace_3416098 : CollatzResearch.WordTrace tailWord_3416098 prefixEnd_3416098 194900026318097859396073 := by
  unfold tailWord_3416098
  simp only [CollatzResearch.WordTrace]
  refine ⟨31148832494516960983706237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83063553318711895956549965 31148832494516960983706237)
  ·
    refine ⟨11680812185443860368889839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31148832494516960983706237 11680812185443860368889839)
    ·
      refine ⟨17521218278165790553334759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11680812185443860368889839 17521218278165790553334759)
      ·
        refine ⟨26281827417248685830002139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17521218278165790553334759 26281827417248685830002139)
        ·
          refine ⟨39422741125873028745003209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26281827417248685830002139 39422741125873028745003209)
          ·
            refine ⟨29567055844404771558752407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39422741125873028745003209 29567055844404771558752407)
            ·
              refine ⟨44350583766607157338128611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29567055844404771558752407 44350583766607157338128611)
              ·
                refine ⟨66525875649910736007192917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44350583766607157338128611 66525875649910736007192917)
                ·
                  refine ⟨194900026318097859396073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 66525875649910736007192917 194900026318097859396073)
                  ·
                    rfl

theorem cell23_3416098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_3416098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416098 prefixEnd_3416098 := by exact prefixLift 3416098
  have htrace : WordTrace (prefixWord ++ tailWord_3416098) baseStart_3416098 baseEnd_3416098 := by
    simpa [prefixWord, tailWord_3416098, baseEnd_3416098] using wordTrace_append hprefix tailTrace_3416098
  have hstable : (prefixWord ++ tailWord_3416098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416098).length < 2 ^ (prefixWord ++ tailWord_3416098).sum := by decide
  have hdescent : baseEnd_3416098 < baseStart_3416098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416152 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 2, 3, 2]
def baseStart_3416152 : Nat := 118140960795 + 3416152 * 2 ^ 59
def prefixEnd_3416152 : Nat := 4983230072969 + 3 ^ 40 * 3416152 * 2
def baseEnd_3416152 : Nat := 1754127964818223523289409

theorem tailTrace_3416152 : CollatzResearch.WordTrace tailWord_3416152 prefixEnd_3416152 1754127964818223523289409 := by
  unfold tailWord_3416152
  simp only [CollatzResearch.WordTrace]
  refine ⟨62298649759936105578645355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83064866346581474104860473 62298649759936105578645355)
  ·
    refine ⟨93447974639904158367968033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62298649759936105578645355 93447974639904158367968033)
    ·
      refine ⟨70085980979928118775976025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93447974639904158367968033 70085980979928118775976025)
      ·
        refine ⟨52564485734946089081982019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70085980979928118775976025 52564485734946089081982019)
        ·
          refine ⟨78846728602419133622973029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52564485734946089081982019 78846728602419133622973029)
          ·
            refine ⟨14783761612953587554307443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78846728602419133622973029 14783761612953587554307443)
            ·
              refine ⟨22175642419430381331461165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783761612953587554307443 22175642419430381331461165)
              ·
                refine ⟨8315865907286392999297937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22175642419430381331461165 8315865907286392999297937)
                ·
                  refine ⟨6236899430464794749473453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8315865907286392999297937 6236899430464794749473453)
                  ·
                    refine ⟨2338837286424298031052545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6236899430464794749473453 2338837286424298031052545)
                    ·
                      refine ⟨1754127964818223523289409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2338837286424298031052545 1754127964818223523289409)
                      ·
                        rfl

theorem cell23_3416152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_3416152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416152 prefixEnd_3416152 := by exact prefixLift 3416152
  have htrace : WordTrace (prefixWord ++ tailWord_3416152) baseStart_3416152 baseEnd_3416152 := by
    simpa [prefixWord, tailWord_3416152, baseEnd_3416152] using wordTrace_append hprefix tailTrace_3416152
  have hstable : (prefixWord ++ tailWord_3416152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416152).length < 2 ^ (prefixWord ++ tailWord_3416152).sum := by decide
  have hdescent : baseEnd_3416152 < baseStart_3416152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416176 : List Nat := [2, 1, 1, 1, 5, 2, 4, 2, 1, 1, 3]
def baseStart_3416176 : Nat := 118140960795 + 3416176 * 2 ^ 59
def prefixEnd_3416176 : Nat := 4983230072969 + 3 ^ 40 * 3416176 * 2
def baseEnd_3416176 : Nat := 1754140288353931429389299

theorem tailTrace_3416176 : CollatzResearch.WordTrace tailWord_3416176 prefixEnd_3416176 1754140288353931429389299 := by
  unfold tailWord_3416176
  simp only [CollatzResearch.WordTrace]
  refine ⟨62299087435892631628082191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83065449914523508837442921 62299087435892631628082191)
  ·
    refine ⟨93448631153838947442123287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62299087435892631628082191 93448631153838947442123287)
    ·
      refine ⟨140172946730758421163184931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93448631153838947442123287 140172946730758421163184931)
      ·
        refine ⟨210259420096137631744777397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140172946730758421163184931 210259420096137631744777397)
        ·
          refine ⟨19711820634012902976072881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210259420096137631744777397 19711820634012902976072881)
          ·
            refine ⟨14783865475509677232054661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19711820634012902976072881 14783865475509677232054661)
            ·
              refine ⟨2771974776658064481010249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14783865475509677232054661 2771974776658064481010249)
              ·
                refine ⟨2078981082493548360757687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2771974776658064481010249 2078981082493548360757687)
                ·
                  refine ⟨3118471623740322541136531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078981082493548360757687 3118471623740322541136531)
                  ·
                    refine ⟨4677707435610483811704797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3118471623740322541136531 4677707435610483811704797)
                    ·
                      refine ⟨1754140288353931429389299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4677707435610483811704797 1754140288353931429389299)
                      ·
                        rfl

theorem cell23_3416176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 2, 1, 1, 3].length) (baseStart_3416176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416176 prefixEnd_3416176 := by exact prefixLift 3416176
  have htrace : WordTrace (prefixWord ++ tailWord_3416176) baseStart_3416176 baseEnd_3416176 := by
    simpa [prefixWord, tailWord_3416176, baseEnd_3416176] using wordTrace_append hprefix tailTrace_3416176
  have hstable : (prefixWord ++ tailWord_3416176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416176).length < 2 ^ (prefixWord ++ tailWord_3416176).sum := by decide
  have hdescent : baseEnd_3416176 < baseStart_3416176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416182 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3416182 : Nat := 118140960795 + 3416182 * 2 ^ 59
def prefixEnd_3416182 : Nat := 4983230072969 + 3 ^ 40 * 3416182 * 2
def baseEnd_3416182 : Nat := 1754143369237858405914271

theorem tailTrace_3416182 : CollatzResearch.WordTrace tailWord_3416182 prefixEnd_3416182 1754143369237858405914271 := by
  unfold tailWord_3416182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7787399606860220392555175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83065595806509017520588533 7787399606860220392555175)
  ·
    refine ⟨11681099410290330588832763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7787399606860220392555175 11681099410290330588832763)
    ·
      refine ⟨17521649115435495883249145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11681099410290330588832763 17521649115435495883249145)
      ·
        refine ⟨13141236836576621912436859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17521649115435495883249145 13141236836576621912436859)
        ·
          refine ⟨19711855254864932868655289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13141236836576621912436859 19711855254864932868655289)
          ·
            refine ⟨14783891441148699651491467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19711855254864932868655289 14783891441148699651491467)
            ·
              refine ⟨22175837161723049477237201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783891441148699651491467 22175837161723049477237201)
              ·
                refine ⟨16631877871292287107927901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22175837161723049477237201 16631877871292287107927901)
                ·
                  refine ⟨6236954201734607665472963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16631877871292287107927901 6236954201734607665472963)
                  ·
                    refine ⟨9355431302601911498209445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6236954201734607665472963 9355431302601911498209445)
                    ·
                      refine ⟨1754143369237858405914271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9355431302601911498209445 1754143369237858405914271)
                      ·
                        rfl

theorem cell23_3416182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3416182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416182 prefixEnd_3416182 := by exact prefixLift 3416182
  have htrace : WordTrace (prefixWord ++ tailWord_3416182) baseStart_3416182 baseEnd_3416182 := by
    simpa [prefixWord, tailWord_3416182, baseEnd_3416182] using wordTrace_append hprefix tailTrace_3416182
  have hstable : (prefixWord ++ tailWord_3416182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416182).length < 2 ^ (prefixWord ++ tailWord_3416182).sum := by decide
  have hdescent : baseEnd_3416182 < baseStart_3416182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416195 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 4]
def baseStart_3416195 : Nat := 118140960795 + 3416195 * 2 ^ 59
def prefixEnd_3416195 : Nat := 4983230072969 + 3 ^ 40 * 3416195 * 2
def baseEnd_3416195 : Nat := 1754150044486366855051711

theorem tailTrace_3416195 : CollatzResearch.WordTrace tailWord_3416195 prefixEnd_3416195 1754150044486366855051711 := by
  unfold tailWord_3416195
  simp only [CollatzResearch.WordTrace]
  refine ⟨124598867858716429501106039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83065911905810953000737359 124598867858716429501106039)
  ·
    refine ⟨186898301788074644251659059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124598867858716429501106039 186898301788074644251659059)
    ·
      refine ⟨280347452682111966377488589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186898301788074644251659059 280347452682111966377488589)
      ·
        refine ⟨105130294755791987391558221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280347452682111966377488589 105130294755791987391558221)
        ·
          refine ⟨39423860533421995271834333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105130294755791987391558221 39423860533421995271834333)
          ·
            refine ⟨14783947700033248226937875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39423860533421995271834333 14783947700033248226937875)
            ·
              refine ⟨22175921550049872340406813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783947700033248226937875 22175921550049872340406813)
              ·
                refine ⟨8315970581268702127652555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22175921550049872340406813 8315970581268702127652555)
                ·
                  refine ⟨12473955871903053191478833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8315970581268702127652555 12473955871903053191478833)
                  ·
                    refine ⟨9355466903927289893609125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12473955871903053191478833 9355466903927289893609125)
                    ·
                      refine ⟨1754150044486366855051711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9355466903927289893609125 1754150044486366855051711)
                      ·
                        rfl

theorem cell23_3416195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_3416195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416195 prefixEnd_3416195 := by exact prefixLift 3416195
  have htrace : WordTrace (prefixWord ++ tailWord_3416195) baseStart_3416195 baseEnd_3416195 := by
    simpa [prefixWord, tailWord_3416195, baseEnd_3416195] using wordTrace_append hprefix tailTrace_3416195
  have hstable : (prefixWord ++ tailWord_3416195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416195).length < 2 ^ (prefixWord ++ tailWord_3416195).sum := by decide
  have hdescent : baseEnd_3416195 < baseStart_3416195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416202 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_3416202 : Nat := 118140960795 + 3416202 * 2 ^ 59
def prefixEnd_3416202 : Nat := 4983230072969 + 3 ^ 40 * 3416202 * 2
def baseEnd_3416202 : Nat := 1754153638850948327664179

theorem tailTrace_3416202 : CollatzResearch.WordTrace tailWord_3416202 prefixEnd_3416202 1754153638850948327664179 := by
  unfold tailWord_3416202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31149780792422767424152715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83066082113127379797740573 31149780792422767424152715)
  ·
    refine ⟨46724671188634151136229073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31149780792422767424152715 46724671188634151136229073)
    ·
      refine ⟨35043503391475613352171805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46724671188634151136229073 35043503391475613352171805)
      ·
        refine ⟨13141313771803355007064427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35043503391475613352171805 13141313771803355007064427)
        ·
          refine ⟨19711970657705032510596641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13141313771803355007064427 19711970657705032510596641)
          ·
            refine ⟨14783977993278774382947481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19711970657705032510596641 14783977993278774382947481)
            ·
              refine ⟨11087983494959080787210611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14783977993278774382947481 11087983494959080787210611)
              ·
                refine ⟨16631975242438621180815917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11087983494959080787210611 16631975242438621180815917)
                ·
                  refine ⟨6236990715914482942805969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16631975242438621180815917 6236990715914482942805969)
                  ·
                    refine ⟨4677743036935862207104477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6236990715914482942805969 4677743036935862207104477)
                    ·
                      refine ⟨1754153638850948327664179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4677743036935862207104477 1754153638850948327664179)
                      ·
                        rfl

theorem cell23_3416202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_3416202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416202 prefixEnd_3416202 := by exact prefixLift 3416202
  have htrace : WordTrace (prefixWord ++ tailWord_3416202) baseStart_3416202 baseEnd_3416202 := by
    simpa [prefixWord, tailWord_3416202, baseEnd_3416202] using wordTrace_append hprefix tailTrace_3416202
  have hstable : (prefixWord ++ tailWord_3416202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416202).length < 2 ^ (prefixWord ++ tailWord_3416202).sum := by decide
  have hdescent : baseEnd_3416202 < baseStart_3416202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416216 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 1, 1, 4]
def baseStart_3416216 : Nat := 118140960795 + 3416216 * 2 ^ 59
def prefixEnd_3416216 : Nat := 4983230072969 + 3 ^ 40 * 3416216 * 2
def baseEnd_3416216 : Nat := 1754160827580111272889115

theorem tailTrace_3416216 : CollatzResearch.WordTrace tailWord_3416216 prefixEnd_3416216 1754160827580111272889115 := by
  unfold tailWord_3416216
  simp only [CollatzResearch.WordTrace]
  refine ⟨62299816895820175043810251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83066422527760233391747001 62299816895820175043810251)
  ·
    refine ⟨93449725343730262565715377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62299816895820175043810251 93449725343730262565715377)
    ·
      refine ⟨70087294007797696924286533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93449725343730262565715377 70087294007797696924286533)
      ·
        refine ⟨13141367626462068173303725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70087294007797696924286533 13141367626462068173303725)
        ·
          refine ⟨4928012859923275564988897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13141367626462068173303725 4928012859923275564988897)
          ·
            refine ⟨3696009644942456673741673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4928012859923275564988897 3696009644942456673741673)
            ·
              refine ⟨2772007233706842505306255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3696009644942456673741673 2772007233706842505306255)
              ·
                refine ⟨4158010850560263757959383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772007233706842505306255 4158010850560263757959383)
                ·
                  refine ⟨6237016275840395636939075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4158010850560263757959383 6237016275840395636939075)
                  ·
                    refine ⟨9355524413760593455408613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6237016275840395636939075 9355524413760593455408613)
                    ·
                      refine ⟨1754160827580111272889115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9355524413760593455408613 1754160827580111272889115)
                      ·
                        rfl

theorem cell23_3416216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_3416216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416216 prefixEnd_3416216 := by exact prefixLift 3416216
  have htrace : WordTrace (prefixWord ++ tailWord_3416216) baseStart_3416216 baseEnd_3416216 := by
    simpa [prefixWord, tailWord_3416216, baseEnd_3416216] using wordTrace_append hprefix tailTrace_3416216
  have hstable : (prefixWord ++ tailWord_3416216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416216).length < 2 ^ (prefixWord ++ tailWord_3416216).sum := by decide
  have hdescent : baseEnd_3416216 < baseStart_3416216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416222 : List Nat := [4, 3, 1, 1, 3, 1, 10]
def baseStart_3416222 : Nat := 118140960795 + 3416222 * 2 ^ 59
def prefixEnd_3416222 : Nat := 4983230072969 + 3 ^ 40 * 3416222 * 2
def baseEnd_3416222 : Nat := 21656344548938743819927

theorem tailTrace_3416222 : CollatzResearch.WordTrace tailWord_3416222 prefixEnd_3416222 21656344548938743819927 := by
  unfold tailWord_3416222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15574981578702326639042365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83066568419745742074892613 15574981578702326639042365)
  ·
    refine ⟨5840618092013372489640887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15574981578702326639042365 5840618092013372489640887)
    ·
      refine ⟨8760927138020058734461331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5840618092013372489640887 8760927138020058734461331)
      ·
        refine ⟨13141390707030088101691997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8760927138020058734461331 13141390707030088101691997)
        ·
          refine ⟨4928021515136283038134499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13141390707030088101691997 4928021515136283038134499)
          ·
            refine ⟨7392032272704424557201749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4928021515136283038134499 7392032272704424557201749)
            ·
              refine ⟨21656344548938743819927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7392032272704424557201749 21656344548938743819927)
              ·
                rfl

theorem cell23_3416222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 10].length) (baseStart_3416222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416222 prefixEnd_3416222 := by exact prefixLift 3416222
  have htrace : WordTrace (prefixWord ++ tailWord_3416222) baseStart_3416222 baseEnd_3416222 := by
    simpa [prefixWord, tailWord_3416222, baseEnd_3416222] using wordTrace_append hprefix tailTrace_3416222
  have hstable : (prefixWord ++ tailWord_3416222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416222).length < 2 ^ (prefixWord ++ tailWord_3416222).sum := by decide
  have hdescent : baseEnd_3416222 < baseStart_3416222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416226 : List Nat := [3, 3, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_3416226 : Nat := 118140960795 + 3416226 * 2 ^ 59
def prefixEnd_3416226 : Nat := 4983230072969 + 3 ^ 40 * 3416226 * 2
def baseEnd_3416226 : Nat := 584721987462218744588023

theorem tailTrace_3416226 : CollatzResearch.WordTrace tailWord_3416226 prefixEnd_3416226 584721987462218744588023 := by
  unfold tailWord_3416226
  simp only [CollatzResearch.WordTrace]
  refine ⟨31149999630401030448871133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83066665681069414530323021 31149999630401030448871133)
  ·
    refine ⟨11681249861400386418326675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31149999630401030448871133 11681249861400386418326675)
    ·
      refine ⟨17521874792100579627490013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11681249861400386418326675 17521874792100579627490013)
      ·
        refine ⟨6570703047037717360308755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17521874792100579627490013 6570703047037717360308755)
        ·
          refine ⟨9856054570556576040463133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6570703047037717360308755 9856054570556576040463133)
          ·
            refine ⟨3696020463958716015173675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9856054570556576040463133 3696020463958716015173675)
            ·
              refine ⟨5544030695938074022760513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3696020463958716015173675 5544030695938074022760513)
              ·
                refine ⟨4158023021953555517070385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5544030695938074022760513 4158023021953555517070385)
                ·
                  refine ⟨3118517266465166637802789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4158023021953555517070385 3118517266465166637802789)
                  ·
                    refine ⟨584721987462218744588023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3118517266465166637802789 584721987462218744588023)
                    ·
                      rfl

theorem cell23_3416226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_3416226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416226 prefixEnd_3416226 := by exact prefixLift 3416226
  have htrace : WordTrace (prefixWord ++ tailWord_3416226) baseStart_3416226 baseEnd_3416226 := by
    simpa [prefixWord, tailWord_3416226, baseEnd_3416226] using wordTrace_append hprefix tailTrace_3416226
  have hstable : (prefixWord ++ tailWord_3416226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416226).length < 2 ^ (prefixWord ++ tailWord_3416226).sum := by decide
  have hdescent : baseEnd_3416226 < baseStart_3416226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416289 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 4, 2, 2]
def baseStart_3416289 : Nat := 118140960795 + 3416289 * 2 ^ 59
def prefixEnd_3416289 : Nat := 4983230072969 + 3 ^ 40 * 3416289 * 2
def baseEnd_3416289 : Nat := 1754198311667889487276279

theorem tailTrace_3416289 : CollatzResearch.WordTrace tailWord_3416289 prefixEnd_3416289 1754198311667889487276279 := by
  unfold tailWord_3416289
  simp only [CollatzResearch.WordTrace]
  refine ⟨124602296320375883555027921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83068197546917255703351947 124602296320375883555027921)
  ·
    refine ⟨93451722240281912666270941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124602296320375883555027921 93451722240281912666270941)
    ·
      refine ⟨35044395840105717249851603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93451722240281912666270941 35044395840105717249851603)
      ·
        refine ⟨52566593760158575874777405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35044395840105717249851603 52566593760158575874777405)
        ·
          refine ⟨19712472660059465953041527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52566593760158575874777405 19712472660059465953041527)
          ·
            refine ⟨29568708990089198929562291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19712472660059465953041527 29568708990089198929562291)
            ·
              refine ⟨44353063485133798394343437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29568708990089198929562291 44353063485133798394343437)
              ·
                refine ⟨16632398806925174397878789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44353063485133798394343437 16632398806925174397878789)
                ·
                  refine ⟨3118574776298470199602273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16632398806925174397878789 3118574776298470199602273)
                  ·
                    refine ⟨2338931082223852649701705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3118574776298470199602273 2338931082223852649701705)
                    ·
                      refine ⟨1754198311667889487276279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2338931082223852649701705 1754198311667889487276279)
                      ·
                        rfl

theorem cell23_3416289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_3416289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416289 prefixEnd_3416289 := by exact prefixLift 3416289
  have htrace : WordTrace (prefixWord ++ tailWord_3416289) baseStart_3416289 baseEnd_3416289 := by
    simpa [prefixWord, tailWord_3416289, baseEnd_3416289] using wordTrace_append hprefix tailTrace_3416289
  have hstable : (prefixWord ++ tailWord_3416289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416289).length < 2 ^ (prefixWord ++ tailWord_3416289).sum := by decide
  have hdescent : baseEnd_3416289 < baseStart_3416289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416352 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3416352 : Nat := 118140960795 + 3416352 * 2 ^ 59
def prefixEnd_3416352 : Nat := 4983230072969 + 3 ^ 40 * 3416352 * 2
def baseEnd_3416352 : Nat := 1754230660949122740788489

theorem tailTrace_3416352 : CollatzResearch.WordTrace tailWord_3416352 prefixEnd_3416352 1754230660949122740788489 := by
  unfold tailWord_3416352
  simp only [CollatzResearch.WordTrace]
  refine ⟨62302297059573822657285655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83069729412765096876380873 62302297059573822657285655)
  ·
    refine ⟨93453445589360733985928483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62302297059573822657285655 93453445589360733985928483)
    ·
      refine ⟨140180168384041100978892725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93453445589360733985928483 140180168384041100978892725)
      ·
        refine ⟨13141890786003853216771193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140180168384041100978892725 13141890786003853216771193)
        ·
          refine ⟨9856418089502889912578395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13141890786003853216771193 9856418089502889912578395)
          ·
            refine ⟨14784627134254334868867593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9856418089502889912578395 14784627134254334868867593)
            ·
              refine ⟨11088470350690751151650695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14784627134254334868867593 11088470350690751151650695)
              ·
                refine ⟨16632705526036126727476043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11088470350690751151650695 16632705526036126727476043)
                ·
                  refine ⟨24949058289054190091214065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16632705526036126727476043 24949058289054190091214065)
                  ·
                    refine ⟨18711793716790642568410549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24949058289054190091214065 18711793716790642568410549)
                    ·
                      refine ⟨1754230660949122740788489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18711793716790642568410549 1754230660949122740788489)
                      ·
                        rfl

theorem cell23_3416352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3416352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416352 prefixEnd_3416352 := by exact prefixLift 3416352
  have htrace : WordTrace (prefixWord ++ tailWord_3416352) baseStart_3416352 baseEnd_3416352 := by
    simpa [prefixWord, tailWord_3416352, baseEnd_3416352] using wordTrace_append hprefix tailTrace_3416352
  have hstable : (prefixWord ++ tailWord_3416352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416352).length < 2 ^ (prefixWord ++ tailWord_3416352).sum := by decide
  have hdescent : baseEnd_3416352 < baseStart_3416352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416375 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 6]
def baseStart_3416375 : Nat := 118140960795 + 3416375 * 2 ^ 59
def prefixEnd_3416375 : Nat := 4983230072969 + 3 ^ 40 * 3416375 * 2
def baseEnd_3416375 : Nat := 1754242471004176150800883

theorem tailTrace_3416375 : CollatzResearch.WordTrace tailWord_3416375 prefixEnd_3416375 1754242471004176150800883 := by
  unfold tailWord_3416375
  simp only [CollatzResearch.WordTrace]
  refine ⟨124605432998064320242658579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83070288665376213495105719 124605432998064320242658579)
  ·
    refine ⟨186908149497096480363987869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124605432998064320242658579 186908149497096480363987869)
    ·
      refine ⟨70090556061411180136495451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186908149497096480363987869 70090556061411180136495451)
      ·
        refine ⟨105135834092116770204743177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70090556061411180136495451 105135834092116770204743177)
        ·
          refine ⟨78851875569087577653557383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105135834092116770204743177 78851875569087577653557383)
          ·
            refine ⟨118277813353631366480336075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78851875569087577653557383 118277813353631366480336075)
            ·
              refine ⟨177416720030447049720504113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118277813353631366480336075 177416720030447049720504113)
              ·
                refine ⟨133062540022835287290378085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177416720030447049720504113 133062540022835287290378085)
                ·
                  refine ⟨24949226254281616366945891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133062540022835287290378085 24949226254281616366945891)
                  ·
                    refine ⟨37423839381422424550418837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24949226254281616366945891 37423839381422424550418837)
                    ·
                      refine ⟨1754242471004176150800883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37423839381422424550418837 1754242471004176150800883)
                      ·
                        rfl

theorem cell23_3416375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_3416375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416375 prefixEnd_3416375 := by exact prefixLift 3416375
  have htrace : WordTrace (prefixWord ++ tailWord_3416375) baseStart_3416375 baseEnd_3416375 := by
    simpa [prefixWord, tailWord_3416375, baseEnd_3416375] using wordTrace_append hprefix tailTrace_3416375
  have hstable : (prefixWord ++ tailWord_3416375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416375).length < 2 ^ (prefixWord ++ tailWord_3416375).sum := by decide
  have hdescent : baseEnd_3416375 < baseStart_3416375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416419 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 6]
def baseStart_3416419 : Nat := 118140960795 + 3416419 * 2 ^ 59
def prefixEnd_3416419 : Nat := 4983230072969 + 3 ^ 40 * 3416419 * 2
def baseEnd_3416419 : Nat := 194918340461441553183409

theorem tailTrace_3416419 : CollatzResearch.WordTrace tailWord_3416419 prefixEnd_3416419 194918340461441553183409 := by
  unfold tailWord_3416419
  simp only [CollatzResearch.WordTrace]
  refine ⟨124607037809904915757260311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83071358539936610504840207 124607037809904915757260311)
  ·
    refine ⟨186910556714857373635890467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124607037809904915757260311 186910556714857373635890467)
    ·
      refine ⟨280365835072286060453835701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186910556714857373635890467 280365835072286060453835701)
      ·
        refine ⟨26284297038026818167547097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280365835072286060453835701 26284297038026818167547097)
        ·
          refine ⟨19713222778520113625660323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26284297038026818167547097 19713222778520113625660323)
          ·
            refine ⟨29569834167780170438490485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19713222778520113625660323 29569834167780170438490485)
            ·
              refine ⟨2772171953229390978608483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29569834167780170438490485 2772171953229390978608483)
              ·
                refine ⟨4158257929844086467912725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772171953229390978608483 4158257929844086467912725)
                ·
                  refine ⟨194918340461441553183409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4158257929844086467912725 194918340461441553183409)
                  ·
                    rfl

theorem cell23_3416419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 6].length) (baseStart_3416419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416419 prefixEnd_3416419 := by exact prefixLift 3416419
  have htrace : WordTrace (prefixWord ++ tailWord_3416419) baseStart_3416419 baseEnd_3416419 := by
    simpa [prefixWord, tailWord_3416419, baseEnd_3416419] using wordTrace_append hprefix tailTrace_3416419
  have hstable : (prefixWord ++ tailWord_3416419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416419).length < 2 ^ (prefixWord ++ tailWord_3416419).sum := by decide
  have hdescent : baseEnd_3416419 < baseStart_3416419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416456 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 2, 3, 2]
def baseStart_3416456 : Nat := 118140960795 + 3416456 * 2 ^ 59
def prefixEnd_3416456 : Nat := 4983230072969 + 3 ^ 40 * 3416456 * 2
def baseEnd_3416456 : Nat := 1754284062937190333888011

theorem tailTrace_3416456 : CollatzResearch.WordTrace tailWord_3416456 prefixEnd_3416456 1754284062937190333888011 := by
  unfold tailWord_3416456
  simp only [CollatzResearch.WordTrace]
  refine ⟨62304193655385435538178611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83072258207180580717571481 62304193655385435538178611)
  ·
    refine ⟨93456290483078153307267917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62304193655385435538178611 93456290483078153307267917)
    ·
      refine ⟨35046108931154307490225469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93456290483078153307267917 35046108931154307490225469)
      ·
        refine ⟨13142290849182865308834551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35046108931154307490225469 13142290849182865308834551)
        ·
          refine ⟨19713436273774297963251827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13142290849182865308834551 19713436273774297963251827)
          ·
            refine ⟨29570154410661446944877741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19713436273774297963251827 29570154410661446944877741)
            ·
              refine ⟨11088807903998042604329153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29570154410661446944877741 11088807903998042604329153)
              ·
                refine ⟨8316605927998531953246865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11088807903998042604329153 8316605927998531953246865)
                ·
                  refine ⟨6237454445998898964935149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8316605927998531953246865 6237454445998898964935149)
                  ·
                    refine ⟨2339045417249587111850681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6237454445998898964935149 2339045417249587111850681)
                    ·
                      refine ⟨1754284062937190333888011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2339045417249587111850681 1754284062937190333888011)
                      ·
                        rfl

theorem cell23_3416456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_3416456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416456 prefixEnd_3416456 := by exact prefixLift 3416456
  have htrace : WordTrace (prefixWord ++ tailWord_3416456) baseStart_3416456 baseEnd_3416456 := by
    simpa [prefixWord, tailWord_3416456, baseEnd_3416456] using wordTrace_append hprefix tailTrace_3416456
  have hstable : (prefixWord ++ tailWord_3416456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416456).length < 2 ^ (prefixWord ++ tailWord_3416456).sum := by decide
  have hdescent : baseEnd_3416456 < baseStart_3416456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416470 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3416470 : Nat := 118140960795 + 3416470 * 2 ^ 59
def prefixEnd_3416470 : Nat := 4983230072969 + 3 ^ 40 * 3416470 * 2
def baseEnd_3416470 : Nat := 194921250185150364345883

theorem tailTrace_3416470 : CollatzResearch.WordTrace tailWord_3416470 prefixEnd_3416470 194921250185150364345883 := by
  unfold tailWord_3416470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7788056120795009466710429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83072598621813434311577909 7788056120795009466710429)
  ·
    refine ⟨2920521045298128550016411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7788056120795009466710429 2920521045298128550016411)
    ·
      refine ⟨4380781567947192825024617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2920521045298128550016411 4380781567947192825024617)
      ·
        refine ⟨3285586175960394618768463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4380781567947192825024617 3285586175960394618768463)
        ·
          refine ⟨4928379263940591928152695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3285586175960394618768463 4928379263940591928152695)
          ·
            refine ⟨7392568895910887892229043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4928379263940591928152695 7392568895910887892229043)
            ·
              refine ⟨11088853343866331838343565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7392568895910887892229043 11088853343866331838343565)
              ·
                refine ⟨4158320003949874439378837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11088853343866331838343565 4158320003949874439378837)
                ·
                  refine ⟨194921250185150364345883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4158320003949874439378837 194921250185150364345883)
                  ·
                    rfl

theorem cell23_3416470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3416470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416470 prefixEnd_3416470 := by exact prefixLift 3416470
  have htrace : WordTrace (prefixWord ++ tailWord_3416470) baseStart_3416470 baseEnd_3416470 := by
    simpa [prefixWord, tailWord_3416470, baseEnd_3416470] using wordTrace_append hprefix tailTrace_3416470
  have hstable : (prefixWord ++ tailWord_3416470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416470).length < 2 ^ (prefixWord ++ tailWord_3416470).sum := by decide
  have hdescent : baseEnd_3416470 < baseStart_3416470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416520 : List Nat := [2, 1, 3, 1, 3, 3, 1, 4, 1, 2, 2]
def baseStart_3416520 : Nat := 118140960795 + 3416520 * 2 ^ 59
def prefixEnd_3416520 : Nat := 4983230072969 + 3 ^ 40 * 3416520 * 2
def baseEnd_3416520 : Nat := 1754316925699078083487717

theorem tailTrace_3416520 : CollatzResearch.WordTrace tailWord_3416520 prefixEnd_3416520 1754316925699078083487717 := by
  unfold tailWord_3416520
  simp only [CollatzResearch.WordTrace]
  refine ⟨62305360791269505003343507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83073814388359340004458009 62305360791269505003343507)
  ·
    refine ⟨93458041186904257505015261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62305360791269505003343507 93458041186904257505015261)
    ·
      refine ⟨35046765445089096564380723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93458041186904257505015261 35046765445089096564380723)
      ·
        refine ⟨52570148167633644846571085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35046765445089096564380723 52570148167633644846571085)
        ·
          refine ⟨19713805562862616817464157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52570148167633644846571085 19713805562862616817464157)
          ·
            refine ⟨7392677086073481306549059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19713805562862616817464157 7392677086073481306549059)
            ·
              refine ⟨11089015629110221959823589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7392677086073481306549059 11089015629110221959823589)
              ·
                refine ⟨2079190430458166617466923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11089015629110221959823589 2079190430458166617466923)
                ·
                  refine ⟨3118785645687249926200385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079190430458166617466923 3118785645687249926200385)
                  ·
                    refine ⟨2339089234265437444650289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3118785645687249926200385 2339089234265437444650289)
                    ·
                      refine ⟨1754316925699078083487717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2339089234265437444650289 1754316925699078083487717)
                      ·
                        rfl

theorem cell23_3416520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 1, 2, 2].length) (baseStart_3416520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416520 prefixEnd_3416520 := by exact prefixLift 3416520
  have htrace : WordTrace (prefixWord ++ tailWord_3416520) baseStart_3416520 baseEnd_3416520 := by
    simpa [prefixWord, tailWord_3416520, baseEnd_3416520] using wordTrace_append hprefix tailTrace_3416520
  have hstable : (prefixWord ++ tailWord_3416520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416520).length < 2 ^ (prefixWord ++ tailWord_3416520).sum := by decide
  have hdescent : baseEnd_3416520 < baseStart_3416520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416522 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_3416522 : Nat := 118140960795 + 3416522 * 2 ^ 59
def prefixEnd_3416522 : Nat := 4983230072969 + 3 ^ 40 * 3416522 * 2
def baseEnd_3416522 : Nat := 584772650886795691887569

theorem tailTrace_3416522 : CollatzResearch.WordTrace tailWord_3416522 prefixEnd_3416522 584772650886795691887569 := by
  unfold tailWord_3416522
  simp only [CollatzResearch.WordTrace]
  refine ⟨31152698632132941087064955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83073863019021176232173213 31152698632132941087064955)
  ·
    refine ⟨46729047948199411630597433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31152698632132941087064955 46729047948199411630597433)
    ·
      refine ⟨35046785961149558722948075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46729047948199411630597433 35046785961149558722948075)
      ·
        refine ⟨52570178941724338084422113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35046785961149558722948075 52570178941724338084422113)
        ·
          refine ⟨39427634206293253563316585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52570178941724338084422113 39427634206293253563316585)
          ·
            refine ⟨29570725654719940172487439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39427634206293253563316585 29570725654719940172487439)
            ·
              refine ⟨44356088482079910258731159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29570725654719940172487439 44356088482079910258731159)
              ·
                refine ⟨66534132723119865388096739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44356088482079910258731159 66534132723119865388096739)
                ·
                  refine ⟨99801199084679798082145109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66534132723119865388096739 99801199084679798082145109)
                  ·
                    refine ⟨584772650886795691887569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 99801199084679798082145109 584772650886795691887569)
                    ·
                      rfl

theorem cell23_3416522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_3416522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416522 prefixEnd_3416522 := by exact prefixLift 3416522
  have htrace : WordTrace (prefixWord ++ tailWord_3416522) baseStart_3416522 baseEnd_3416522 := by
    simpa [prefixWord, tailWord_3416522, baseEnd_3416522] using wordTrace_append hprefix tailTrace_3416522
  have hstable : (prefixWord ++ tailWord_3416522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416522).length < 2 ^ (prefixWord ++ tailWord_3416522).sum := by decide
  have hdescent : baseEnd_3416522 < baseStart_3416522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416633 : List Nat := [1, 2, 1, 5, 1, 1, 5, 2, 5]
def baseStart_3416633 : Nat := 118140960795 + 3416633 * 2 ^ 59
def prefixEnd_3416633 : Nat := 4983230072969 + 3 ^ 40 * 3416633 * 2
def baseEnd_3416633 : Nat := 194930549890337349041633

theorem tailTrace_3416633 : CollatzResearch.WordTrace tailWord_3416633 prefixEnd_3416633 194930549890337349041633 := by
  unfold tailWord_3416633
  simp only [CollatzResearch.WordTrace]
  refine ⟨124614843031129630305550553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83076562020753086870367035 124614843031129630305550553)
  ·
    refine ⟨93461132273347222729162915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124614843031129630305550553 93461132273347222729162915)
    ·
      refine ⟨140191698410020834093744373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93461132273347222729162915 140191698410020834093744373)
      ·
        refine ⟨13142971725939453196288535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140191698410020834093744373 13142971725939453196288535)
        ·
          refine ⟨19714457588909179794432803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13142971725939453196288535 19714457588909179794432803)
          ·
            refine ⟨29571686383363769691649205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19714457588909179794432803 29571686383363769691649205)
            ·
              refine ⟨2772345598440353408592113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29571686383363769691649205 2772345598440353408592113)
              ·
                refine ⟨2079259198830265056444085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772345598440353408592113 2079259198830265056444085)
                ·
                  refine ⟨194930549890337349041633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2079259198830265056444085 194930549890337349041633)
                  ·
                    rfl

theorem cell23_3416633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 5].length) (baseStart_3416633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416633 prefixEnd_3416633 := by exact prefixLift 3416633
  have htrace : WordTrace (prefixWord ++ tailWord_3416633) baseStart_3416633 baseEnd_3416633 := by
    simpa [prefixWord, tailWord_3416633, baseEnd_3416633] using wordTrace_append hprefix tailTrace_3416633
  have hstable : (prefixWord ++ tailWord_3416633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416633).length < 2 ^ (prefixWord ++ tailWord_3416633).sum := by decide
  have hdescent : baseEnd_3416633 < baseStart_3416633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416639 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 5]
def baseStart_3416639 : Nat := 118140960795 + 3416639 * 2 ^ 59
def prefixEnd_3416639 : Nat := 4983230072969 + 3 ^ 40 * 3416639 * 2
def baseEnd_3416639 : Nat := 1754378029896963117899669

theorem tailTrace_3416639 : CollatzResearch.WordTrace tailWord_3416639 prefixEnd_3416639 1754378029896963117899669 := by
  unfold tailWord_3416639
  simp only [CollatzResearch.WordTrace]
  refine ⟨124615061869107893330268971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83076707912738595553512647 124615061869107893330268971)
  ·
    refine ⟨186922592803661839995403457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124615061869107893330268971 186922592803661839995403457)
    ·
      refine ⟨140191944602746379996552593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186922592803661839995403457 140191944602746379996552593)
      ·
        refine ⟨105143958452059784997414445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140191944602746379996552593 105143958452059784997414445)
        ·
          refine ⟨39428984419522419374030417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105143958452059784997414445 39428984419522419374030417)
          ·
            refine ⟨29571738314641814530522813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39428984419522419374030417 29571738314641814530522813)
            ·
              refine ⟨11089401867990680448946055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29571738314641814530522813 11089401867990680448946055)
              ·
                refine ⟨16634102801986020673419083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11089401867990680448946055 16634102801986020673419083)
                ·
                  refine ⟨24951154202979031010128625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16634102801986020673419083 24951154202979031010128625)
                  ·
                    refine ⟨18713365652234273257596469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24951154202979031010128625 18713365652234273257596469)
                    ·
                      refine ⟨1754378029896963117899669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18713365652234273257596469 1754378029896963117899669)
                      ·
                        rfl

theorem cell23_3416639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_3416639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416639 prefixEnd_3416639 := by exact prefixLift 3416639
  have htrace : WordTrace (prefixWord ++ tailWord_3416639) baseStart_3416639 baseEnd_3416639 := by
    simpa [prefixWord, tailWord_3416639, baseEnd_3416639] using wordTrace_append hprefix tailTrace_3416639
  have hstable : (prefixWord ++ tailWord_3416639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416639).length < 2 ^ (prefixWord ++ tailWord_3416639).sum := by decide
  have hdescent : baseEnd_3416639 < baseStart_3416639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416666 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2]
def baseStart_3416666 : Nat := 118140960795 + 3416666 * 2 ^ 59
def prefixEnd_3416666 : Nat := 4983230072969 + 3 ^ 40 * 3416666 * 2
def baseEnd_3416666 : Nat := 1754391893874634512262045

theorem tailTrace_3416666 : CollatzResearch.WordTrace tailWord_3416666 prefixEnd_3416666 1754391893874634512262045 := by
  unfold tailWord_3416666
  simp only [CollatzResearch.WordTrace]
  refine ⟨31154011660002519235375463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83077364426673384627667901 31154011660002519235375463)
  ·
    refine ⟨46731017490003778853063195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31154011660002519235375463 46731017490003778853063195)
    ·
      refine ⟨70096526235005668279594793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46731017490003778853063195 70096526235005668279594793)
      ·
        refine ⟨52572394676254251209696095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70096526235005668279594793 52572394676254251209696095)
        ·
          refine ⟨78858592014381376814544143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52572394676254251209696095 78858592014381376814544143)
          ·
            refine ⟨118287888021572065221816215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78858592014381376814544143 118287888021572065221816215)
            ·
              refine ⟨177431832032358097832724323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118287888021572065221816215 177431832032358097832724323)
              ·
                refine ⟨266147748048537146749086485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177431832032358097832724323 266147748048537146749086485)
                ·
                  refine ⟨12475675689775178753863429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 266147748048537146749086485 12475675689775178753863429)
                  ·
                    refine ⟨2339189191832846016349393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12475675689775178753863429 2339189191832846016349393)
                    ·
                      refine ⟨1754391893874634512262045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2339189191832846016349393 1754391893874634512262045)
                      ·
                        rfl

theorem cell23_3416666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_3416666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416666 prefixEnd_3416666 := by exact prefixLift 3416666
  have htrace : WordTrace (prefixWord ++ tailWord_3416666) baseStart_3416666 baseEnd_3416666 := by
    simpa [prefixWord, tailWord_3416666, baseEnd_3416666] using wordTrace_append hprefix tailTrace_3416666
  have hstable : (prefixWord ++ tailWord_3416666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416666).length < 2 ^ (prefixWord ++ tailWord_3416666).sum := by decide
  have hdescent : baseEnd_3416666 < baseStart_3416666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416679 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_3416679 : Nat := 118140960795 + 3416679 * 2 ^ 59
def prefixEnd_3416679 : Nat := 4983230072969 + 3 ^ 40 * 3416679 * 2
def baseEnd_3416679 : Nat := 1754398569123142961399485

theorem tailTrace_3416679 : CollatzResearch.WordTrace tailWord_3416679 prefixEnd_3416679 1754398569123142961399485 := by
  unfold tailWord_3416679
  simp only [CollatzResearch.WordTrace]
  refine ⟨124616520788962980161725091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83077680525975320107816727 124616520788962980161725091)
  ·
    refine ⟨186924781183444470242587637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124616520788962980161725091 186924781183444470242587637)
    ·
      refine ⟨17524198235947919085242591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186924781183444470242587637 17524198235947919085242591)
      ·
        refine ⟨26286297353921878627863887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17524198235947919085242591 26286297353921878627863887)
        ·
          refine ⟨39429446030882817941795831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26286297353921878627863887 39429446030882817941795831)
          ·
            refine ⟨59144169046324226912693747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39429446030882817941795831 59144169046324226912693747)
            ·
              refine ⟨88716253569486340369040621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59144169046324226912693747 88716253569486340369040621)
              ·
                refine ⟨33268595088557377638390233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88716253569486340369040621 33268595088557377638390233)
                ·
                  refine ⟨24951446316418033228792675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33268595088557377638390233 24951446316418033228792675)
                  ·
                    refine ⟨37427169474627049843189013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24951446316418033228792675 37427169474627049843189013)
                    ·
                      refine ⟨1754398569123142961399485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37427169474627049843189013 1754398569123142961399485)
                      ·
                        rfl

theorem cell23_3416679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_3416679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416679 prefixEnd_3416679 := by exact prefixLift 3416679
  have htrace : WordTrace (prefixWord ++ tailWord_3416679) baseStart_3416679 baseEnd_3416679 := by
    simpa [prefixWord, tailWord_3416679, baseEnd_3416679] using wordTrace_append hprefix tailTrace_3416679
  have hstable : (prefixWord ++ tailWord_3416679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416679).length < 2 ^ (prefixWord ++ tailWord_3416679).sum := by decide
  have hdescent : baseEnd_3416679 < baseStart_3416679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416793 : List Nat := [1, 2, 1, 2, 3, 2, 1, 5, 1, 2, 3]
def baseStart_3416793 : Nat := 118140960795 + 3416793 * 2 ^ 59
def prefixEnd_3416793 : Nat := 4983230072969 + 3 ^ 40 * 3416793 * 2
def baseEnd_3416793 : Nat := 1754457105917755515373961

theorem tailTrace_3416793 : CollatzResearch.WordTrace tailWord_3416793 prefixEnd_3416793 1754457105917755515373961 := by
  unfold tailWord_3416793
  simp only [CollatzResearch.WordTrace]
  refine ⟨124620678710549977631375033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83080452473699985087583355 124620678710549977631375033)
  ·
    refine ⟨93465509032912483223531275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124620678710549977631375033 93465509032912483223531275)
    ·
      refine ⟨140198263549368724835296913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93465509032912483223531275 140198263549368724835296913)
      ·
        refine ⟨105148697662026543626472685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140198263549368724835296913 105148697662026543626472685)
        ·
          refine ⟨39430761623259953859927257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105148697662026543626472685 39430761623259953859927257)
          ·
            refine ⟨29573071217444965394945443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39430761623259953859927257 29573071217444965394945443)
            ·
              refine ⟨44359606826167448092418165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29573071217444965394945443 44359606826167448092418165)
              ·
                refine ⟨4158713139953198258664203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44359606826167448092418165 4158713139953198258664203)
                ·
                  refine ⟨6238069709929797387996305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4158713139953198258664203 6238069709929797387996305)
                  ·
                    refine ⟨4678552282447348040997229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6238069709929797387996305 4678552282447348040997229)
                    ·
                      refine ⟨1754457105917755515373961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4678552282447348040997229 1754457105917755515373961)
                      ·
                        rfl

theorem cell23_3416793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_3416793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416793 prefixEnd_3416793 := by exact prefixLift 3416793
  have htrace : WordTrace (prefixWord ++ tailWord_3416793) baseStart_3416793 baseEnd_3416793 := by
    simpa [prefixWord, tailWord_3416793, baseEnd_3416793] using wordTrace_append hprefix tailTrace_3416793
  have hstable : (prefixWord ++ tailWord_3416793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416793).length < 2 ^ (prefixWord ++ tailWord_3416793).sum := by decide
  have hdescent : baseEnd_3416793 < baseStart_3416793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416821 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3416821 : Nat := 118140960795 + 3416821 * 2 ^ 59
def prefixEnd_3416821 : Nat := 4983230072969 + 3 ^ 40 * 3416821 * 2
def baseEnd_3416821 : Nat := 584823827792027135274611

theorem tailTrace_3416821 : CollatzResearch.WordTrace tailWord_3416821 prefixEnd_3416821 584823827792027135274611 := by
  unfold tailWord_3416821
  simp only [CollatzResearch.WordTrace]
  refine ⟨124621699954448538413394317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83081133302965692275596211 124621699954448538413394317)
  ·
    refine ⟨46733137482918201905022869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124621699954448538413394317 46733137482918201905022869)
    ·
      refine ⟨2190615819511790714297947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46733137482918201905022869 2190615819511790714297947)
      ·
        refine ⟨3285923729267686071446921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2190615819511790714297947 3285923729267686071446921)
        ·
          refine ⟨2464442796950764553585191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3285923729267686071446921 2464442796950764553585191)
          ·
            refine ⟨3696664195426146830377787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464442796950764553585191 3696664195426146830377787)
            ·
              refine ⟨5544996293139220245566681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3696664195426146830377787 5544996293139220245566681)
              ·
                refine ⟨4158747219854415184175011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5544996293139220245566681 4158747219854415184175011)
                ·
                  refine ⟨6238120829781622776262517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4158747219854415184175011 6238120829781622776262517)
                  ·
                    refine ⟨584823827792027135274611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6238120829781622776262517 584823827792027135274611)
                    ·
                      rfl

theorem cell23_3416821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3416821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416821 prefixEnd_3416821 := by exact prefixLift 3416821
  have htrace : WordTrace (prefixWord ++ tailWord_3416821) baseStart_3416821 baseEnd_3416821 := by
    simpa [prefixWord, tailWord_3416821, baseEnd_3416821] using wordTrace_append hprefix tailTrace_3416821
  have hstable : (prefixWord ++ tailWord_3416821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416821).length < 2 ^ (prefixWord ++ tailWord_3416821).sum := by decide
  have hdescent : baseEnd_3416821 < baseStart_3416821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416856 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 2, 6]
def baseStart_3416856 : Nat := 118140960795 + 3416856 * 2 ^ 59
def prefixEnd_3416856 : Nat := 4983230072969 + 3 ^ 40 * 3416856 * 2
def baseEnd_3416856 : Nat := 584829818399662922962057

theorem tailTrace_3416856 : CollatzResearch.WordTrace tailWord_3416856 prefixEnd_3416856 584829818399662922962057 := by
  unfold tailWord_3416856
  simp only [CollatzResearch.WordTrace]
  refine ⟨62311488254660869695459211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83081984339547826260612281 62311488254660869695459211)
  ·
    refine ⟨93467232381991304543188817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62311488254660869695459211 93467232381991304543188817)
    ·
      refine ⟨70100424286493478407391613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93467232381991304543188817 70100424286493478407391613)
      ·
        refine ⟨26287659107435054402771855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70100424286493478407391613 26287659107435054402771855)
        ·
          refine ⟨39431488661152581604157783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26287659107435054402771855 39431488661152581604157783)
          ·
            refine ⟨59147232991728872406236675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39431488661152581604157783 59147232991728872406236675)
            ·
              refine ⟨88720849487593308609355013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59147232991728872406236675 88720849487593308609355013)
              ·
                refine ⟨16635159278923745364254065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88720849487593308609355013 16635159278923745364254065)
                ·
                  refine ⟨12476369459192809023190549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16635159278923745364254065 12476369459192809023190549)
                  ·
                    refine ⟨584829818399662922962057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12476369459192809023190549 584829818399662922962057)
                    ·
                      rfl

theorem cell23_3416856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 2, 6].length) (baseStart_3416856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416856 prefixEnd_3416856 := by exact prefixLift 3416856
  have htrace : WordTrace (prefixWord ++ tailWord_3416856) baseStart_3416856 baseEnd_3416856 := by
    simpa [prefixWord, tailWord_3416856, baseEnd_3416856] using wordTrace_append hprefix tailTrace_3416856
  have hstable : (prefixWord ++ tailWord_3416856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416856).length < 2 ^ (prefixWord ++ tailWord_3416856).sum := by decide
  have hdescent : baseEnd_3416856 < baseStart_3416856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416923 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 8, 5, 2]
def baseStart_3416923 : Nat := 118140960795 + 3416923 * 2 ^ 59
def prefixEnd_3416923 : Nat := 4983230072969 + 3 ^ 40 * 3416923 * 2
def baseEnd_3416923 : Nat := 1754523858402840006748363

theorem tailTrace_3416923 : CollatzResearch.WordTrace tailWord_3416923 prefixEnd_3416923 1754523858402840006748363 := by
  unfold tailWord_3416923
  simp only [CollatzResearch.WordTrace]
  refine ⟨124625420200079009833607423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83083613466719339889071615 124625420200079009833607423)
  ·
    refine ⟨186938130300118514750411135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124625420200079009833607423 186938130300118514750411135)
    ·
      refine ⟨280407195450177772125616703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186938130300118514750411135 280407195450177772125616703)
      ·
        refine ⟨420610793175266658188425055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280407195450177772125616703 420610793175266658188425055)
        ·
          refine ⟨630916189762899987282637583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420610793175266658188425055 630916189762899987282637583)
          ·
            refine ⟨946374284644349980923956375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630916189762899987282637583 946374284644349980923956375)
            ·
              refine ⟨1419561426966524971385934563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946374284644349980923956375 1419561426966524971385934563)
              ·
                refine ⟨2129342140449787457078901845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419561426966524971385934563 2129342140449787457078901845)
                ·
                  refine ⟨24953228208395946762643381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2129342140449787457078901845 24953228208395946762643381)
                  ·
                    refine ⟨2339365144537120008997817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24953228208395946762643381 2339365144537120008997817)
                    ·
                      refine ⟨1754523858402840006748363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2339365144537120008997817 1754523858402840006748363)
                      ·
                        rfl

theorem cell23_3416923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 5, 2].length) (baseStart_3416923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416923 prefixEnd_3416923 := by exact prefixLift 3416923
  have htrace : WordTrace (prefixWord ++ tailWord_3416923) baseStart_3416923 baseEnd_3416923 := by
    simpa [prefixWord, tailWord_3416923, baseEnd_3416923] using wordTrace_append hprefix tailTrace_3416923
  have hstable : (prefixWord ++ tailWord_3416923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416923).length < 2 ^ (prefixWord ++ tailWord_3416923).sum := by decide
  have hdescent : baseEnd_3416923 < baseStart_3416923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416950 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_3416950 : Nat := 118140960795 + 3416950 * 2 ^ 59
def prefixEnd_3416950 : Nat := 4983230072969 + 3 ^ 40 * 3416950 * 2
def baseEnd_3416950 : Nat := 584845907460170467036913

theorem tailTrace_3416950 : CollatzResearch.WordTrace tailWord_3416950 prefixEnd_3416950 584845907460170467036913 := by
  unfold tailWord_3416950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7789150310686324590302519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83084269980654128963226869 7789150310686324590302519)
  ·
    refine ⟨11683725466029486885453779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7789150310686324590302519 11683725466029486885453779)
    ·
      refine ⟨17525588199044230328180669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11683725466029486885453779 17525588199044230328180669)
      ·
        refine ⟨6572095574641586373067751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17525588199044230328180669 6572095574641586373067751)
        ·
          refine ⟨9858143361962379559601627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6572095574641586373067751 9858143361962379559601627)
          ·
            refine ⟨14787215042943569339402441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9858143361962379559601627 14787215042943569339402441)
            ·
              refine ⟨11090411282207677004551831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14787215042943569339402441 11090411282207677004551831)
              ·
                refine ⟨16635616923311515506827747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11090411282207677004551831 16635616923311515506827747)
                ·
                  refine ⟨24953425384967273260241621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16635616923311515506827747 24953425384967273260241621)
                  ·
                    refine ⟨584845907460170467036913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24953425384967273260241621 584845907460170467036913)
                    ·
                      rfl

theorem cell23_3416950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_3416950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416950 prefixEnd_3416950 := by exact prefixLift 3416950
  have htrace : WordTrace (prefixWord ++ tailWord_3416950) baseStart_3416950 baseEnd_3416950 := by
    simpa [prefixWord, tailWord_3416950, baseEnd_3416950] using wordTrace_append hprefix tailTrace_3416950
  have hstable : (prefixWord ++ tailWord_3416950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416950).length < 2 ^ (prefixWord ++ tailWord_3416950).sum := by decide
  have hdescent : baseEnd_3416950 < baseStart_3416950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416953 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 4]
def baseStart_3416953 : Nat := 118140960795 + 3416953 * 2 ^ 59
def prefixEnd_3416953 : Nat := 4983230072969 + 3 ^ 40 * 3416953 * 2
def baseEnd_3416953 : Nat := 1754539262822474889373225

theorem tailTrace_3416953 : CollatzResearch.WordTrace tailWord_3416953 prefixEnd_3416953 1754539262822474889373225 := by
  unfold tailWord_3416953
  simp only [CollatzResearch.WordTrace]
  refine ⟨124626514389970324957199513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83084342926646883304799675 124626514389970324957199513)
  ·
    refine ⟨93469885792477743717899635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124626514389970324957199513 93469885792477743717899635)
    ·
      refine ⟨140204828688716615576849453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93469885792477743717899635 140204828688716615576849453)
      ·
        refine ⟨52576810758268730841318545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140204828688716615576849453 52576810758268730841318545)
        ·
          refine ⟨39432608068701548130988909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52576810758268730841318545 39432608068701548130988909)
          ·
            refine ⟨14787228025763080549120841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39432608068701548130988909 14787228025763080549120841)
            ·
              refine ⟨11090421019322310411840631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14787228025763080549120841 11090421019322310411840631)
              ·
                refine ⟨16635631528983465617760947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11090421019322310411840631 16635631528983465617760947)
                ·
                  refine ⟨24953447293475198426641421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16635631528983465617760947 24953447293475198426641421)
                  ·
                    refine ⟨9357542735053199409990533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24953447293475198426641421 9357542735053199409990533)
                    ·
                      refine ⟨1754539262822474889373225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9357542735053199409990533 1754539262822474889373225)
                      ·
                        rfl

theorem cell23_3416953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_3416953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416953 prefixEnd_3416953 := by exact prefixLift 3416953
  have htrace : WordTrace (prefixWord ++ tailWord_3416953) baseStart_3416953 baseEnd_3416953 := by
    simpa [prefixWord, tailWord_3416953, baseEnd_3416953] using wordTrace_append hprefix tailTrace_3416953
  have hstable : (prefixWord ++ tailWord_3416953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416953).length < 2 ^ (prefixWord ++ tailWord_3416953).sum := by decide
  have hdescent : baseEnd_3416953 < baseStart_3416953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416970 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3416970 : Nat := 118140960795 + 3416970 * 2 ^ 59
def prefixEnd_3416970 : Nat := 4983230072969 + 3 ^ 40 * 3416970 * 2
def baseEnd_3416970 : Nat := 1754547991993601322860647

theorem tailTrace_3416970 : CollatzResearch.WordTrace tailWord_3416970 prefixEnd_3416970 1754547991993601322860647 := by
  unfold tailWord_3416970
  simp only [CollatzResearch.WordTrace]
  refine ⟨31156783607727184215142091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83084756287272491240378909 31156783607727184215142091)
  ·
    refine ⟨46735175411590776322713137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31156783607727184215142091 46735175411590776322713137)
    ·
      refine ⟨35051381558693082242034853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46735175411590776322713137 35051381558693082242034853)
      ·
        refine ⟨6572134042254952920381535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35051381558693082242034853 6572134042254952920381535)
        ·
          refine ⟨9858201063382429380572303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6572134042254952920381535 9858201063382429380572303)
          ·
            refine ⟨14787301595073644070858455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9858201063382429380572303 14787301595073644070858455)
            ·
              refine ⟨22180952392610466106287683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14787301595073644070858455 22180952392610466106287683)
              ·
                refine ⟨33271428588915699159431525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22180952392610466106287683 33271428588915699159431525)
                ·
                  refine ⟨6238392860421693592393411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33271428588915699159431525 6238392860421693592393411)
                  ·
                    refine ⟨9357589290632540388590117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6238392860421693592393411 9357589290632540388590117)
                    ·
                      refine ⟨1754547991993601322860647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9357589290632540388590117 1754547991993601322860647)
                      ·
                        rfl

theorem cell23_3416970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3416970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416970 prefixEnd_3416970 := by exact prefixLift 3416970
  have htrace : WordTrace (prefixWord ++ tailWord_3416970) baseStart_3416970 baseEnd_3416970 := by
    simpa [prefixWord, tailWord_3416970, baseEnd_3416970] using wordTrace_append hprefix tailTrace_3416970
  have hstable : (prefixWord ++ tailWord_3416970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416970).length < 2 ^ (prefixWord ++ tailWord_3416970).sum := by decide
  have hdescent : baseEnd_3416970 < baseStart_3416970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3416976 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 12]
def baseStart_3416976 : Nat := 118140960795 + 3416976 * 2 ^ 59
def prefixEnd_3416976 : Nat := 4983230072969 + 3 ^ 40 * 3416976 * 2
def baseEnd_3416976 : Nat := 194950119208614255487291

theorem tailTrace_3416976 : CollatzResearch.WordTrace tailWord_3416976 prefixEnd_3416976 194950119208614255487291 := by
  unfold tailWord_3416976
  simp only [CollatzResearch.WordTrace]
  refine ⟨62313676634443499942643391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83084902179257999923524521 62313676634443499942643391)
  ·
    refine ⟨93470514951665249913965087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62313676634443499942643391 93470514951665249913965087)
    ·
      refine ⟨140205772427497874870947631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93470514951665249913965087 140205772427497874870947631)
      ·
        refine ⟨210308658641246812306421447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140205772427497874870947631 210308658641246812306421447)
        ·
          refine ⟨315462987961870218459632171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210308658641246812306421447 315462987961870218459632171)
          ·
            refine ⟨473194481942805327689448257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315462987961870218459632171 473194481942805327689448257)
            ·
              refine ⟨354895861457103995767086193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473194481942805327689448257 354895861457103995767086193)
              ·
                refine ⟨266171896092827996825314645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354895861457103995767086193 266171896092827996825314645)
                ·
                  refine ⟨194950119208614255487291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 266171896092827996825314645 194950119208614255487291)
                  ·
                    rfl

theorem cell23_3416976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 12].length) (baseStart_3416976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3416976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3416976 prefixEnd_3416976 := by exact prefixLift 3416976
  have htrace : WordTrace (prefixWord ++ tailWord_3416976) baseStart_3416976 baseEnd_3416976 := by
    simpa [prefixWord, tailWord_3416976, baseEnd_3416976] using wordTrace_append hprefix tailTrace_3416976
  have hstable : (prefixWord ++ tailWord_3416976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3416976).length < 2 ^ (prefixWord ++ tailWord_3416976).sum := by decide
  have hdescent : baseEnd_3416976 < baseStart_3416976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3416976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417060 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 1, 8, 2]
def baseStart_3417060 : Nat := 118140960795 + 3417060 * 2 ^ 59
def prefixEnd_3417060 : Nat := 4983230072969 + 3 ^ 40 * 3417060 * 2
def baseEnd_3417060 : Nat := 1754594205252505970735233

theorem tailTrace_3417060 : CollatzResearch.WordTrace tailWord_3417060 prefixEnd_3417060 1754594205252505970735233 := by
  unfold tailWord_3417060
  simp only [CollatzResearch.WordTrace]
  refine ⟨62315208500291341115672317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83086944667055121487563089 62315208500291341115672317)
  ·
    refine ⟨23368203187609252918377119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62315208500291341115672317 23368203187609252918377119)
    ·
      refine ⟨35052304781413879377565679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23368203187609252918377119 35052304781413879377565679)
      ·
        refine ⟨52578457172120819066348519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35052304781413879377565679 52578457172120819066348519)
        ·
          refine ⟨78867685758181228599522779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52578457172120819066348519 78867685758181228599522779)
          ·
            refine ⟨118301528637271842899284169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78867685758181228599522779 118301528637271842899284169)
            ·
              refine ⟨88726146477953882174463127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118301528637271842899284169 88726146477953882174463127)
              ·
                refine ⟨133089219716930823261694691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88726146477953882174463127 133089219716930823261694691)
                ·
                  refine ⟨199633829575396234892542037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133089219716930823261694691 199633829575396234892542037)
                  ·
                    refine ⟨2339458940336674627646977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 199633829575396234892542037 2339458940336674627646977)
                    ·
                      refine ⟨1754594205252505970735233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2339458940336674627646977 1754594205252505970735233)
                      ·
                        rfl

theorem cell23_3417060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_3417060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417060 prefixEnd_3417060 := by exact prefixLift 3417060
  have htrace : WordTrace (prefixWord ++ tailWord_3417060) baseStart_3417060 baseEnd_3417060 := by
    simpa [prefixWord, tailWord_3417060, baseEnd_3417060] using wordTrace_append hprefix tailTrace_3417060
  have hstable : (prefixWord ++ tailWord_3417060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417060).length < 2 ^ (prefixWord ++ tailWord_3417060).sum := by decide
  have hdescent : baseEnd_3417060 < baseStart_3417060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417074 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_3417074 : Nat := 118140960795 + 3417074 * 2 ^ 59
def prefixEnd_3417074 : Nat := 4983230072969 + 3 ^ 40 * 3417074 * 2
def baseEnd_3417074 : Nat := 584867131327222971986723

theorem tailTrace_3417074 : CollatzResearch.WordTrace tailWord_3417074 prefixEnd_3417074 584867131327222971986723 := by
  unfold tailWord_3417074
  simp only [CollatzResearch.WordTrace]
  refine ⟨31157731905632990655588569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83087285081687975081569517 31157731905632990655588569)
  ·
    refine ⟨23368298929224742991691427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31157731905632990655588569 23368298929224742991691427)
    ·
      refine ⟨35052448393837114487537141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23368298929224742991691427 35052448393837114487537141)
      ·
        refine ⟨3286167036922229483206607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35052448393837114487537141 3286167036922229483206607)
        ·
          refine ⟨4929250555383344224809911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286167036922229483206607 4929250555383344224809911)
          ·
            refine ⟨7393875833075016337214867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929250555383344224809911 7393875833075016337214867)
            ·
              refine ⟨11090813749612524505822301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7393875833075016337214867 11090813749612524505822301)
              ·
                refine ⟨4159055156104696689683363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11090813749612524505822301 4159055156104696689683363)
                ·
                  refine ⟨6238582734157045034525045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159055156104696689683363 6238582734157045034525045)
                  ·
                    refine ⟨584867131327222971986723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6238582734157045034525045 584867131327222971986723)
                    ·
                      rfl

theorem cell23_3417074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_3417074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417074 prefixEnd_3417074 := by exact prefixLift 3417074
  have htrace : WordTrace (prefixWord ++ tailWord_3417074) baseStart_3417074 baseEnd_3417074 := by
    simpa [prefixWord, tailWord_3417074, baseEnd_3417074] using wordTrace_append hprefix tailTrace_3417074
  have hstable : (prefixWord ++ tailWord_3417074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417074).length < 2 ^ (prefixWord ++ tailWord_3417074).sum := by decide
  have hdescent : baseEnd_3417074 < baseStart_3417074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417113 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 2, 7]
def baseStart_3417113 : Nat := 118140960795 + 3417113 * 2 ^ 59
def prefixEnd_3417113 : Nat := 4983230072969 + 3 ^ 40 * 3417113 * 2
def baseEnd_3417113 : Nat := 584873806575731421124163

theorem tailTrace_3417113 : CollatzResearch.WordTrace tailWord_3417113 prefixEnd_3417113 584873806575731421124163 := by
  unfold tailWord_3417113
  simp only [CollatzResearch.WordTrace]
  refine ⟨124632350069390672283023993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83088233379593781522015995 124632350069390672283023993)
  ·
    refine ⟨93474262552043004212267995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124632350069390672283023993 93474262552043004212267995)
    ·
      refine ⟨140211393828064506318401993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93474262552043004212267995 140211393828064506318401993)
      ·
        refine ⟨105158545371048379738801495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140211393828064506318401993 105158545371048379738801495)
        ·
          refine ⟨157737818056572569608202243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105158545371048379738801495 157737818056572569608202243)
          ·
            refine ⟨236606727084858854412303365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157737818056572569608202243 236606727084858854412303365)
            ·
              refine ⟨44363761328411035202306881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236606727084858854412303365 44363761328411035202306881)
              ·
                refine ⟨33272820996308276401730161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44363761328411035202306881 33272820996308276401730161)
                ·
                  refine ⟨24954615747231207301297621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33272820996308276401730161 24954615747231207301297621)
                  ·
                    refine ⟨584873806575731421124163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24954615747231207301297621 584873806575731421124163)
                    ·
                      rfl

theorem cell23_3417113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_3417113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417113 prefixEnd_3417113 := by exact prefixLift 3417113
  have htrace : WordTrace (prefixWord ++ tailWord_3417113) baseStart_3417113 baseEnd_3417113 := by
    simpa [prefixWord, tailWord_3417113, baseEnd_3417113] using wordTrace_append hprefix tailTrace_3417113
  have hstable : (prefixWord ++ tailWord_3417113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417113).length < 2 ^ (prefixWord ++ tailWord_3417113).sum := by decide
  have hdescent : baseEnd_3417113 < baseStart_3417113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417207 : List Nat := [1, 1, 3, 1, 1, 4, 3, 4, 5]
def baseStart_3417207 : Nat := 118140960795 + 3417207 * 2 ^ 59
def prefixEnd_3417207 : Nat := 4983230072969 + 3 ^ 40 * 3417207 * 2
def baseEnd_3417207 : Nat := 194963298545412988399673

theorem tailTrace_3417207 : CollatzResearch.WordTrace tailWord_3417207 prefixEnd_3417207 194963298545412988399673 := by
  unfold tailWord_3417207
  simp only [CollatzResearch.WordTrace]
  refine ⟨124635778531050126336945875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83090519020700084224630583 124635778531050126336945875)
  ·
    refine ⟨186953667796575189505418813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124635778531050126336945875 186953667796575189505418813)
    ·
      refine ⟨70107625423715696064532055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186953667796575189505418813 70107625423715696064532055)
      ·
        refine ⟨105161438135573544096798083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70107625423715696064532055 105161438135573544096798083)
        ·
          refine ⟨157742157203360316145197125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105161438135573544096798083 157742157203360316145197125)
          ·
            refine ⟨29576654475630059277224461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157742157203360316145197125 29576654475630059277224461)
            ·
              refine ⟨11091245428361272228959173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29576654475630059277224461 11091245428361272228959173)
              ·
                refine ⟨2079608517817738542929845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11091245428361272228959173 2079608517817738542929845)
                ·
                  refine ⟨194963298545412988399673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2079608517817738542929845 194963298545412988399673)
                  ·
                    rfl

theorem cell23_3417207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 5].length) (baseStart_3417207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417207 prefixEnd_3417207 := by exact prefixLift 3417207
  have htrace : WordTrace (prefixWord ++ tailWord_3417207) baseStart_3417207 baseEnd_3417207 := by
    simpa [prefixWord, tailWord_3417207, baseEnd_3417207] using wordTrace_append hprefix tailTrace_3417207
  have hstable : (prefixWord ++ tailWord_3417207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417207).length < 2 ^ (prefixWord ++ tailWord_3417207).sum := by decide
  have hdescent : baseEnd_3417207 < baseStart_3417207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417217 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_3417217 : Nat := 118140960795 + 3417217 * 2 ^ 59
def prefixEnd_3417217 : Nat := 4983230072969 + 3 ^ 40 * 3417217 * 2
def baseEnd_3417217 : Nat := 1754674821715261856472011

theorem tailTrace_3417217 : CollatzResearch.WordTrace tailWord_3417217 prefixEnd_3417217 1754674821715261856472011 := by
  unfold tailWord_3417217
  simp only [CollatzResearch.WordTrace]
  refine ⟨124636143261013898044809905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83090762174009265363206603 124636143261013898044809905)
  ·
    refine ⟨93477107445760423533607429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124636143261013898044809905 93477107445760423533607429)
    ·
      refine ⟨17526957646080079412551393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93477107445760423533607429 17526957646080079412551393)
      ·
        refine ⟨13145218234560059559413545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17526957646080079412551393 13145218234560059559413545)
        ·
          refine ⟨9858913675920044669560159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13145218234560059559413545 9858913675920044669560159)
          ·
            refine ⟨14788370513880067004340239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9858913675920044669560159 14788370513880067004340239)
            ·
              refine ⟨22182555770820100506510359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14788370513880067004340239 22182555770820100506510359)
              ·
                refine ⟨33273833656230150759765539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22182555770820100506510359 33273833656230150759765539)
                ·
                  refine ⟨49910750484345226139648309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33273833656230150759765539 49910750484345226139648309)
                  ·
                    refine ⟨4679132857907364950592029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49910750484345226139648309 4679132857907364950592029)
                    ·
                      refine ⟨1754674821715261856472011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4679132857907364950592029 1754674821715261856472011)
                      ·
                        rfl

theorem cell23_3417217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_3417217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417217 prefixEnd_3417217 := by exact prefixLift 3417217
  have htrace : WordTrace (prefixWord ++ tailWord_3417217) baseStart_3417217 baseEnd_3417217 := by
    simpa [prefixWord, tailWord_3417217, baseEnd_3417217] using wordTrace_append hprefix tailTrace_3417217
  have hstable : (prefixWord ++ tailWord_3417217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417217).length < 2 ^ (prefixWord ++ tailWord_3417217).sum := by decide
  have hdescent : baseEnd_3417217 < baseStart_3417217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417267 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 3, 4]
def baseStart_3417267 : Nat := 118140960795 + 3417267 * 2 ^ 59
def prefixEnd_3417267 : Nat := 4983230072969 + 3 ^ 40 * 3417267 * 2
def baseEnd_3417267 : Nat := 584900165249328886948927

theorem tailTrace_3417267 : CollatzResearch.WordTrace tailWord_3417267 prefixEnd_3417267 584900165249328886948927 := by
  unfold tailWord_3417267
  simp only [CollatzResearch.WordTrace]
  refine ⟨124637966910832756584130055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83091977940555171056086703 124637966910832756584130055)
  ·
    refine ⟨186956950366249134876195083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124637966910832756584130055 186956950366249134876195083)
    ·
      refine ⟨280435425549373702314292625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186956950366249134876195083 280435425549373702314292625)
      ·
        refine ⟨210326569162030276735719469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280435425549373702314292625 210326569162030276735719469)
        ·
          refine ⟨78872463435761353775894801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210326569162030276735719469 78872463435761353775894801)
          ·
            refine ⟨59154347576821015331921101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78872463435761353775894801 59154347576821015331921101)
            ·
              refine ⟨22182880341307880749470413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59154347576821015331921101 22182880341307880749470413)
              ·
                refine ⟨8318580127990455281051405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22182880341307880749470413 8318580127990455281051405)
                ·
                  refine ⟨3119467547996420730394277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8318580127990455281051405 3119467547996420730394277)
                  ·
                    refine ⟨584900165249328886948927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3119467547996420730394277 584900165249328886948927)
                    ·
                      rfl

theorem cell23_3417267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 4].length) (baseStart_3417267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417267 prefixEnd_3417267 := by exact prefixLift 3417267
  have htrace : WordTrace (prefixWord ++ tailWord_3417267) baseStart_3417267 baseEnd_3417267 := by
    simpa [prefixWord, tailWord_3417267, baseEnd_3417267] using wordTrace_append hprefix tailTrace_3417267
  have hstable : (prefixWord ++ tailWord_3417267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417267).length < 2 ^ (prefixWord ++ tailWord_3417267).sum := by decide
  have hdescent : baseEnd_3417267 < baseStart_3417267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417277 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 1, 4, 3]
def baseStart_3417277 : Nat := 118140960795 + 3417277 * 2 ^ 59
def prefixEnd_3417277 : Nat := 4983230072969 + 3 ^ 40 * 3417277 * 2
def baseEnd_3417277 : Nat := 1754705630554531621721735

theorem tailTrace_3417277 : CollatzResearch.WordTrace tailWord_3417277 prefixEnd_3417277 1754705630554531621721735 := by
  unfold tailWord_3417277
  simp only [CollatzResearch.WordTrace]
  refine ⟨124638331640796528291994085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83092221093864352194662723 124638331640796528291994085)
  ·
    refine ⟨23369687182649349054748891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124638331640796528291994085 23369687182649349054748891)
    ·
      refine ⟨35054530773974023582123337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23369687182649349054748891 35054530773974023582123337)
      ·
        refine ⟨26290898080480517686592503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35054530773974023582123337 26290898080480517686592503)
        ·
          refine ⟨39436347120720776529888755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26290898080480517686592503 39436347120720776529888755)
          ·
            refine ⟨59154520681081164794833133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39436347120720776529888755 59154520681081164794833133)
            ·
              refine ⟨22182945255405436798062425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59154520681081164794833133 22182945255405436798062425)
              ·
                refine ⟨16637208941554077598546819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22182945255405436798062425 16637208941554077598546819)
                ·
                  refine ⟨24955813412331116397820229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16637208941554077598546819 24955813412331116397820229)
                  ·
                    refine ⟨4679215014812084324591293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24955813412331116397820229 4679215014812084324591293)
                    ·
                      refine ⟨1754705630554531621721735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4679215014812084324591293 1754705630554531621721735)
                      ·
                        rfl

theorem cell23_3417277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_3417277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417277 prefixEnd_3417277 := by exact prefixLift 3417277
  have htrace : WordTrace (prefixWord ++ tailWord_3417277) baseStart_3417277 baseEnd_3417277 := by
    simpa [prefixWord, tailWord_3417277, baseEnd_3417277] using wordTrace_append hprefix tailTrace_3417277
  have hstable : (prefixWord ++ tailWord_3417277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417277).length < 2 ^ (prefixWord ++ tailWord_3417277).sum := by decide
  have hdescent : baseEnd_3417277 < baseStart_3417277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417377 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_3417377 : Nat := 118140960795 + 3417377 * 2 ^ 59
def prefixEnd_3417377 : Nat := 4983230072969 + 3 ^ 40 * 3417377 * 2
def baseEnd_3417377 : Nat := 1754756978619981230471275

theorem tailTrace_3417377 : CollatzResearch.WordTrace tailWord_3417377 prefixEnd_3417377 1754756978619981230471275 := by
  unfold tailWord_3417377
  simp only [CollatzResearch.WordTrace]
  refine ⟨124641978940434245370634385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83094652626956163580422923 124641978940434245370634385)
  ·
    refine ⟨93481484205325684027975789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124641978940434245370634385 93481484205325684027975789)
    ·
      refine ⟨35055556576997131510490921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93481484205325684027975789 35055556576997131510490921)
      ·
        refine ⟨26291667432747848632868191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35055556576997131510490921 26291667432747848632868191)
        ·
          refine ⟨39437501149121772949302287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26291667432747848632868191 39437501149121772949302287)
          ·
            refine ⟨59156251723682659423953431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39437501149121772949302287 59156251723682659423953431)
            ·
              refine ⟨88734377585523989135930147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59156251723682659423953431 88734377585523989135930147)
              ·
                refine ⟨133101566378285983703895221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88734377585523989135930147 133101566378285983703895221)
                ·
                  refine ⟨12478271847964310972240177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133101566378285983703895221 12478271847964310972240177)
                  ·
                    refine ⟨9358703885973233229180133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12478271847964310972240177 9358703885973233229180133)
                    ·
                      refine ⟨1754756978619981230471275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9358703885973233229180133 1754756978619981230471275)
                      ·
                        rfl

theorem cell23_3417377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_3417377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417377 prefixEnd_3417377 := by exact prefixLift 3417377
  have htrace : WordTrace (prefixWord ++ tailWord_3417377) baseStart_3417377 baseEnd_3417377 := by
    simpa [prefixWord, tailWord_3417377, baseEnd_3417377] using wordTrace_append hprefix tailTrace_3417377
  have hstable : (prefixWord ++ tailWord_3417377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417377).length < 2 ^ (prefixWord ++ tailWord_3417377).sum := by decide
  have hdescent : baseEnd_3417377 < baseStart_3417377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417394 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4]
def baseStart_3417394 : Nat := 118140960795 + 3417394 * 2 ^ 59
def prefixEnd_3417394 : Nat := 4983230072969 + 3 ^ 40 * 3417394 * 2
def baseEnd_3417394 : Nat := 1754765707791107663958697

theorem tailTrace_3417394 : CollatzResearch.WordTrace tailWord_3417394 prefixEnd_3417394 1754765707791107663958697 := by
  unfold tailWord_3417394
  simp only [CollatzResearch.WordTrace]
  refine ⟨31160649745343164318500809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83095065987581771516002157 31160649745343164318500809)
  ·
    refine ⟨23370487309007373238875607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31160649745343164318500809 23370487309007373238875607)
    ·
      refine ⟨35055730963511059858313411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23370487309007373238875607 35055730963511059858313411)
      ·
        refine ⟨52583596445266589787470117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35055730963511059858313411 52583596445266589787470117)
        ·
          refine ⟨9859424333487485585150647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52583596445266589787470117 9859424333487485585150647)
          ·
            refine ⟨14789136500231228377725971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9859424333487485585150647 14789136500231228377725971)
            ·
              refine ⟨22183704750346842566588957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14789136500231228377725971 22183704750346842566588957)
              ·
                refine ⟨8318889281380065962470859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22183704750346842566588957 8318889281380065962470859)
                ·
                  refine ⟨12478333922070098943706289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8318889281380065962470859 12478333922070098943706289)
                  ·
                    refine ⟨9358750441552574207779717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12478333922070098943706289 9358750441552574207779717)
                    ·
                      refine ⟨1754765707791107663958697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9358750441552574207779717 1754765707791107663958697)
                      ·
                        rfl

theorem cell23_3417394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_3417394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417394 prefixEnd_3417394 := by exact prefixLift 3417394
  have htrace : WordTrace (prefixWord ++ tailWord_3417394) baseStart_3417394 baseEnd_3417394 := by
    simpa [prefixWord, tailWord_3417394, baseEnd_3417394] using wordTrace_append hprefix tailTrace_3417394
  have hstable : (prefixWord ++ tailWord_3417394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417394).length < 2 ^ (prefixWord ++ tailWord_3417394).sum := by decide
  have hdescent : baseEnd_3417394 < baseStart_3417394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417404 : List Nat := [2, 2, 2, 2, 1, 4, 3, 7]
def baseStart_3417404 : Nat := 118140960795 + 3417404 * 2 ^ 59
def prefixEnd_3417404 : Nat := 4983230072969 + 3 ^ 40 * 3417404 * 2
def baseEnd_3417404 : Nat := 64991512688801949067913

theorem tailTrace_3417404 : CollatzResearch.WordTrace tailWord_3417404 prefixEnd_3417404 64991512688801949067913 := by
  unfold tailWord_3417404
  simp only [CollatzResearch.WordTrace]
  refine ⟨62321481855668214490933633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83095309140890952654578177 62321481855668214490933633)
  ·
    refine ⟨46741111391751160868200225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62321481855668214490933633 46741111391751160868200225)
    ·
      refine ⟨35055833543813370651150169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46741111391751160868200225 35055833543813370651150169)
      ·
        refine ⟨26291875157860027988362627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35055833543813370651150169 26291875157860027988362627)
        ·
          refine ⟨39437812736790041982543941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26291875157860027988362627 39437812736790041982543941)
          ·
            refine ⟨7394589888148132871726989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39437812736790041982543941 7394589888148132871726989)
            ·
              refine ⟨2772971208055549826897621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7394589888148132871726989 2772971208055549826897621)
              ·
                refine ⟨64991512688801949067913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2772971208055549826897621 64991512688801949067913)
                ·
                  rfl

theorem cell23_3417404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 7].length) (baseStart_3417404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417404 prefixEnd_3417404 := by exact prefixLift 3417404
  have htrace : WordTrace (prefixWord ++ tailWord_3417404) baseStart_3417404 baseEnd_3417404 := by
    simpa [prefixWord, tailWord_3417404, baseEnd_3417404] using wordTrace_append hprefix tailTrace_3417404
  have hstable : (prefixWord ++ tailWord_3417404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417404).length < 2 ^ (prefixWord ++ tailWord_3417404).sum := by decide
  have hdescent : baseEnd_3417404 < baseStart_3417404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417415 : List Nat := [1, 1, 4, 1, 2, 4, 2, 3, 1, 2, 2]
def baseStart_3417415 : Nat := 118140960795 + 3417415 * 2 ^ 59
def prefixEnd_3417415 : Nat := 4983230072969 + 3 ^ 40 * 3417415 * 2
def baseEnd_3417415 : Nat := 1754776490884852081796101

theorem tailTrace_3417415 : CollatzResearch.WordTrace tailWord_3417415 prefixEnd_3417415 1754776490884852081796101 := by
  unfold tailWord_3417415
  simp only [CollatzResearch.WordTrace]
  refine ⟨124643364914296577860517699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83095576609531051907011799 124643364914296577860517699)
  ·
    refine ⟨186965047371444866790776549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124643364914296577860517699 186965047371444866790776549)
    ·
      refine ⟨35055946382145912523270603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186965047371444866790776549 35055946382145912523270603)
      ·
        refine ⟨52583919573218868784905905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35055946382145912523270603 52583919573218868784905905)
        ·
          refine ⟨39437939679914151588679429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52583919573218868784905905 39437939679914151588679429)
          ·
            refine ⟨7394613689983903422877393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39437939679914151588679429 7394613689983903422877393)
            ·
              refine ⟨5545960267487927567158045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7394613689983903422877393 5545960267487927567158045)
              ·
                refine ⟨2079735100307972837684267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5545960267487927567158045 2079735100307972837684267)
                ·
                  refine ⟨3119602650461959256526401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079735100307972837684267 3119602650461959256526401)
                  ·
                    refine ⟨2339701987846469442394801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3119602650461959256526401 2339701987846469442394801)
                    ·
                      refine ⟨1754776490884852081796101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2339701987846469442394801 1754776490884852081796101)
                      ·
                        rfl

theorem cell23_3417415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_3417415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417415 prefixEnd_3417415 := by exact prefixLift 3417415
  have htrace : WordTrace (prefixWord ++ tailWord_3417415) baseStart_3417415 baseEnd_3417415 := by
    simpa [prefixWord, tailWord_3417415, baseEnd_3417415] using wordTrace_append hprefix tailTrace_3417415
  have hstable : (prefixWord ++ tailWord_3417415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417415).length < 2 ^ (prefixWord ++ tailWord_3417415).sum := by decide
  have hdescent : baseEnd_3417415 < baseStart_3417415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417421 : List Nat := [1, 6, 1, 3, 1, 1, 10]
def baseStart_3417421 : Nat := 118140960795 + 3417421 * 2 ^ 59
def prefixEnd_3417421 : Nat := 4983230072969 + 3 ^ 40 * 3417421 * 2
def baseEnd_3417421 : Nat := 21663945330478753806433

theorem tailTrace_3417421 : CollatzResearch.WordTrace tailWord_3417421 prefixEnd_3417421 21663945330478753806433 := by
  unfold tailWord_3417421
  simp only [CollatzResearch.WordTrace]
  refine ⟨124643583752274840885236117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83095722501516560590157411 124643583752274840885236117)
  ·
    refine ⟨5842667988387883166495443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124643583752274840885236117 5842667988387883166495443)
    ·
      refine ⟨8764001982581824749743165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5842667988387883166495443 8764001982581824749743165)
      ·
        refine ⟨3286500743468184281153687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8764001982581824749743165 3286500743468184281153687)
        ·
          refine ⟨4929751115202276421730531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286500743468184281153687 4929751115202276421730531)
          ·
            refine ⟨7394626672803414632595797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929751115202276421730531 7394626672803414632595797)
            ·
              refine ⟨21663945330478753806433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7394626672803414632595797 21663945330478753806433)
              ·
                rfl

theorem cell23_3417421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 10].length) (baseStart_3417421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417421 prefixEnd_3417421 := by exact prefixLift 3417421
  have htrace : WordTrace (prefixWord ++ tailWord_3417421) baseStart_3417421 baseEnd_3417421 := by
    simpa [prefixWord, tailWord_3417421, baseEnd_3417421] using wordTrace_append hprefix tailTrace_3417421
  have hstable : (prefixWord ++ tailWord_3417421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417421).length < 2 ^ (prefixWord ++ tailWord_3417421).sum := by decide
  have hdescent : baseEnd_3417421 < baseStart_3417421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417431 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 4, 1, 3]
def baseStart_3417431 : Nat := 118140960795 + 3417431 * 2 ^ 59
def prefixEnd_3417431 : Nat := 4983230072969 + 3 ^ 40 * 3417431 * 2
def baseEnd_3417431 : Nat := 1754784706575324019196027

theorem tailTrace_3417431 : CollatzResearch.WordTrace tailWord_3417431 prefixEnd_3417431 1754784706575324019196027 := by
  unfold tailWord_3417431
  simp only [CollatzResearch.WordTrace]
  refine ⟨124643948482238612593100147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83095965654825741728733431 124643948482238612593100147)
  ·
    refine ⟨186965922723357918889650221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124643948482238612593100147 186965922723357918889650221)
    ·
      refine ⟨70112221021259219583618833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186965922723357918889650221 70112221021259219583618833)
      ·
        refine ⟨52584165765944414687714125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70112221021259219583618833 52584165765944414687714125)
        ·
          refine ⟨19719062162229155507892797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52584165765944414687714125 19719062162229155507892797)
          ·
            refine ⟨7394648310835933315459799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19719062162229155507892797 7394648310835933315459799)
            ·
              refine ⟨11091972466253899973189699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7394648310835933315459799 11091972466253899973189699)
              ·
                refine ⟨16637958699380849959784549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11091972466253899973189699 16637958699380849959784549)
                ·
                  refine ⟨3119617256133909367459603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16637958699380849959784549 3119617256133909367459603)
                  ·
                    refine ⟨4679425884200864051189405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3119617256133909367459603 4679425884200864051189405)
                    ·
                      refine ⟨1754784706575324019196027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4679425884200864051189405 1754784706575324019196027)
                      ·
                        rfl

theorem cell23_3417431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_3417431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417431 prefixEnd_3417431 := by exact prefixLift 3417431
  have htrace : WordTrace (prefixWord ++ tailWord_3417431) baseStart_3417431 baseEnd_3417431 := by
    simpa [prefixWord, tailWord_3417431, baseEnd_3417431] using wordTrace_append hprefix tailTrace_3417431
  have hstable : (prefixWord ++ tailWord_3417431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417431).length < 2 ^ (prefixWord ++ tailWord_3417431).sum := by decide
  have hdescent : baseEnd_3417431 < baseStart_3417431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417448 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 1, 3, 3]
def baseStart_3417448 : Nat := 118140960795 + 3417448 * 2 ^ 59
def prefixEnd_3417448 : Nat := 4983230072969 + 3 ^ 40 * 3417448 * 2
def baseEnd_3417448 : Nat := 1754793435746450452683449

theorem tailTrace_3417448 : CollatzResearch.WordTrace tailWord_3417448 prefixEnd_3417448 1754793435746450452683449 := by
  unfold tailWord_3417448
  simp only [CollatzResearch.WordTrace]
  refine ⟨62322284261588512248234499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83096379015451349664312665 62322284261588512248234499)
  ·
    refine ⟨93483426392382768372351749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62322284261588512248234499 93483426392382768372351749)
    ·
      refine ⟨17528142448571769069815953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93483426392382768372351749 17528142448571769069815953)
      ·
        refine ⟨13146106836428826802361965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17528142448571769069815953 13146106836428826802361965)
        ·
          refine ⟨4929790063660810050885737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13146106836428826802361965 4929790063660810050885737)
          ·
            refine ⟨3697342547745607538164303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4929790063660810050885737 3697342547745607538164303)
            ·
              refine ⟨5546013821618411307246455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3697342547745607538164303 5546013821618411307246455)
              ·
                refine ⟨8319020732427616960869683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5546013821618411307246455 8319020732427616960869683)
                ·
                  refine ⟨12478531098641425441304525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8319020732427616960869683 12478531098641425441304525)
                  ·
                    refine ⟨4679449161990534540489197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12478531098641425441304525 4679449161990534540489197)
                    ·
                      refine ⟨1754793435746450452683449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4679449161990534540489197 1754793435746450452683449)
                      ·
                        rfl

theorem cell23_3417448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_3417448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417448 prefixEnd_3417448 := by exact prefixLift 3417448
  have htrace : WordTrace (prefixWord ++ tailWord_3417448) baseStart_3417448 baseEnd_3417448 := by
    simpa [prefixWord, tailWord_3417448, baseEnd_3417448] using wordTrace_append hprefix tailTrace_3417448
  have hstable : (prefixWord ++ tailWord_3417448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417448).length < 2 ^ (prefixWord ++ tailWord_3417448).sum := by decide
  have hdescent : baseEnd_3417448 < baseStart_3417448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417458 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 1, 3, 2]
def baseStart_3417458 : Nat := 118140960795 + 3417458 * 2 ^ 59
def prefixEnd_3417458 : Nat := 4983230072969 + 3 ^ 40 * 3417458 * 2
def baseEnd_3417458 : Nat := 1754798570552995413558403

theorem tailTrace_3417458 : CollatzResearch.WordTrace tailWord_3417458 prefixEnd_3417458 1754798570552995413558403 := by
  unfold tailWord_3417458
  simp only [CollatzResearch.WordTrace]
  refine ⟨31161233313285199051083257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83096622168760530802888685 31161233313285199051083257)
  ·
    refine ⟨23370924984963899288312443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31161233313285199051083257 23370924984963899288312443)
    ·
      refine ⟨35056387477445848932468665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23370924984963899288312443 35056387477445848932468665)
      ·
        refine ⟨26292290608084386699351499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35056387477445848932468665 26292290608084386699351499)
        ·
          refine ⟨39438435912126580049027249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26292290608084386699351499 39438435912126580049027249)
          ·
            refine ⟨29578826934094935036770437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39438435912126580049027249 29578826934094935036770437)
            ·
              refine ⟨5546030050142800319394457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29578826934094935036770437 5546030050142800319394457)
              ·
                refine ⟨4159522537607100239545843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5546030050142800319394457 4159522537607100239545843)
                ·
                  refine ⟨6239283806410650359318765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159522537607100239545843 6239283806410650359318765)
                  ·
                    refine ⟨2339731427403993884744537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6239283806410650359318765 2339731427403993884744537)
                    ·
                      refine ⟨1754798570552995413558403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2339731427403993884744537 1754798570552995413558403)
                      ·
                        rfl

theorem cell23_3417458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_3417458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417458 prefixEnd_3417458 := by exact prefixLift 3417458
  have htrace : WordTrace (prefixWord ++ tailWord_3417458) baseStart_3417458 baseEnd_3417458 := by
    simpa [prefixWord, tailWord_3417458, baseEnd_3417458] using wordTrace_append hprefix tailTrace_3417458
  have hstable : (prefixWord ++ tailWord_3417458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417458).length < 2 ^ (prefixWord ++ tailWord_3417458).sum := by decide
  have hdescent : baseEnd_3417458 < baseStart_3417458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417477 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 9]
def baseStart_3417477 : Nat := 118140960795 + 3417477 * 2 ^ 59
def prefixEnd_3417477 : Nat := 4983230072969 + 3 ^ 40 * 3417477 * 2
def baseEnd_3417477 : Nat := 194978702965047871024535

theorem tailTrace_3417477 : CollatzResearch.WordTrace tailWord_3417477 prefixEnd_3417477 194978702965047871024535 := by
  unfold tailWord_3417477
  simp only [CollatzResearch.WordTrace]
  refine ⟨124645626240071962449274685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83097084160047974966183123 124645626240071962449274685)
  ·
    refine ⟨46742109840026985918478007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124645626240071962449274685 46742109840026985918478007)
    ·
      refine ⟨70113164760040478877717011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46742109840026985918478007 70113164760040478877717011)
      ·
        refine ⟨105169747140060718316575517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70113164760040478877717011 105169747140060718316575517)
        ·
          refine ⟨39438655177522769368715819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105169747140060718316575517 39438655177522769368715819)
          ·
            refine ⟨59157982766284154053073729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39438655177522769368715819 59157982766284154053073729)
            ·
              refine ⟨44368487074713115539805297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59157982766284154053073729 44368487074713115539805297)
              ·
                refine ⟨33276365306034836654853973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44368487074713115539805297 33276365306034836654853973)
                ·
                  refine ⟨194978702965047871024535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33276365306034836654853973 194978702965047871024535)
                  ·
                    rfl

theorem cell23_3417477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 9].length) (baseStart_3417477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417477 prefixEnd_3417477 := by exact prefixLift 3417477
  have htrace : WordTrace (prefixWord ++ tailWord_3417477) baseStart_3417477 baseEnd_3417477 := by
    simpa [prefixWord, tailWord_3417477, baseEnd_3417477] using wordTrace_append hprefix tailTrace_3417477
  have hstable : (prefixWord ++ tailWord_3417477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417477).length < 2 ^ (prefixWord ++ tailWord_3417477).sum := by decide
  have hdescent : baseEnd_3417477 < baseStart_3417477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417504 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 3]
def baseStart_3417504 : Nat := 118140960795 + 3417504 * 2 ^ 59
def prefixEnd_3417504 : Nat := 4983230072969 + 3 ^ 40 * 3417504 * 2
def baseEnd_3417504 : Nat := 1754822190663102233583191

theorem tailTrace_3417504 : CollatzResearch.WordTrace tailWord_3417504 prefixEnd_3417504 1754822190663102233583191 := by
  unfold tailWord_3417504
  simp only [CollatzResearch.WordTrace]
  refine ⟨62323305505487073030253783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83097740673982764040338377 62323305505487073030253783)
  ·
    refine ⟨93484958258230609545380675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62323305505487073030253783 93484958258230609545380675)
    ·
      refine ⟨140227437387345914318071013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93484958258230609545380675 140227437387345914318071013)
      ·
        refine ⟨26292644510127358934638315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140227437387345914318071013 26292644510127358934638315)
        ·
          refine ⟨39438966765191038401957473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26292644510127358934638315 39438966765191038401957473)
          ·
            refine ⟨29579225073893278801468105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39438966765191038401957473 29579225073893278801468105)
            ·
              refine ⟨22184418805419959101101079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29579225073893278801468105 22184418805419959101101079)
              ·
                refine ⟨33276628208129938651651619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22184418805419959101101079 33276628208129938651651619)
                ·
                  refine ⟨49914942312194907977477429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33276628208129938651651619 49914942312194907977477429)
                  ·
                    refine ⟨4679525841768272622888509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49914942312194907977477429 4679525841768272622888509)
                    ·
                      refine ⟨1754822190663102233583191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4679525841768272622888509 1754822190663102233583191)
                      ·
                        rfl

theorem cell23_3417504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_3417504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417504 prefixEnd_3417504 := by exact prefixLift 3417504
  have htrace : WordTrace (prefixWord ++ tailWord_3417504) baseStart_3417504 baseEnd_3417504 := by
    simpa [prefixWord, tailWord_3417504, baseEnd_3417504] using wordTrace_append hprefix tailTrace_3417504
  have hstable : (prefixWord ++ tailWord_3417504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417504).length < 2 ^ (prefixWord ++ tailWord_3417504).sum := by decide
  have hdescent : baseEnd_3417504 < baseStart_3417504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417561 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 1, 6, 2]
def baseStart_3417561 : Nat := 118140960795 + 3417561 * 2 ^ 59
def prefixEnd_3417561 : Nat := 4983230072969 + 3 ^ 40 * 3417561 * 2
def baseEnd_3417561 : Nat := 1754851459060408510570429

theorem tailTrace_3417561 : CollatzResearch.WordTrace tailWord_3417561 prefixEnd_3417561 1754851459060408510570429 := by
  unfold tailWord_3417561
  simp only [CollatzResearch.WordTrace]
  refine ⟨124648689971767644795332537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83099126647845096530221691 124648689971767644795332537)
  ·
    refine ⟨93486517478825733596499403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124648689971767644795332537 93486517478825733596499403)
    ·
      refine ⟨140229776218238600394749105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93486517478825733596499403 140229776218238600394749105)
      ·
        refine ⟨105172332163678950296061829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140229776218238600394749105 105172332163678950296061829)
        ·
          refine ⟨19719812280689803180511593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105172332163678950296061829 19719812280689803180511593)
          ·
            refine ⟨14789859210517352385383695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19719812280689803180511593 14789859210517352385383695)
            ·
              refine ⟨22184788815776028578075543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14789859210517352385383695 22184788815776028578075543)
              ·
                refine ⟨33277183223664042867113315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22184788815776028578075543 33277183223664042867113315)
                ·
                  refine ⟨49915774835496064300669973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33277183223664042867113315 49915774835496064300669973)
                  ·
                    refine ⟨2339801945413878014093905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49915774835496064300669973 2339801945413878014093905)
                    ·
                      refine ⟨1754851459060408510570429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2339801945413878014093905 1754851459060408510570429)
                      ·
                        rfl

theorem cell23_3417561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 6, 2].length) (baseStart_3417561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417561 prefixEnd_3417561 := by exact prefixLift 3417561
  have htrace : WordTrace (prefixWord ++ tailWord_3417561) baseStart_3417561 baseEnd_3417561 := by
    simpa [prefixWord, tailWord_3417561, baseEnd_3417561] using wordTrace_append hprefix tailTrace_3417561
  have hstable : (prefixWord ++ tailWord_3417561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417561).length < 2 ^ (prefixWord ++ tailWord_3417561).sum := by decide
  have hdescent : baseEnd_3417561 < baseStart_3417561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417571 : List Nat := [1, 1, 1, 6, 2, 1, 1, 1, 5, 4]
def baseStart_3417571 : Nat := 118140960795 + 3417571 * 2 ^ 59
def prefixEnd_3417571 : Nat := 4983230072969 + 3 ^ 40 * 3417571 * 2
def baseEnd_3417571 : Nat := 584952197955651157148461

theorem tailTrace_3417571 : CollatzResearch.WordTrace tailWord_3417571 prefixEnd_3417571 584952197955651157148461 := by
  unfold tailWord_3417571
  simp only [CollatzResearch.WordTrace]
  refine ⟨124649054701731416503196567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83099369801154277668797711 124649054701731416503196567)
  ·
    refine ⟨186973582052597124754794851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124649054701731416503196567 186973582052597124754794851)
    ·
      refine ⟨280460373078895687132192277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186973582052597124754794851 280460373078895687132192277)
      ·
        refine ⟨13146579988073235334321513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 280460373078895687132192277 13146579988073235334321513)
        ·
          refine ⟨9859934991054926500741135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13146579988073235334321513 9859934991054926500741135)
          ·
            refine ⟨14789902486582389751111703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9859934991054926500741135 14789902486582389751111703)
            ·
              refine ⟨22184853729873584626667555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14789902486582389751111703 22184853729873584626667555)
              ·
                refine ⟨33277280594810376940001333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22184853729873584626667555 33277280594810376940001333)
                ·
                  refine ⟨3119745055763472838125125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33277280594810376940001333 3119745055763472838125125)
                  ·
                    refine ⟨584952197955651157148461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3119745055763472838125125 584952197955651157148461)
                    ·
                      rfl

theorem cell23_3417571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 4].length) (baseStart_3417571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417571 prefixEnd_3417571 := by exact prefixLift 3417571
  have htrace : WordTrace (prefixWord ++ tailWord_3417571) baseStart_3417571 baseEnd_3417571 := by
    simpa [prefixWord, tailWord_3417571, baseEnd_3417571] using wordTrace_append hprefix tailTrace_3417571
  have hstable : (prefixWord ++ tailWord_3417571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417571).length < 2 ^ (prefixWord ++ tailWord_3417571).sum := by decide
  have hdescent : baseEnd_3417571 < baseStart_3417571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417601 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 8]
def baseStart_3417601 : Nat := 118140960795 + 3417601 * 2 ^ 59
def prefixEnd_3417601 : Nat := 4983230072969 + 3 ^ 40 * 3417601 * 2
def baseEnd_3417601 : Nat := 194985777587398706007805

theorem tailTrace_3417601 : CollatzResearch.WordTrace tailWord_3417601 prefixEnd_3417601 194985777587398706007805 := by
  unfold tailWord_3417601
  simp only [CollatzResearch.WordTrace]
  refine ⟨124650148891622731626788657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83100099261081821084525771 124650148891622731626788657)
  ·
    refine ⟨93487611668717048720091493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124650148891622731626788657 93487611668717048720091493)
    ·
      refine ⟨17528927187884446635017155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93487611668717048720091493 17528927187884446635017155)
      ·
        refine ⟨26293390781826669952525733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17528927187884446635017155 26293390781826669952525733)
        ·
          refine ⟨4930010771592500616098575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26293390781826669952525733 4930010771592500616098575)
          ·
            refine ⟨7395016157388750924147863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930010771592500616098575 7395016157388750924147863)
            ·
              refine ⟨11092524236083126386221795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395016157388750924147863 11092524236083126386221795)
              ·
                refine ⟨16638786354124689579332693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11092524236083126386221795 16638786354124689579332693)
                ·
                  refine ⟨194985777587398706007805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16638786354124689579332693 194985777587398706007805)
                  ·
                    rfl

theorem cell23_3417601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 8].length) (baseStart_3417601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417601 prefixEnd_3417601 := by exact prefixLift 3417601
  have htrace : WordTrace (prefixWord ++ tailWord_3417601) baseStart_3417601 baseEnd_3417601 := by
    simpa [prefixWord, tailWord_3417601, baseEnd_3417601] using wordTrace_append hprefix tailTrace_3417601
  have hstable : (prefixWord ++ tailWord_3417601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417601).length < 2 ^ (prefixWord ++ tailWord_3417601).sum := by decide
  have hdescent : baseEnd_3417601 < baseStart_3417601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417628 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_3417628 : Nat := 118140960795 + 3417628 * 2 ^ 59
def prefixEnd_3417628 : Nat := 4983230072969 + 3 ^ 40 * 3417628 * 2
def baseEnd_3417628 : Nat := 1754885862264259748432621

theorem tailTrace_3417628 : CollatzResearch.WordTrace tailWord_3417628 prefixEnd_3417628 1754885862264259748432621 := by
  unfold tailWord_3417628
  simp only [CollatzResearch.WordTrace]
  refine ⟨62325566831262457619010769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83100755775016610158681025 62325566831262457619010769)
  ·
    refine ⟨46744175123446843214258077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62325566831262457619010769 46744175123446843214258077)
    ·
      refine ⟨17529065671292566205346779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46744175123446843214258077 17529065671292566205346779)
      ·
        refine ⟨26293598506938849308020169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17529065671292566205346779 26293598506938849308020169)
        ·
          refine ⟨19720198880204136981015127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26293598506938849308020169 19720198880204136981015127)
          ·
            refine ⟨29580298320306205471522691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19720198880204136981015127 29580298320306205471522691)
            ·
              refine ⟨44370447480459308207284037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29580298320306205471522691 44370447480459308207284037)
              ·
                refine ⟨8319458902586120288865757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44370447480459308207284037 8319458902586120288865757)
                ·
                  refine ⟨3119797088469795108324659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8319458902586120288865757 3119797088469795108324659)
                  ·
                    refine ⟨4679695632704692662486989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3119797088469795108324659 4679695632704692662486989)
                    ·
                      refine ⟨1754885862264259748432621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4679695632704692662486989 1754885862264259748432621)
                      ·
                        rfl

theorem cell23_3417628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_3417628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417628 prefixEnd_3417628 := by exact prefixLift 3417628
  have htrace : WordTrace (prefixWord ++ tailWord_3417628) baseStart_3417628 baseEnd_3417628 := by
    simpa [prefixWord, tailWord_3417628, baseEnd_3417628] using wordTrace_append hprefix tailTrace_3417628
  have hstable : (prefixWord ++ tailWord_3417628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417628).length < 2 ^ (prefixWord ++ tailWord_3417628).sum := by decide
  have hdescent : baseEnd_3417628 < baseStart_3417628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417631 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 1, 5]
def baseStart_3417631 : Nat := 118140960795 + 3417631 * 2 ^ 59
def prefixEnd_3417631 : Nat := 4983230072969 + 3 ^ 40 * 3417631 * 2
def baseEnd_3417631 : Nat := 584962467568741078898369

theorem tailTrace_3417631 : CollatzResearch.WordTrace tailWord_3417631 prefixEnd_3417631 584962467568741078898369 := by
  unfold tailWord_3417631
  simp only [CollatzResearch.WordTrace]
  refine ⟨124651243081514046750380747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83100828721009364500253831 124651243081514046750380747)
  ·
    refine ⟨186976864622271070125571121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124651243081514046750380747 186976864622271070125571121)
    ·
      refine ⟨140232648466703302594178341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186976864622271070125571121 140232648466703302594178341)
      ·
        refine ⟨26293621587506869236408439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140232648466703302594178341 26293621587506869236408439)
        ·
          refine ⟨39440432381260303854612659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26293621587506869236408439 39440432381260303854612659)
          ·
            refine ⟨59160648571890455781918989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39440432381260303854612659 59160648571890455781918989)
            ·
              refine ⟨22185243214458920918219621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59160648571890455781918989 22185243214458920918219621)
              ·
                refine ⟨4159733102711047672166179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22185243214458920918219621 4159733102711047672166179)
                ·
                  refine ⟨6239599654066571508249269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159733102711047672166179 6239599654066571508249269)
                  ·
                    refine ⟨584962467568741078898369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6239599654066571508249269 584962467568741078898369)
                    ·
                      rfl

theorem cell23_3417631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 5].length) (baseStart_3417631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417631 prefixEnd_3417631 := by exact prefixLift 3417631
  have htrace : WordTrace (prefixWord ++ tailWord_3417631) baseStart_3417631 baseEnd_3417631 := by
    simpa [prefixWord, tailWord_3417631, baseEnd_3417631] using wordTrace_append hprefix tailTrace_3417631
  have hstable : (prefixWord ++ tailWord_3417631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417631).length < 2 ^ (prefixWord ++ tailWord_3417631).sum := by decide
  have hdescent : baseEnd_3417631 < baseStart_3417631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417681 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_3417681 : Nat := 118140960795 + 3417681 * 2 ^ 59
def prefixEnd_3417681 : Nat := 4983230072969 + 3 ^ 40 * 3417681 * 2
def baseEnd_3417681 : Nat := 1754913076738948041069877

theorem tailTrace_3417681 : CollatzResearch.WordTrace tailWord_3417681 prefixEnd_3417681 1754913076738948041069877 := by
  unfold tailWord_3417681
  simp only [CollatzResearch.WordTrace]
  refine ⟨124653066731332905289700897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83102044487555270193133931 124653066731332905289700897)
  ·
    refine ⟨93489800048499678967275673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124653066731332905289700897 93489800048499678967275673)
    ·
      refine ⟨70117350036374759225456755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93489800048499678967275673 70117350036374759225456755)
      ·
        refine ⟨105176025054562138838185133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70117350036374759225456755 105176025054562138838185133)
        ·
          refine ⟨39441009395460802064319425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105176025054562138838185133 39441009395460802064319425)
          ·
            refine ⟨29580757046595601548239569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39441009395460802064319425 29580757046595601548239569)
            ·
              refine ⟨22185567784946701161179677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29580757046595601548239569 22185567784946701161179677)
              ·
                refine ⟨8319587919355012935442379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22185567784946701161179677 8319587919355012935442379)
                ·
                  refine ⟨12479381879032519403163569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8319587919355012935442379 12479381879032519403163569)
                  ·
                    refine ⟨9359536409274389552372677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12479381879032519403163569 9359536409274389552372677)
                    ·
                      refine ⟨1754913076738948041069877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9359536409274389552372677 1754913076738948041069877)
                      ·
                        rfl

theorem cell23_3417681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_3417681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417681 prefixEnd_3417681 := by exact prefixLift 3417681
  have htrace : WordTrace (prefixWord ++ tailWord_3417681) baseStart_3417681 baseEnd_3417681 := by
    simpa [prefixWord, tailWord_3417681, baseEnd_3417681] using wordTrace_append hprefix tailTrace_3417681
  have hstable : (prefixWord ++ tailWord_3417681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417681).length < 2 ^ (prefixWord ++ tailWord_3417681).sum := by decide
  have hdescent : baseEnd_3417681 < baseStart_3417681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417728 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 5, 3, 2]
def baseStart_3417728 : Nat := 118140960795 + 3417728 * 2 ^ 59
def prefixEnd_3417728 : Nat := 4983230072969 + 3 ^ 40 * 3417728 * 2
def baseEnd_3417728 : Nat := 1754937210329709357182161

theorem tailTrace_3417728 : CollatzResearch.WordTrace tailWord_3417728 prefixEnd_3417728 1754937210329709357182161 := by
  unfold tailWord_3417728
  simp only [CollatzResearch.WordTrace]
  refine ⟨62327390481081316158330919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83103187308108421544441225 62327390481081316158330919)
  ·
    refine ⟨93491085721621974237496379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62327390481081316158330919 93491085721621974237496379)
    ·
      refine ⟨140236628582432961356244569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93491085721621974237496379 140236628582432961356244569)
      ·
        refine ⟨105177471436824721017183427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140236628582432961356244569 105177471436824721017183427)
        ·
          refine ⟨157766207155237081525775141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105177471436824721017183427 157766207155237081525775141)
          ·
            refine ⟨29581163841606952786082839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157766207155237081525775141 29581163841606952786082839)
            ·
              refine ⟨44371745762410429179124259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29581163841606952786082839 44371745762410429179124259)
              ·
                refine ⟨66557618643615643768686389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44371745762410429179124259 66557618643615643768686389)
                ·
                  refine ⟨6239776747838966603314349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66557618643615643768686389 6239776747838966603314349)
                  ·
                    refine ⟨2339916280439612476242881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6239776747838966603314349 2339916280439612476242881)
                    ·
                      refine ⟨1754937210329709357182161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2339916280439612476242881 1754937210329709357182161)
                      ·
                        rfl

theorem cell23_3417728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 3, 2].length) (baseStart_3417728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417728 prefixEnd_3417728 := by exact prefixLift 3417728
  have htrace : WordTrace (prefixWord ++ tailWord_3417728) baseStart_3417728 baseEnd_3417728 := by
    simpa [prefixWord, tailWord_3417728, baseEnd_3417728] using wordTrace_append hprefix tailTrace_3417728
  have hstable : (prefixWord ++ tailWord_3417728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417728).length < 2 ^ (prefixWord ++ tailWord_3417728).sum := by decide
  have hdescent : baseEnd_3417728 < baseStart_3417728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417735 : List Nat := [1, 1, 4, 2, 1, 3, 2, 3, 2, 1, 3]
def baseStart_3417735 : Nat := 118140960795 + 3417735 * 2 ^ 59
def prefixEnd_3417735 : Nat := 4983230072969 + 3 ^ 40 * 3417735 * 2
def baseEnd_3417735 : Nat := 1754940804694290829794629

theorem tailTrace_3417735 : CollatzResearch.WordTrace tailWord_3417735 prefixEnd_3417735 1754940804694290829794629 := by
  unfold tailWord_3417735
  simp only [CollatzResearch.WordTrace]
  refine ⟨124655036273137272512166659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83103357515424848341444439 124655036273137272512166659)
  ·
    refine ⟨186982554409705908768249989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124655036273137272512166659 186982554409705908768249989)
    ·
      refine ⟨35059228951819857894046873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186982554409705908768249989 35059228951819857894046873)
      ·
        refine ⟨26294421713864893420535155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35059228951819857894046873 26294421713864893420535155)
        ·
          refine ⟨39441632570797340130802733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26294421713864893420535155 39441632570797340130802733)
          ·
            refine ⟨14790612214049002549051025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39441632570797340130802733 14790612214049002549051025)
            ·
              refine ⟨11092959160536751911788269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14790612214049002549051025 11092959160536751911788269)
              ·
                refine ⟨4159859685201281966920601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11092959160536751911788269 4159859685201281966920601)
                ·
                  refine ⟨3119894763900961475190451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4159859685201281966920601 3119894763900961475190451)
                  ·
                    refine ⟨4679842145851442212785677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3119894763900961475190451 4679842145851442212785677)
                    ·
                      refine ⟨1754940804694290829794629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4679842145851442212785677 1754940804694290829794629)
                      ·
                        rfl

theorem cell23_3417735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_3417735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417735 prefixEnd_3417735 := by exact prefixLift 3417735
  have htrace : WordTrace (prefixWord ++ tailWord_3417735) baseStart_3417735 baseEnd_3417735 := by
    simpa [prefixWord, tailWord_3417735, baseEnd_3417735] using wordTrace_append hprefix tailTrace_3417735
  have hstable : (prefixWord ++ tailWord_3417735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417735).length < 2 ^ (prefixWord ++ tailWord_3417735).sum := by decide
  have hdescent : baseEnd_3417735 < baseStart_3417735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417775 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 4, 2, 2]
def baseStart_3417775 : Nat := 118140960795 + 3417775 * 2 ^ 59
def prefixEnd_3417775 : Nat := 4983230072969 + 3 ^ 40 * 3417775 * 2
def baseEnd_3417775 : Nat := 1754961343920470673294445

theorem tailTrace_3417775 : CollatzResearch.WordTrace tailWord_3417775 prefixEnd_3417775 1754961343920470673294445 := by
  unfold tailWord_3417775
  simp only [CollatzResearch.WordTrace]
  refine ⟨124656495192992359343622779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83104330128661572895748519 124656495192992359343622779)
  ·
    refine ⟨186984742789488539015434169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124656495192992359343622779 186984742789488539015434169)
    ·
      refine ⟨140238557092116404261575627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186984742789488539015434169 140238557092116404261575627)
      ·
        refine ⟨210357835638174606392363441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140238557092116404261575627 210357835638174606392363441)
        ·
          refine ⟨157768376728630954794272581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210357835638174606392363441 157768376728630954794272581)
          ·
            refine ⟨29581570636618304023926109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157768376728630954794272581 29581570636618304023926109)
            ·
              refine ⟨11093088988731864008972291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29581570636618304023926109 11093088988731864008972291)
              ·
                refine ⟨16639633483097796013458437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11093088988731864008972291 16639633483097796013458437)
                ·
                  refine ⟨3119931278080836752523457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16639633483097796013458437 3119931278080836752523457)
                  ·
                    refine ⟨2339948458560627564392593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3119931278080836752523457 2339948458560627564392593)
                    ·
                      refine ⟨1754961343920470673294445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2339948458560627564392593 1754961343920470673294445)
                      ·
                        rfl

theorem cell23_3417775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 2, 2].length) (baseStart_3417775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417775 prefixEnd_3417775 := by exact prefixLift 3417775
  have htrace : WordTrace (prefixWord ++ tailWord_3417775) baseStart_3417775 baseEnd_3417775 := by
    simpa [prefixWord, tailWord_3417775, baseEnd_3417775] using wordTrace_append hprefix tailTrace_3417775
  have hstable : (prefixWord ++ tailWord_3417775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417775).length < 2 ^ (prefixWord ++ tailWord_3417775).sum := by decide
  have hdescent : baseEnd_3417775 < baseStart_3417775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417788 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3417788 : Nat := 118140960795 + 3417788 * 2 ^ 59
def prefixEnd_3417788 : Nat := 4983230072969 + 3 ^ 40 * 3417788 * 2
def baseEnd_3417788 : Nat := 1754968019168979122431885

theorem tailTrace_3417788 : CollatzResearch.WordTrace tailWord_3417788 prefixEnd_3417788 1754968019168979122431885 := by
  unfold tailWord_3417788
  simp only [CollatzResearch.WordTrace]
  refine ⟨62328484670972631281923009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83104646227963508375897345 62328484670972631281923009)
  ·
    refine ⟨46746363503229473461442257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62328484670972631281923009 46746363503229473461442257)
    ·
      refine ⟨35059772627422105096081693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46746363503229473461442257 35059772627422105096081693)
      ·
        refine ⟨13147414735283289411030635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35059772627422105096081693 13147414735283289411030635)
        ·
          refine ⟨19721122102924934116545953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13147414735283289411030635 19721122102924934116545953)
          ·
            refine ⟨14790841577193700587409465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19721122102924934116545953 14790841577193700587409465)
            ·
              refine ⟨11093131182895275440557099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14790841577193700587409465 11093131182895275440557099)
              ·
                refine ⟨16639696774342913160835649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11093131182895275440557099 16639696774342913160835649)
                ·
                  refine ⟨12479772580757184870626737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16639696774342913160835649 12479772580757184870626737)
                  ·
                    refine ⟨9359829435567888652970053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12479772580757184870626737 9359829435567888652970053)
                    ·
                      refine ⟨1754968019168979122431885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9359829435567888652970053 1754968019168979122431885)
                      ·
                        rfl

theorem cell23_3417788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3417788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417788 prefixEnd_3417788 := by exact prefixLift 3417788
  have htrace : WordTrace (prefixWord ++ tailWord_3417788) baseStart_3417788 baseEnd_3417788 := by
    simpa [prefixWord, tailWord_3417788, baseEnd_3417788] using wordTrace_append hprefix tailTrace_3417788
  have hstable : (prefixWord ++ tailWord_3417788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417788).length < 2 ^ (prefixWord ++ tailWord_3417788).sum := by decide
  have hdescent : baseEnd_3417788 < baseStart_3417788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417828 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 2, 5]
def baseStart_3417828 : Nat := 118140960795 + 3417828 * 2 ^ 59
def prefixEnd_3417828 : Nat := 4983230072969 + 3 ^ 40 * 3417828 * 2
def baseEnd_3417828 : Nat := 584996186131719655310567

theorem tailTrace_3417828 : CollatzResearch.WordTrace tailWord_3417828 prefixEnd_3417828 584996186131719655310567 := by
  unfold tailWord_3417828
  simp only [CollatzResearch.WordTrace]
  refine ⟨62329214130900174697651069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83105618841200232930201425 62329214130900174697651069)
  ·
    refine ⟨23373455299087565511619151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62329214130900174697651069 23373455299087565511619151)
    ·
      refine ⟨35060182948631348267428727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23373455299087565511619151 35060182948631348267428727)
      ·
        refine ⟨52590274422947022401143091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35060182948631348267428727 52590274422947022401143091)
        ·
          refine ⟨78885411634420533601714637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52590274422947022401143091 78885411634420533601714637)
          ·
            refine ⟨29582029362907700100642989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78885411634420533601714637 29582029362907700100642989)
            ·
              refine ⟨11093261011090387537741121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29582029362907700100642989 11093261011090387537741121)
              ·
                refine ⟨8319945758317790653305841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11093261011090387537741121 8319945758317790653305841)
                ·
                  refine ⟨6239959318738342989979381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8319945758317790653305841 6239959318738342989979381)
                  ·
                    refine ⟨584996186131719655310567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6239959318738342989979381 584996186131719655310567)
                    ·
                      rfl

theorem cell23_3417828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_3417828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417828 prefixEnd_3417828 := by exact prefixLift 3417828
  have htrace : WordTrace (prefixWord ++ tailWord_3417828) baseStart_3417828 baseEnd_3417828 := by
    simpa [prefixWord, tailWord_3417828, baseEnd_3417828] using wordTrace_append hprefix tailTrace_3417828
  have hstable : (prefixWord ++ tailWord_3417828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417828).length < 2 ^ (prefixWord ++ tailWord_3417828).sum := by decide
  have hdescent : baseEnd_3417828 < baseStart_3417828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417832 : List Nat := [2, 1, 4, 1, 3, 2, 3, 2, 5]
def baseStart_3417832 : Nat := 118140960795 + 3417832 * 2 ^ 59
def prefixEnd_3417832 : Nat := 4983230072969 + 3 ^ 40 * 3417832 * 2
def baseEnd_3417832 : Nat := 194998956924197438920187

theorem tailTrace_3417832 : CollatzResearch.WordTrace tailWord_3417832 prefixEnd_3417832 194998956924197438920187 := by
  unfold tailWord_3417832
  simp only [CollatzResearch.WordTrace]
  refine ⟨62329287076892929039223875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83105716102523905385631833 62329287076892929039223875)
  ·
    refine ⟨93493930615339393558835813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62329287076892929039223875 93493930615339393558835813)
    ·
      refine ⟨17530111990376136292281715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93493930615339393558835813 17530111990376136292281715)
      ·
        refine ⟨26295167985564204438422573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17530111990376136292281715 26295167985564204438422573)
        ·
          refine ⟨9860687994586576664408465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26295167985564204438422573 9860687994586576664408465)
          ·
            refine ⟨7395515995939932498306349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9860687994586576664408465 7395515995939932498306349)
            ·
              refine ⟨2773318498477474686864881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7395515995939932498306349 2773318498477474686864881)
              ·
                refine ⟨2079988873858106015148661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773318498477474686864881 2079988873858106015148661)
                ·
                  refine ⟨194998956924197438920187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2079988873858106015148661 194998956924197438920187)
                  ·
                    rfl

theorem cell23_3417832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 5].length) (baseStart_3417832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417832 prefixEnd_3417832 := by exact prefixLift 3417832
  have htrace : WordTrace (prefixWord ++ tailWord_3417832) baseStart_3417832 baseEnd_3417832 := by
    simpa [prefixWord, tailWord_3417832, baseEnd_3417832] using wordTrace_append hprefix tailTrace_3417832
  have hstable : (prefixWord ++ tailWord_3417832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417832).length < 2 ^ (prefixWord ++ tailWord_3417832).sum := by decide
  have hdescent : baseEnd_3417832 < baseStart_3417832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417838 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_3417838 : Nat := 118140960795 + 3417838 * 2 ^ 59
def prefixEnd_3417838 : Nat := 4983230072969 + 3 ^ 40 * 3417838 * 2
def baseEnd_3417838 : Nat := 1754993693201703926806655

theorem tailTrace_3417838 : CollatzResearch.WordTrace tailWord_3417838 prefixEnd_3417838 1754993693201703926806655 := by
  unfold tailWord_3417838
  simp only [CollatzResearch.WordTrace]
  refine ⟨15582349123970515137895771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83105861994509414068777445 15582349123970515137895771)
  ·
    refine ⟨23373523685955772706843657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15582349123970515137895771 23373523685955772706843657)
    ·
      refine ⟨17530142764466829530132743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23373523685955772706843657 17530142764466829530132743)
      ·
        refine ⟨26295214146700244295199115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17530142764466829530132743 26295214146700244295199115)
        ·
          refine ⟨39442821220050366442798673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26295214146700244295199115 39442821220050366442798673)
          ·
            refine ⟨29582115915037774832099005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39442821220050366442798673 29582115915037774832099005)
            ·
              refine ⟨11093293468139165562037127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29582115915037774832099005 11093293468139165562037127)
              ·
                refine ⟨16639940202208748343055691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11093293468139165562037127 16639940202208748343055691)
                ·
                  refine ⟨24959910303313122514583537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16639940202208748343055691 24959910303313122514583537)
                  ·
                    refine ⟨18719932727484841885937653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24959910303313122514583537 18719932727484841885937653)
                    ·
                      refine ⟨1754993693201703926806655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18719932727484841885937653 1754993693201703926806655)
                      ·
                        rfl

theorem cell23_3417838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_3417838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417838 prefixEnd_3417838 := by exact prefixLift 3417838
  have htrace : WordTrace (prefixWord ++ tailWord_3417838) baseStart_3417838 baseEnd_3417838 := by
    simpa [prefixWord, tailWord_3417838, baseEnd_3417838] using wordTrace_append hprefix tailTrace_3417838
  have hstable : (prefixWord ++ tailWord_3417838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417838).length < 2 ^ (prefixWord ++ tailWord_3417838).sum := by decide
  have hdescent : baseEnd_3417838 < baseStart_3417838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417861 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_3417861 : Nat := 118140960795 + 3417861 * 2 ^ 59
def prefixEnd_3417861 : Nat := 4983230072969 + 3 ^ 40 * 3417861 * 2
def baseEnd_3417861 : Nat := 1755005503256757336819049

theorem tailTrace_3417861 : CollatzResearch.WordTrace tailWord_3417861 prefixEnd_3417861 1755005503256757336819049 := by
  unfold tailWord_3417861
  simp only [CollatzResearch.WordTrace]
  refine ⟨124659631870680796031253437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83106421247120530687502291 124659631870680796031253437)
  ·
    refine ⟨46747361951505298511720039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124659631870680796031253437 46747361951505298511720039)
    ·
      refine ⟨70121042927257947767580059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46747361951505298511720039 70121042927257947767580059)
      ·
        refine ⟨105181564390886921651370089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70121042927257947767580059 105181564390886921651370089)
        ·
          refine ⟨78886173293165191238527567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105181564390886921651370089 78886173293165191238527567)
          ·
            refine ⟨118329259939747786857791351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78886173293165191238527567 118329259939747786857791351)
            ·
              refine ⟨177493889909621680286687027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118329259939747786857791351 177493889909621680286687027)
              ·
                refine ⟨266240834864432520430030541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177493889909621680286687027 266240834864432520430030541)
                ·
                  refine ⟨99840313074162195161261453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266240834864432520430030541 99840313074162195161261453)
                  ·
                    refine ⟨37440117402810823185473045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99840313074162195161261453 37440117402810823185473045)
                    ·
                      refine ⟨1755005503256757336819049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37440117402810823185473045 1755005503256757336819049)
                      ·
                        rfl

theorem cell23_3417861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_3417861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417861 prefixEnd_3417861 := by exact prefixLift 3417861
  have htrace : WordTrace (prefixWord ++ tailWord_3417861) baseStart_3417861 baseEnd_3417861 := by
    simpa [prefixWord, tailWord_3417861, baseEnd_3417861] using wordTrace_append hprefix tailTrace_3417861
  have hstable : (prefixWord ++ tailWord_3417861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417861).length < 2 ^ (prefixWord ++ tailWord_3417861).sum := by decide
  have hdescent : baseEnd_3417861 < baseStart_3417861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417868 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 1, 4, 3]
def baseStart_3417868 : Nat := 118140960795 + 3417868 * 2 ^ 59
def prefixEnd_3417868 : Nat := 4983230072969 + 3 ^ 40 * 3417868 * 2
def baseEnd_3417868 : Nat := 1755009097621338809431517

theorem tailTrace_3417868 : CollatzResearch.WordTrace tailWord_3417868 prefixEnd_3417868 1755009097621338809431517 := by
  unfold tailWord_3417868
  simp only [CollatzResearch.WordTrace]
  refine ⟨62329943590827718113379129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83106591454436957484505505 62329943590827718113379129)
  ·
    refine ⟨46747457693120788585034347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62329943590827718113379129 46747457693120788585034347)
    ·
      refine ⟨70121186539681182877551521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46747457693120788585034347 70121186539681182877551521)
      ·
        refine ⟨52590889904760887158163641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70121186539681182877551521 52590889904760887158163641)
        ·
          refine ⟨39443167428570665368622731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52590889904760887158163641 39443167428570665368622731)
          ·
            refine ⟨59164751142855998052934097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39443167428570665368622731 59164751142855998052934097)
            ·
              refine ⟨44373563357141998539700573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59164751142855998052934097 44373563357141998539700573)
              ·
                refine ⟨16640086258928249452387715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44373563357141998539700573 16640086258928249452387715)
                ·
                  refine ⟨24960129388392374178581573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16640086258928249452387715 24960129388392374178581573)
                  ·
                    refine ⟨4680024260323570158484045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24960129388392374178581573 4680024260323570158484045)
                    ·
                      refine ⟨1755009097621338809431517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4680024260323570158484045 1755009097621338809431517)
                      ·
                        rfl

theorem cell23_3417868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_3417868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417868 prefixEnd_3417868 := by exact prefixLift 3417868
  have htrace : WordTrace (prefixWord ++ tailWord_3417868) baseStart_3417868 baseEnd_3417868 := by
    simpa [prefixWord, tailWord_3417868, baseEnd_3417868] using wordTrace_append hprefix tailTrace_3417868
  have hstable : (prefixWord ++ tailWord_3417868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417868).length < 2 ^ (prefixWord ++ tailWord_3417868).sum := by decide
  have hdescent : baseEnd_3417868 < baseStart_3417868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417871 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 8]
def baseStart_3417871 : Nat := 118140960795 + 3417871 * 2 ^ 59
def prefixEnd_3417871 : Nat := 4983230072969 + 3 ^ 40 * 3417871 * 2
def baseEnd_3417871 : Nat := 195001182007033588632667

theorem tailTrace_3417871 : CollatzResearch.WordTrace tailWord_3417871 prefixEnd_3417871 195001182007033588632667 := by
  unfold tailWord_3417871
  simp only [CollatzResearch.WordTrace]
  refine ⟨124659996600644567739117467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83106664400429711826078311 124659996600644567739117467)
  ·
    refine ⟨186989994900966851608676201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124659996600644567739117467 186989994900966851608676201)
    ·
      refine ⟨140242496175725138706507151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186989994900966851608676201 140242496175725138706507151)
      ·
        refine ⟨210363744263587708059760727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140242496175725138706507151 210363744263587708059760727)
        ·
          refine ⟨315545616395381562089641091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210363744263587708059760727 315545616395381562089641091)
          ·
            refine ⟨473318424593072343134461637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315545616395381562089641091 473318424593072343134461637)
            ·
              refine ⟨88747204611201064337711557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 473318424593072343134461637 88747204611201064337711557)
              ·
                refine ⟨16640100864600199563320917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88747204611201064337711557 16640100864600199563320917)
                ·
                  refine ⟨195001182007033588632667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16640100864600199563320917 195001182007033588632667)
                  ·
                    rfl

theorem cell23_3417871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 8].length) (baseStart_3417871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417871 prefixEnd_3417871 := by exact prefixLift 3417871
  have htrace : WordTrace (prefixWord ++ tailWord_3417871) baseStart_3417871 baseEnd_3417871 := by
    simpa [prefixWord, tailWord_3417871, baseEnd_3417871] using wordTrace_append hprefix tailTrace_3417871
  have hstable : (prefixWord ++ tailWord_3417871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417871).length < 2 ^ (prefixWord ++ tailWord_3417871).sum := by decide
  have hdescent : baseEnd_3417871 < baseStart_3417871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417919 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 2, 2, 3]
def baseStart_3417919 : Nat := 118140960795 + 3417919 * 2 ^ 59
def prefixEnd_3417919 : Nat := 4983230072969 + 3 ^ 40 * 3417919 * 2
def baseEnd_3417919 : Nat := 1755035285134718109893783

theorem tailTrace_3417919 : CollatzResearch.WordTrace tailWord_3417919 prefixEnd_3417919 1755035285134718109893783 := by
  unfold tailWord_3417919
  simp only [CollatzResearch.WordTrace]
  refine ⟨124661747304470671936864811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83107831536313781291243207 124661747304470671936864811)
  ·
    refine ⟨186992620956706007905297217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124661747304470671936864811 186992620956706007905297217)
    ·
      refine ⟨140244465717529505928972913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186992620956706007905297217 140244465717529505928972913)
      ·
        refine ⟨105183349288147129446729685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140244465717529505928972913 105183349288147129446729685)
        ·
          refine ⟨2465234748940948346407727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 105183349288147129446729685 2465234748940948346407727)
          ·
            refine ⟨3697852123411422519611591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465234748940948346407727 3697852123411422519611591)
            ·
              refine ⟨5546778185117133779417387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3697852123411422519611591 5546778185117133779417387)
              ·
                refine ⟨8320167277675700669126081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5546778185117133779417387 8320167277675700669126081)
                ·
                  refine ⟨6240125458256775501844561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8320167277675700669126081 6240125458256775501844561)
                  ·
                    refine ⟨4680094093692581626383421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6240125458256775501844561 4680094093692581626383421)
                    ·
                      refine ⟨1755035285134718109893783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4680094093692581626383421 1755035285134718109893783)
                      ·
                        rfl

theorem cell23_3417919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 2, 2, 3].length) (baseStart_3417919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417919 prefixEnd_3417919 := by exact prefixLift 3417919
  have htrace : WordTrace (prefixWord ++ tailWord_3417919) baseStart_3417919 baseEnd_3417919 := by
    simpa [prefixWord, tailWord_3417919, baseEnd_3417919] using wordTrace_append hprefix tailTrace_3417919
  have hstable : (prefixWord ++ tailWord_3417919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417919).length < 2 ^ (prefixWord ++ tailWord_3417919).sum := by decide
  have hdescent : baseEnd_3417919 < baseStart_3417919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417925 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 1, 5, 2]
def baseStart_3417925 : Nat := 118140960795 + 3417925 * 2 ^ 59
def prefixEnd_3417925 : Nat := 4983230072969 + 3 ^ 40 * 3417925 * 2
def baseEnd_3417925 : Nat := 1755038366018645086418755

theorem tailTrace_3417925 : CollatzResearch.WordTrace tailWord_3417925 prefixEnd_3417925 1755038366018645086418755 := by
  unfold tailWord_3417925
  simp only [CollatzResearch.WordTrace]
  refine ⟨124661966142448934961583229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83107977428299289974388819 124661966142448934961583229)
  ·
    refine ⟨46748237303418350610593711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124661966142448934961583229 46748237303418350610593711)
    ·
      refine ⟨70122355955127525915890567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46748237303418350610593711 70122355955127525915890567)
      ·
        refine ⟨105183533932691288873835851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70122355955127525915890567 105183533932691288873835851)
        ·
          refine ⟨157775300899036933310753777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105183533932691288873835851 157775300899036933310753777)
          ·
            refine ⟨118331475674277699983065333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157775300899036933310753777 118331475674277699983065333)
            ·
              refine ⟨11093575844463534373412375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118331475674277699983065333 11093575844463534373412375)
              ·
                refine ⟨16640363766695301560118563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11093575844463534373412375 16640363766695301560118563)
                ·
                  refine ⟨24960545650042952340177845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16640363766695301560118563 24960545650042952340177845)
                  ·
                    refine ⟨2340051154691526781891673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24960545650042952340177845 2340051154691526781891673)
                    ·
                      refine ⟨1755038366018645086418755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2340051154691526781891673 1755038366018645086418755)
                      ·
                        rfl

theorem cell23_3417925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 5, 2].length) (baseStart_3417925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417925 prefixEnd_3417925 := by exact prefixLift 3417925
  have htrace : WordTrace (prefixWord ++ tailWord_3417925) baseStart_3417925 baseEnd_3417925 := by
    simpa [prefixWord, tailWord_3417925, baseEnd_3417925] using wordTrace_append hprefix tailTrace_3417925
  have hstable : (prefixWord ++ tailWord_3417925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417925).length < 2 ^ (prefixWord ++ tailWord_3417925).sum := by decide
  have hdescent : baseEnd_3417925 < baseStart_3417925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417926 : List Nat := [6, 1, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_3417926 : Nat := 118140960795 + 3417926 * 2 ^ 59
def prefixEnd_3417926 : Nat := 4983230072969 + 3 ^ 40 * 3417926 * 2
def baseEnd_3417926 : Nat := 585012959833099860835417

theorem tailTrace_3417926 : CollatzResearch.WordTrace tailWord_3417926 prefixEnd_3417926 585012959833099860835417 := by
  unfold tailWord_3417926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3895687581732666004136551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 83108001743630208088246421 3895687581732666004136551)
  ·
    refine ⟨5843531372598999006204827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3895687581732666004136551 5843531372598999006204827)
    ·
      refine ⟨8765297058898498509307241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5843531372598999006204827 8765297058898498509307241)
      ·
        refine ⟨6573972794173873881980431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8765297058898498509307241 6573972794173873881980431)
        ·
          refine ⟨9860959191260810822970647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6573972794173873881980431 9860959191260810822970647)
          ·
            refine ⟨14791438786891216234455971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9860959191260810822970647 14791438786891216234455971)
            ·
              refine ⟨22187158180336824351683957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14791438786891216234455971 22187158180336824351683957)
              ·
                refine ⟨2080046079406577282970371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22187158180336824351683957 2080046079406577282970371)
                ·
                  refine ⟨3120069119109865924455557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080046079406577282970371 3120069119109865924455557)
                  ·
                    refine ⟨585012959833099860835417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3120069119109865924455557 585012959833099860835417)
                    ·
                      rfl

theorem cell23_3417926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_3417926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417926 prefixEnd_3417926 := by exact prefixLift 3417926
  have htrace : WordTrace (prefixWord ++ tailWord_3417926) baseStart_3417926 baseEnd_3417926 := by
    simpa [prefixWord, tailWord_3417926, baseEnd_3417926] using wordTrace_append hprefix tailTrace_3417926
  have hstable : (prefixWord ++ tailWord_3417926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417926).length < 2 ^ (prefixWord ++ tailWord_3417926).sum := by decide
  have hdescent : baseEnd_3417926 < baseStart_3417926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417965 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 1, 6]
def baseStart_3417965 : Nat := 118140960795 + 3417965 * 2 ^ 59
def prefixEnd_3417965 : Nat := 4983230072969 + 3 ^ 40 * 3417965 * 2
def baseEnd_3417965 : Nat := 585019635081608309972857

theorem tailTrace_3417965 : CollatzResearch.WordTrace tailWord_3417965 prefixEnd_3417965 585019635081608309972857 := by
  unfold tailWord_3417965
  simp only [CollatzResearch.WordTrace]
  refine ⟨124663425062304021793039349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83108950041536014528692899 124663425062304021793039349)
  ·
    refine ⟨11687196099591002043097439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124663425062304021793039349 11687196099591002043097439)
    ·
      refine ⟨17530794149386503064646159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11687196099591002043097439 17530794149386503064646159)
      ·
        refine ⟨26296191224079754596969239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17530794149386503064646159 26296191224079754596969239)
        ·
          refine ⟨39444286836119631895453859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26296191224079754596969239 39444286836119631895453859)
          ·
            refine ⟨59166430254179447843180789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39444286836119631895453859 59166430254179447843180789)
            ·
              refine ⟨5546852836329323235298199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59166430254179447843180789 5546852836329323235298199)
              ·
                refine ⟨8320279254493984852947299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5546852836329323235298199 8320279254493984852947299)
                ·
                  refine ⟨12480418881740977279420949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8320279254493984852947299 12480418881740977279420949)
                  ·
                    refine ⟨585019635081608309972857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12480418881740977279420949 585019635081608309972857)
                    ·
                      rfl

theorem cell23_3417965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_3417965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417965 prefixEnd_3417965 := by exact prefixLift 3417965
  have htrace : WordTrace (prefixWord ++ tailWord_3417965) baseStart_3417965 baseEnd_3417965 := by
    simpa [prefixWord, tailWord_3417965, baseEnd_3417965] using wordTrace_append hprefix tailTrace_3417965
  have hstable : (prefixWord ++ tailWord_3417965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417965).length < 2 ^ (prefixWord ++ tailWord_3417965).sum := by decide
  have hdescent : baseEnd_3417965 < baseStart_3417965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3417992 : List Nat := [2, 1, 3, 3, 3, 1, 2, 1, 1, 1, 5]
def baseStart_3417992 : Nat := 118140960795 + 3417992 * 2 ^ 59
def prefixEnd_3417992 : Nat := 4983230072969 + 3 ^ 40 * 3417992 * 2
def baseEnd_3417992 : Nat := 1755072769222496324280947

theorem tailTrace_3417992 : CollatzResearch.WordTrace tailWord_3417992 prefixEnd_3417992 1755072769222496324280947 := by
  unfold tailWord_3417992
  simp only [CollatzResearch.WordTrace]
  refine ⟨62332204916603102702136115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83109606555470803602848153 62332204916603102702136115)
  ·
    refine ⟨93498307374904654053204173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62332204916603102702136115 93498307374904654053204173)
    ·
      refine ⟨35061865265589245269951565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93498307374904654053204173 35061865265589245269951565)
      ·
        refine ⟨13148199474595966976231837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35061865265589245269951565 13148199474595966976231837)
        ·
          refine ⟨4930574802973487616086939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13148199474595966976231837 4930574802973487616086939)
          ·
            refine ⟨7395862204460231424130409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930574802973487616086939 7395862204460231424130409)
            ·
              refine ⟨5546896653345173568097807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7395862204460231424130409 5546896653345173568097807)
              ·
                refine ⟨8320344980017760352146711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5546896653345173568097807 8320344980017760352146711)
                ·
                  refine ⟨12480517470026640528220067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8320344980017760352146711 12480517470026640528220067)
                  ·
                    refine ⟨18720776205039960792330101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12480517470026640528220067 18720776205039960792330101)
                    ·
                      refine ⟨1755072769222496324280947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18720776205039960792330101 1755072769222496324280947)
                      ·
                        rfl

theorem cell23_3417992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_3417992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3417992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3417992 prefixEnd_3417992 := by exact prefixLift 3417992
  have htrace : WordTrace (prefixWord ++ tailWord_3417992) baseStart_3417992 baseEnd_3417992 := by
    simpa [prefixWord, tailWord_3417992, baseEnd_3417992] using wordTrace_append hprefix tailTrace_3417992
  have hstable : (prefixWord ++ tailWord_3417992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3417992).length < 2 ^ (prefixWord ++ tailWord_3417992).sum := by decide
  have hdescent : baseEnd_3417992 < baseStart_3417992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3417992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418062 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2]
def baseStart_3418062 : Nat := 118140960795 + 3418062 * 2 ^ 59
def prefixEnd_3418062 : Nat := 4983230072969 + 3 ^ 40 * 3418062 * 2
def baseEnd_3418062 : Nat := 1755108712868311050405625

theorem tailTrace_3418062 : CollatzResearch.WordTrace tailWord_3418062 prefixEnd_3418062 1755108712868311050405625 := by
  unfold tailWord_3418062
  simp only [CollatzResearch.WordTrace]
  refine ⟨15583370367869075919915055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83111308628635071572880293 15583370367869075919915055)
  ·
    refine ⟨23375055551803613879872583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15583370367869075919915055 23375055551803613879872583)
    ·
      refine ⟨35062583327705420819808875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23375055551803613879872583 35062583327705420819808875)
      ·
        refine ⟨52593874991558131229713313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35062583327705420819808875 52593874991558131229713313)
        ·
          refine ⟨39445406243668598422284985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52593874991558131229713313 39445406243668598422284985)
          ·
            refine ⟨29584054682751448816713739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39445406243668598422284985 29584054682751448816713739)
            ·
              refine ⟨44376082024127173225070609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29584054682751448816713739 44376082024127173225070609)
              ·
                refine ⟨33282061518095379918802957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44376082024127173225070609 33282061518095379918802957)
                ·
                  refine ⟨12480773069285767469551109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33282061518095379918802957 12480773069285767469551109)
                  ·
                    refine ⟨2340144950491081400540833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12480773069285767469551109 2340144950491081400540833)
                    ·
                      refine ⟨1755108712868311050405625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2340144950491081400540833 1755108712868311050405625)
                      ·
                        rfl

theorem cell23_3418062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2].length) (baseStart_3418062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418062 prefixEnd_3418062 := by exact prefixLift 3418062
  have htrace : WordTrace (prefixWord ++ tailWord_3418062) baseStart_3418062 baseEnd_3418062 := by
    simpa [prefixWord, tailWord_3418062, baseEnd_3418062] using wordTrace_append hprefix tailTrace_3418062
  have hstable : (prefixWord ++ tailWord_3418062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418062).length < 2 ^ (prefixWord ++ tailWord_3418062).sum := by decide
  have hdescent : baseEnd_3418062 < baseStart_3418062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418079 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 1, 4, 2]
def baseStart_3418079 : Nat := 118140960795 + 3418079 * 2 ^ 59
def prefixEnd_3418079 : Nat := 4983230072969 + 3 ^ 40 * 3418079 * 2
def baseEnd_3418079 : Nat := 1755117442039437483893047

theorem tailTrace_3418079 : CollatzResearch.WordTrace tailWord_3418079 prefixEnd_3418079 1755117442039437483893047 := by
  unfold tailWord_3418079
  simp only [CollatzResearch.WordTrace]
  refine ⟨124667582983891019262689291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83111721989260679508459527 124667582983891019262689291)
  ·
    refine ⟨187001374475836528894033937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124667582983891019262689291 187001374475836528894033937)
    ·
      refine ⟨140251030856877396670525453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187001374475836528894033937 140251030856877396670525453)
      ·
        refine ⟨52594136571329023751447045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140251030856877396670525453 52594136571329023751447045)
        ·
          refine ⟨9861400607124191953396321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52594136571329023751447045 9861400607124191953396321)
          ·
            refine ⟨7396050455343143965047241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9861400607124191953396321 7396050455343143965047241)
            ·
              refine ⟨5547037841507357973785431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7396050455343143965047241 5547037841507357973785431)
              ·
                refine ⟨8320556762261036960678147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547037841507357973785431 8320556762261036960678147)
                ·
                  refine ⟨12480835143391555441017221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8320556762261036960678147 12480835143391555441017221)
                  ·
                    refine ⟨2340156589385916645190729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12480835143391555441017221 2340156589385916645190729)
                    ·
                      refine ⟨1755117442039437483893047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2340156589385916645190729 1755117442039437483893047)
                      ·
                        rfl

theorem cell23_3418079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_3418079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418079 prefixEnd_3418079 := by exact prefixLift 3418079
  have htrace : WordTrace (prefixWord ++ tailWord_3418079) baseStart_3418079 baseEnd_3418079 := by
    simpa [prefixWord, tailWord_3418079, baseEnd_3418079] using wordTrace_append hprefix tailTrace_3418079
  have hstable : (prefixWord ++ tailWord_3418079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418079).length < 2 ^ (prefixWord ++ tailWord_3418079).sum := by decide
  have hdescent : baseEnd_3418079 < baseStart_3418079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418095 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 3]
def baseStart_3418095 : Nat := 118140960795 + 3418095 * 2 ^ 59
def prefixEnd_3418095 : Nat := 4983230072969 + 3 ^ 40 * 3418095 * 2
def baseEnd_3418095 : Nat := 1755125657729909421292973

theorem tailTrace_3418095 : CollatzResearch.WordTrace tailWord_3418095 prefixEnd_3418095 1755125657729909421292973 := by
  unfold tailWord_3418095
  simp only [CollatzResearch.WordTrace]
  refine ⟨124668166551833053995271739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83112111034555369330181159 124668166551833053995271739)
  ·
    refine ⟨187002249827749580992907609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124668166551833053995271739 187002249827749580992907609)
    ·
      refine ⟨140251687370812185744680707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187002249827749580992907609 140251687370812185744680707)
      ·
        refine ⟨210377531056218278617021061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140251687370812185744680707 210377531056218278617021061)
        ·
          refine ⟨39445787073040927240691449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210377531056218278617021061 39445787073040927240691449)
          ·
            refine ⟨29584340304780695430518587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39445787073040927240691449 29584340304780695430518587)
            ·
              refine ⟨44376510457171043145777881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29584340304780695430518587 44376510457171043145777881)
              ·
                refine ⟨33282382842878282359333411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44376510457171043145777881 33282382842878282359333411)
                ·
                  refine ⟨49923574264317423539000117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33282382842878282359333411 49923574264317423539000117)
                  ·
                    refine ⟨4680335087279758456781261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49923574264317423539000117 4680335087279758456781261)
                    ·
                      refine ⟨1755125657729909421292973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4680335087279758456781261 1755125657729909421292973)
                      ·
                        rfl

theorem cell23_3418095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 3].length) (baseStart_3418095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418095 prefixEnd_3418095 := by exact prefixLift 3418095
  have htrace : WordTrace (prefixWord ++ tailWord_3418095) baseStart_3418095 baseEnd_3418095 := by
    simpa [prefixWord, tailWord_3418095, baseEnd_3418095] using wordTrace_append hprefix tailTrace_3418095
  have hstable : (prefixWord ++ tailWord_3418095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418095).length < 2 ^ (prefixWord ++ tailWord_3418095).sum := by decide
  have hdescent : baseEnd_3418095 < baseStart_3418095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418115 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 2, 5]
def baseStart_3418115 : Nat := 118140960795 + 3418115 * 2 ^ 59
def prefixEnd_3418115 : Nat := 4983230072969 + 3 ^ 40 * 3418115 * 2
def baseEnd_3418115 : Nat := 585045309114333114347627

theorem tailTrace_3418115 : CollatzResearch.WordTrace tailWord_3418115 prefixEnd_3418115 585045309114333114347627 := by
  unfold tailWord_3418115
  simp only [CollatzResearch.WordTrace]
  refine ⟨124668896011760597410999799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83112597341173731607333199 124668896011760597410999799)
  ·
    refine ⟨187003344017640896116499699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124668896011760597410999799 187003344017640896116499699)
    ·
      refine ⟨280505016026461344174749549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187003344017640896116499699 280505016026461344174749549)
      ·
        refine ⟨105189381009923004065531081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280505016026461344174749549 105189381009923004065531081)
        ·
          refine ⟨78892035757442253049148311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105189381009923004065531081 78892035757442253049148311)
          ·
            refine ⟨118338053636163379573722467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78892035757442253049148311 118338053636163379573722467)
            ·
              refine ⟨177507080454245069360583701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118338053636163379573722467 177507080454245069360583701)
              ·
                refine ⟨8320644396292737626277361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177507080454245069360583701 8320644396292737626277361)
                ·
                  refine ⟨6240483297219553219708021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8320644396292737626277361 6240483297219553219708021)
                  ·
                    refine ⟨585045309114333114347627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6240483297219553219708021 585045309114333114347627)
                    ·
                      rfl

theorem cell23_3418115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 5].length) (baseStart_3418115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418115 prefixEnd_3418115 := by exact prefixLift 3418115
  have htrace : WordTrace (prefixWord ++ tailWord_3418115) baseStart_3418115 baseEnd_3418115 := by
    simpa [prefixWord, tailWord_3418115, baseEnd_3418115] using wordTrace_append hprefix tailTrace_3418115
  have hstable : (prefixWord ++ tailWord_3418115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418115).length < 2 ^ (prefixWord ++ tailWord_3418115).sum := by decide
  have hdescent : baseEnd_3418115 < baseStart_3418115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418165 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3418165 : Nat := 118140960795 + 3418165 * 2 ^ 59
def prefixEnd_3418165 : Nat := 4983230072969 + 3 ^ 40 * 3418165 * 2
def baseEnd_3418165 : Nat := 1755161601375724147417651

theorem tailTrace_3418165 : CollatzResearch.WordTrace tailWord_3418165 prefixEnd_3418165 1755161601375724147417651 := by
  unfold tailWord_3418165
  simp only [CollatzResearch.WordTrace]
  refine ⟨124670719661579455950319949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83113813107719637300213299 124670719661579455950319949)
  ·
    refine ⟨46751519873092295981369981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124670719661579455950319949 46751519873092295981369981)
    ·
      refine ⟨17531819952409610993013743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46751519873092295981369981 17531819952409610993013743)
      ·
        refine ⟨26297729928614416489520615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17531819952409610993013743 26297729928614416489520615)
        ·
          refine ⟨39446594892921624734280923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26297729928614416489520615 39446594892921624734280923)
          ·
            refine ⟨59169892339382437101421385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39446594892921624734280923 59169892339382437101421385)
            ·
              refine ⟨44377419254536827826066039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59169892339382437101421385 44377419254536827826066039)
              ·
                refine ⟨66566128881805241739099059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44377419254536827826066039 66566128881805241739099059)
                ·
                  refine ⟨99849193322707862608648589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66566128881805241739099059 99849193322707862608648589)
                  ·
                    refine ⟨37443447496015448478243221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99849193322707862608648589 37443447496015448478243221)
                    ·
                      refine ⟨1755161601375724147417651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37443447496015448478243221 1755161601375724147417651)
                      ·
                        rfl

theorem cell23_3418165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3418165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418165 prefixEnd_3418165 := by exact prefixLift 3418165
  have htrace : WordTrace (prefixWord ++ tailWord_3418165) baseStart_3418165 baseEnd_3418165 := by
    simpa [prefixWord, tailWord_3418165, baseEnd_3418165] using wordTrace_append hprefix tailTrace_3418165
  have hstable : (prefixWord ++ tailWord_3418165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418165).length < 2 ^ (prefixWord ++ tailWord_3418165).sum := by decide
  have hdescent : baseEnd_3418165 < baseStart_3418165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418169 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3418169 : Nat := 118140960795 + 3418169 * 2 ^ 59
def prefixEnd_3418169 : Nat := 4983230072969 + 3 ^ 40 * 3418169 * 2
def baseEnd_3418169 : Nat := 1755163655298342131767633

theorem tailTrace_3418169 : CollatzResearch.WordTrace tailWord_3418169 prefixEnd_3418169 1755163655298342131767633 := by
  unfold tailWord_3418169
  simp only [CollatzResearch.WordTrace]
  refine ⟨124670865553564964633465561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83113910369043309755643707 124670865553564964633465561)
  ·
    refine ⟨93503149165173723475099171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124670865553564964633465561 93503149165173723475099171)
    ·
      refine ⟨140254723747760585212648757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93503149165173723475099171 140254723747760585212648757)
      ·
        refine ⟨13148880351352554863685821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140254723747760585212648757 13148880351352554863685821)
        ·
          refine ⟨4930830131757208073882183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13148880351352554863685821 4930830131757208073882183)
          ·
            refine ⟨7396245197635812110823275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930830131757208073882183 7396245197635812110823275)
            ·
              refine ⟨11094367796453718166234913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7396245197635812110823275 11094367796453718166234913)
              ·
                refine ⟨8320775847340288624676185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11094367796453718166234913 8320775847340288624676185)
                ·
                  refine ⟨6240581885505216468507139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8320775847340288624676185 6240581885505216468507139)
                  ·
                    refine ⟨9360872828257824702760709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6240581885505216468507139 9360872828257824702760709)
                    ·
                      refine ⟨1755163655298342131767633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9360872828257824702760709 1755163655298342131767633)
                      ·
                        rfl

theorem cell23_3418169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3418169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418169 prefixEnd_3418169 := by exact prefixLift 3418169
  have htrace : WordTrace (prefixWord ++ tailWord_3418169) baseStart_3418169 baseEnd_3418169 := by
    simpa [prefixWord, tailWord_3418169, baseEnd_3418169] using wordTrace_append hprefix tailTrace_3418169
  have hstable : (prefixWord ++ tailWord_3418169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418169).length < 2 ^ (prefixWord ++ tailWord_3418169).sum := by decide
  have hdescent : baseEnd_3418169 < baseStart_3418169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418175 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 8]
def baseStart_3418175 : Nat := 118140960795 + 3418175 * 2 ^ 59
def prefixEnd_3418175 : Nat := 4983230072969 + 3 ^ 40 * 3418175 * 2
def baseEnd_3418175 : Nat := 195018526242474345365845

theorem tailTrace_3418175 : CollatzResearch.WordTrace tailWord_3418175 prefixEnd_3418175 195018526242474345365845 := by
  unfold tailWord_3418175
  simp only [CollatzResearch.WordTrace]
  refine ⟨124671084391543227658183979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83114056261028818438789319 124671084391543227658183979)
  ·
    refine ⟨187006626587314841487275969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124671084391543227658183979 187006626587314841487275969)
    ·
      refine ⟨140254969940486131115456977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 187006626587314841487275969 140254969940486131115456977)
      ·
        refine ⟨105191227455364598336592733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140254969940486131115456977 105191227455364598336592733)
        ·
          refine ⟨39446710295761724376222275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105191227455364598336592733 39446710295761724376222275)
          ·
            refine ⟨59170065443642586564333413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39446710295761724376222275 59170065443642586564333413)
            ·
              refine ⟨11094387270682984980812515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59170065443642586564333413 11094387270682984980812515)
              ·
                refine ⟨16641580906024477471218773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11094387270682984980812515 16641580906024477471218773)
                ·
                  refine ⟨195018526242474345365845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16641580906024477471218773 195018526242474345365845)
                  ·
                    rfl

theorem cell23_3418175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 8].length) (baseStart_3418175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418175 prefixEnd_3418175 := by exact prefixLift 3418175
  have htrace : WordTrace (prefixWord ++ tailWord_3418175) baseStart_3418175 baseEnd_3418175 := by
    simpa [prefixWord, tailWord_3418175, baseEnd_3418175] using wordTrace_append hprefix tailTrace_3418175
  have hstable : (prefixWord ++ tailWord_3418175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418175).length < 2 ^ (prefixWord ++ tailWord_3418175).sum := by decide
  have hdescent : baseEnd_3418175 < baseStart_3418175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418189 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3418189 : Nat := 118140960795 + 3418189 * 2 ^ 59
def prefixEnd_3418189 : Nat := 4983230072969 + 3 ^ 40 * 3418189 * 2
def baseEnd_3418189 : Nat := 1755173924911432053517541

theorem tailTrace_3418189 : CollatzResearch.WordTrace tailWord_3418189 prefixEnd_3418189 1755173924911432053517541 := by
  unfold tailWord_3418189
  simp only [CollatzResearch.WordTrace]
  refine ⟨124671595013492508049193621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83114396675661672032795747 124671595013492508049193621)
  ·
    refine ⟨5843981016257461314805951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124671595013492508049193621 5843981016257461314805951)
    ·
      refine ⟨8765971524386191972208927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5843981016257461314805951 8765971524386191972208927)
      ·
        refine ⟨13148957286579287958313391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8765971524386191972208927 13148957286579287958313391)
        ·
          refine ⟨19723435929868931937470087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13148957286579287958313391 19723435929868931937470087)
          ·
            refine ⟨29585153894803397906205131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19723435929868931937470087 29585153894803397906205131)
            ·
              refine ⟨44377730842205096859307697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29585153894803397906205131 44377730842205096859307697)
              ·
                refine ⟨33283298131653822644480773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44377730842205096859307697 33283298131653822644480773)
                ·
                  refine ⟨6240618399685091745840145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33283298131653822644480773 6240618399685091745840145)
                  ·
                    refine ⟨4680463799763818809380109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6240618399685091745840145 4680463799763818809380109)
                    ·
                      refine ⟨1755173924911432053517541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4680463799763818809380109 1755173924911432053517541)
                      ·
                        rfl

theorem cell23_3418189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3418189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418189 prefixEnd_3418189 := by exact prefixLift 3418189
  have htrace : WordTrace (prefixWord ++ tailWord_3418189) baseStart_3418189 baseEnd_3418189 := by
    simpa [prefixWord, tailWord_3418189, baseEnd_3418189] using wordTrace_append hprefix tailTrace_3418189
  have hstable : (prefixWord ++ tailWord_3418189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418189).length < 2 ^ (prefixWord ++ tailWord_3418189).sum := by decide
  have hdescent : baseEnd_3418189 < baseStart_3418189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418230 : List Nat := [5, 1, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_3418230 : Nat := 118140960795 + 3418230 * 2 ^ 59
def prefixEnd_3418230 : Nat := 4983230072969 + 3 ^ 40 * 3418230 * 2
def baseEnd_3418230 : Nat := 585064992539422131034951

theorem tailTrace_3418230 : CollatzResearch.WordTrace tailWord_3418230 prefixEnd_3418230 585064992539422131034951 := by
  unfold tailWord_3418230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7792068150396498253214759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83115393604229314700957429 7792068150396498253214759)
  ·
    refine ⟨11688102225594747379822139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7792068150396498253214759 11688102225594747379822139)
    ·
      refine ⟨17532153338392121069733209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11688102225594747379822139 17532153338392121069733209)
      ·
        refine ⟨13149115003794090802299907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17532153338392121069733209 13149115003794090802299907)
        ·
          refine ⟨19723672505691136203449861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13149115003794090802299907 19723672505691136203449861)
          ·
            refine ⟨3698188594817088038146849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19723672505691136203449861 3698188594817088038146849)
            ·
              refine ⟨2773641446112816028610137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3698188594817088038146849 2773641446112816028610137)
              ·
                refine ⟨2080231084584612021457603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773641446112816028610137 2080231084584612021457603)
                ·
                  refine ⟨3120346626876918032186405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080231084584612021457603 3120346626876918032186405)
                  ·
                    refine ⟨585064992539422131034951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3120346626876918032186405 585064992539422131034951)
                    ·
                      rfl

theorem cell23_3418230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_3418230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418230 prefixEnd_3418230 := by exact prefixLift 3418230
  have htrace : WordTrace (prefixWord ++ tailWord_3418230) baseStart_3418230 baseEnd_3418230 := by
    simpa [prefixWord, tailWord_3418230, baseEnd_3418230] using wordTrace_append hprefix tailTrace_3418230
  have hstable : (prefixWord ++ tailWord_3418230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418230).length < 2 ^ (prefixWord ++ tailWord_3418230).sum := by decide
  have hdescent : baseEnd_3418230 < baseStart_3418230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418252 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 8, 4]
def baseStart_3418252 : Nat := 118140960795 + 3418252 * 2 ^ 59
def prefixEnd_3418252 : Nat := 4983230072969 + 3 ^ 40 * 3418252 * 2
def baseEnd_3418252 : Nat := 585068758064221769009917

theorem tailTrace_3418252 : CollatzResearch.WordTrace tailWord_3418252 prefixEnd_3418252 585068758064221769009917 := by
  unfold tailWord_3418252
  simp only [CollatzResearch.WordTrace]
  refine ⟨62336946406132134904368505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83115928541509513205824673 62336946406132134904368505)
  ·
    refine ⟨46752709804599101178276379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62336946406132134904368505 46752709804599101178276379)
    ·
      refine ⟨70129064706898651767414569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46752709804599101178276379 70129064706898651767414569)
      ·
        refine ⟨52596798530173988825560927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70129064706898651767414569 52596798530173988825560927)
        ·
          refine ⟨78895197795260983238341391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52596798530173988825560927 78895197795260983238341391)
          ·
            refine ⟨118342796692891474857512087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78895197795260983238341391 118342796692891474857512087)
            ·
              refine ⟨177514195039337212286268131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118342796692891474857512087 177514195039337212286268131)
              ·
                refine ⟨266271292559005818429402197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177514195039337212286268131 266271292559005818429402197)
                ·
                  refine ⟨3120366709675849434719557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 266271292559005818429402197 3120366709675849434719557)
                  ·
                    refine ⟨585068758064221769009917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3120366709675849434719557 585068758064221769009917)
                    ·
                      rfl

theorem cell23_3418252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_3418252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418252 prefixEnd_3418252 := by exact prefixLift 3418252
  have htrace : WordTrace (prefixWord ++ tailWord_3418252) baseStart_3418252 baseEnd_3418252 := by
    simpa [prefixWord, tailWord_3418252, baseEnd_3418252] using wordTrace_append hprefix tailTrace_3418252
  have hstable : (prefixWord ++ tailWord_3418252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418252).length < 2 ^ (prefixWord ++ tailWord_3418252).sum := by decide
  have hdescent : baseEnd_3418252 < baseStart_3418252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418263 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 2, 3, 2]
def baseStart_3418263 : Nat := 118140960795 + 3418263 * 2 ^ 59
def prefixEnd_3418263 : Nat := 4983230072969 + 3 ^ 40 * 3418263 * 2
def baseEnd_3418263 : Nat := 1755211922479864763992201

theorem tailTrace_3418263 : CollatzResearch.WordTrace tailWord_3418263 prefixEnd_3418263 1755211922479864763992201 := by
  unfold tailWord_3418263
  simp only [CollatzResearch.WordTrace]
  refine ⟨124674294015224418687387443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83116196010149612458258295 124674294015224418687387443)
  ·
    refine ⟨187011441022836628031081165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124674294015224418687387443 187011441022836628031081165)
    ·
      refine ⟨70129290383563735511655437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187011441022836628031081165 70129290383563735511655437)
      ·
        refine ⟨26298483893836400816870789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70129290383563735511655437 26298483893836400816870789)
        ·
          refine ⟨4930965730094325153163273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26298483893836400816870789 4930965730094325153163273)
          ·
            refine ⟨3698224297570743864872455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4930965730094325153163273 3698224297570743864872455)
            ·
              refine ⟨5547336446356115797308683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3698224297570743864872455 5547336446356115797308683)
              ·
                refine ⟨8321004669534173695963025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547336446356115797308683 8321004669534173695963025)
                ·
                  refine ⟨6240753502150630271972269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8321004669534173695963025 6240753502150630271972269)
                  ·
                    refine ⟨2340282563306486351989601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6240753502150630271972269 2340282563306486351989601)
                    ·
                      refine ⟨1755211922479864763992201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2340282563306486351989601 1755211922479864763992201)
                      ·
                        rfl

theorem cell23_3418263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_3418263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418263 prefixEnd_3418263 := by exact prefixLift 3418263
  have htrace : WordTrace (prefixWord ++ tailWord_3418263) baseStart_3418263 baseEnd_3418263 := by
    simpa [prefixWord, tailWord_3418263, baseEnd_3418263] using wordTrace_append hprefix tailTrace_3418263
  have hstable : (prefixWord ++ tailWord_3418263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418263).length < 2 ^ (prefixWord ++ tailWord_3418263).sum := by decide
  have hdescent : baseEnd_3418263 < baseStart_3418263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418265 : List Nat := [1, 2, 1, 2, 1, 2, 1, 13]
def baseStart_3418265 : Nat := 118140960795 + 3418265 * 2 ^ 59
def prefixEnd_3418265 : Nat := 4983230072969 + 3 ^ 40 * 3418265 * 2
def baseEnd_3418265 : Nat := 65007887016339768746933

theorem tailTrace_3418265 : CollatzResearch.WordTrace tailWord_3418265 prefixEnd_3418265 65007887016339768746933 := by
  unfold tailWord_3418265
  simp only [CollatzResearch.WordTrace]
  refine ⟨124674366961217173028960249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83116244640811448685973499 124674366961217173028960249)
  ·
    refine ⟨93505775220912879771720187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124674366961217173028960249 93505775220912879771720187)
    ·
      refine ⟨140258662831369319657580281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93505775220912879771720187 140258662831369319657580281)
      ·
        refine ⟨105193997123526989743185211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140258662831369319657580281 105193997123526989743185211)
        ·
          refine ⟨157790995685290484614777817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105193997123526989743185211 157790995685290484614777817)
          ·
            refine ⟨118343246763967863461083363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157790995685290484614777817 118343246763967863461083363)
            ·
              refine ⟨177514870145951795191625045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118343246763967863461083363 177514870145951795191625045)
              ·
                refine ⟨65007887016339768746933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 177514870145951795191625045 65007887016339768746933)
                ·
                  rfl

theorem cell23_3418265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 13].length) (baseStart_3418265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418265 prefixEnd_3418265 := by exact prefixLift 3418265
  have htrace : WordTrace (prefixWord ++ tailWord_3418265) baseStart_3418265 baseEnd_3418265 := by
    simpa [prefixWord, tailWord_3418265, baseEnd_3418265] using wordTrace_append hprefix tailTrace_3418265
  have hstable : (prefixWord ++ tailWord_3418265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418265).length < 2 ^ (prefixWord ++ tailWord_3418265).sum := by decide
  have hdescent : baseEnd_3418265 < baseStart_3418265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3418276 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_3418276 : Nat := 118140960795 + 3418276 * 2 ^ 59
def prefixEnd_3418276 : Nat := 4983230072969 + 3 ^ 40 * 3418276 * 2
def baseEnd_3418276 : Nat := 1755218597728373213129641

theorem tailTrace_3418276 : CollatzResearch.WordTrace tailWord_3418276 prefixEnd_3418276 1755218597728373213129641 := by
  unfold tailWord_3418276
  simp only [CollatzResearch.WordTrace]
  refine ⟨62337384082088660953805341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83116512109451547938407121 62337384082088660953805341)
  ·
    refine ⟨23376519030783247857677003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62337384082088660953805341 23376519030783247857677003)
    ·
      refine ⟨35064778546174871786515505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23376519030783247857677003 35064778546174871786515505)
      ·
        refine ⟨26298583909631153839886629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35064778546174871786515505 26298583909631153839886629)
        ·
          refine ⟨4930984483055841344978743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26298583909631153839886629 4930984483055841344978743)
          ·
            refine ⟨7396476724583762017468115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930984483055841344978743 7396476724583762017468115)
            ·
              refine ⟨11094715086875643026202173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7396476724583762017468115 11094715086875643026202173)
              ·
                refine ⟨4160518157578366134825815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11094715086875643026202173 4160518157578366134825815)
                ·
                  refine ⟨6240777236367549202238723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160518157578366134825815 6240777236367549202238723)
                  ·
                    refine ⟨9361165854551323803358085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6240777236367549202238723 9361165854551323803358085)
                    ·
                      refine ⟨1755218597728373213129641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9361165854551323803358085 1755218597728373213129641)
                      ·
                        rfl

theorem cell23_3418276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_3418276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3418276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3418276 prefixEnd_3418276 := by exact prefixLift 3418276
  have htrace : WordTrace (prefixWord ++ tailWord_3418276) baseStart_3418276 baseEnd_3418276 := by
    simpa [prefixWord, tailWord_3418276, baseEnd_3418276] using wordTrace_append hprefix tailTrace_3418276
  have hstable : (prefixWord ++ tailWord_3418276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3418276).length < 2 ^ (prefixWord ++ tailWord_3418276).sum := by decide
  have hdescent : baseEnd_3418276 < baseStart_3418276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3418276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
